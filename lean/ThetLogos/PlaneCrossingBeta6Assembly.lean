/-
# ThetLogos.PlaneCrossingBeta6Assembly — B6-2a: the order-6
assembly opens: `C₆` / `Θ(2,2,2)` channel sums and the four
channel excesses

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is an OPENING brick (B6-2a) for the order-6
assembly, at general `(G, ρ)` — no irreducibility
anywhere: it owns the support families for B6-0's two
card-6 patterns (`HasSixPatternC6`,
`HasSixPatternTheta`), the two channel sums over them
that B6-1b deferred (`kappa6chanC6`, `kappa6chanTheta`),
and the four channel excesses with their baseline
bookkeeping. Definitions and baseline bookkeeping only.
**No assembly identity is asserted here** (that is
B6-2c, over B6-2b's total decomposition), and **no sign
is asserted for any channel or excess**: the β⁶ general
sign is FRONTIER — its new channels carry quadruple
twirls, on top of the still-unowned (2,1) triple twirl.

**Baselines.** Each excess removes, summand by summand,
the fully-split value of its moment's factor pattern:
`(3,1,1,1) ↦ μ₃e₁³`, `(2,2,1,1) ↦ μ₂²e₁²`, and the
all-ones patterns `C₆` / `Θ(2,2,2) ↦ e₁⁶`. These are the
assembly's candidate baselines, validated or corrected
at B6-2b/c.

**Support families.** No landed module exports a finset
of card-6 `C₆` / `Θ` supports, so both are constructed
here, in exactly the form of `primitiveQuads` in
`PlaneCrossingBeta4`: a filter of the universal finset
by a card condition together with the pattern predicate
exported by B6-0 (`OrderSixSelection`). The predicates
are consumed as exported, not restated.
-/

import Mathlib.Data.Nat.Choose.Multinomial
import ThetLogos.PlaneCrossingBeta6
import ThetLogos.PlaneCrossingBeta5Assembly
import ThetLogos.OrderSixSelection

open MeasureTheory Finset

namespace ThetLogos

section Supports6

variable {N : ℕ} [NeZero N]

open Classical in
/-- The finite set of 6-element supports carrying the
`C₆` pattern of B6-0 (`HasSixPatternC6`), constructed as
`primitiveQuads` is constructed: a filter of the
universal finset by card and pattern. -/
noncomputable def c6Supports : Finset (Finset (LayerColumn N)) :=
  Finset.univ.filter (fun S => S.card = 6 ∧ HasSixPatternC6 S)

open Classical in
/-- The finite set of 6-element supports carrying the
`Θ(2,2,2)` pattern of B6-0 (`HasSixPatternTheta`),
constructed as `primitiveQuads` is constructed. -/
noncomputable def thetaSupports : Finset (Finset (LayerColumn N)) :=
  Finset.univ.filter (fun S => S.card = 6 ∧ HasSixPatternTheta S)

/-- A `C₆` support has six columns. -/
theorem card_eq_six_of_mem_c6Supports {S : Finset (LayerColumn N)}
    (hS : S ∈ c6Supports) : S.card = 6 := by
  classical
  rw [c6Supports, Finset.mem_filter] at hS
  exact hS.2.1

/-- A `Θ(2,2,2)` support has six columns. -/
theorem card_eq_six_of_mem_thetaSupports {S : Finset (LayerColumn N)}
    (hS : S ∈ thetaSupports) : S.card = 6 := by
  classical
  rw [thetaSupports, Finset.mem_filter] at hS
  exact hS.2.1

/-- A `C₆` support carries the `C₆` pattern. -/
theorem hasSixPatternC6_of_mem_c6Supports {S : Finset (LayerColumn N)}
    (hS : S ∈ c6Supports) : HasSixPatternC6 S := by
  classical
  rw [c6Supports, Finset.mem_filter] at hS
  exact hS.2.2

/-- A `Θ(2,2,2)` support carries the `Θ` pattern. -/
theorem hasSixPatternTheta_of_mem_thetaSupports
    {S : Finset (LayerColumn N)} (hS : S ∈ thetaSupports) :
    HasSixPatternTheta S := by
  classical
  rw [thetaSupports, Finset.mem_filter] at hS
  exact hS.2.2

end Supports6

section Assembly6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The `C₆` channel expression**: the sum, over the
card-6 `C₆` supports, of the all-distinct order-6
moments `hexaReMoment`. Raw channel expression only:
no assembly identity and no sign is asserted for this
sum. -/
noncomputable def kappa6chanC6 (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ c6Supports, hexaReMoment ρ μG S u u'

/-- **The `Θ(2,2,2)` channel expression**: the sum, over
the card-6 `Θ` supports, of the all-distinct order-6
moments `hexaReMoment`. Raw channel expression only, on
the same fence as `kappa6chanC6`. -/
noncomputable def kappa6chanTheta (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ thetaSupports, hexaReMoment ρ μG S u u'

/-- **The `(3,1,1,1)` channel excess**: the channel sum
of B6-1b with its fully-split baseline `μ₃e₁³` removed
summand by summand. No sign is asserted for it. -/
noncomputable def kappa6chan3111Excess (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (tripledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)

/-- The `(3,1,1,1)` channel excess is the raw channel sum
minus its baseline: each primitive quad contributes four
tripled columns, each carrying baseline `μ₃e₁³`. -/
theorem kappa6chan3111Excess_eq (u u' : LayerLink N → G) :
    kappa6chan3111Excess ρ μG u u'
      = kappa6chan3111 ρ μG u u'
        - 4 * ((primitiveQuads (N := N)).card : ℝ)
          * realMoment ρ μG 3 * (e1 ρ μG) ^ 3 := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ _P ∈ C, (realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        = 4 * (realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    rw [Finset.sum_const, hC4, nsmul_eq_mul, Nat.cast_ofNat]
  have step1 : kappa6chan3111Excess ρ μG u u'
      = kappa6chan3111 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
            (realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    unfold kappa6chan3111Excess kappa6chan3111
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
        (realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = 4 * ((primitiveQuads (N := N)).card : ℝ)
        * realMoment ρ μG 3 * (e1 ρ μG) ^ 3 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- **The `(2,2,1,1)` channel excess**: the channel sum
of B6-1b with its fully-split baseline `μ₂²e₁²` removed
summand by summand. No sign is asserted for it. -/
noncomputable def kappa6chan2211Excess (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    (doubledDoubledQuadReMoment ρ μG C P Q u u'
      - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)

/-- The `(2,2,1,1)` channel excess is the raw channel sum
minus its baseline: each primitive quad contributes
twelve ordered pairs of distinct doubled columns, each
carrying baseline `μ₂²e₁²`. -/
theorem kappa6chan2211Excess_eq (u u' : LayerLink N → G) :
    kappa6chan2211Excess ρ μG u u'
      = kappa6chan2211 ρ μG u u'
        - 12 * ((primitiveQuads (N := N)).card : ℝ)
          * (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2 := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ P ∈ C, ∑ _Q ∈ C.erase P,
          ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        = 12 * ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    have hinner : ∀ P ∈ C,
        ∑ _Q ∈ C.erase P, ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
          = 3 * ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
      intro P hP
      rw [Finset.sum_const, Finset.card_erase_of_mem hP, hC4,
        nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, hC4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have step1 : kappa6chan2211Excess ρ μG u u'
      = kappa6chan2211 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C, ∑ _Q ∈ C.erase P,
            ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    unfold kappa6chan2211Excess kappa6chan2211
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
        ∑ _Q ∈ C.erase P, ((realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 12 * ((primitiveQuads (N := N)).card : ℝ)
        * (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- **The `C₆` channel excess**: the `C₆` channel sum
with its fully-split baseline `e₁⁶` removed summand by
summand. No sign is asserted for it. -/
noncomputable def kappa6chanC6Excess (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ c6Supports, (hexaReMoment ρ μG S u u' - (e1 ρ μG) ^ 6)

/-- The `C₆` channel excess is the raw channel sum minus
its baseline: each `C₆` support carries baseline `e₁⁶`. -/
theorem kappa6chanC6Excess_eq (u u' : LayerLink N → G) :
    kappa6chanC6Excess ρ μG u u'
      = kappa6chanC6 ρ μG u u'
        - ((c6Supports (N := N)).card : ℝ) * (e1 ρ μG) ^ 6 := by
  classical
  have step1 : kappa6chanC6Excess ρ μG u u'
      = kappa6chanC6 ρ μG u u'
        - ∑ _S ∈ c6Supports (N := N), (e1 ρ μG) ^ 6 := by
    unfold kappa6chanC6Excess kappa6chanC6
    exact Finset.sum_sub_distrib _ _
  have step2 : (∑ _S ∈ c6Supports (N := N), (e1 ρ μG) ^ 6)
      = ((c6Supports (N := N)).card : ℝ) * (e1 ρ μG) ^ 6 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [step1, step2]

/-- **The `Θ(2,2,2)` channel excess**: the `Θ` channel
sum with its fully-split baseline `e₁⁶` removed summand
by summand. No sign is asserted for it. -/
noncomputable def kappa6chanThetaExcess (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ thetaSupports, (hexaReMoment ρ μG S u u' - (e1 ρ μG) ^ 6)

/-- The `Θ` channel excess is the raw channel sum minus
its baseline: each `Θ` support carries baseline `e₁⁶`. -/
theorem kappa6chanThetaExcess_eq (u u' : LayerLink N → G) :
    kappa6chanThetaExcess ρ μG u u'
      = kappa6chanTheta ρ μG u u'
        - ((thetaSupports (N := N)).card : ℝ) * (e1 ρ μG) ^ 6 := by
  classical
  have step1 : kappa6chanThetaExcess ρ μG u u'
      = kappa6chanTheta ρ μG u u'
        - ∑ _S ∈ thetaSupports (N := N), (e1 ρ μG) ^ 6 := by
    unfold kappa6chanThetaExcess kappa6chanTheta
    exact Finset.sum_sub_distrib _ _
  have step2 : (∑ _S ∈ thetaSupports (N := N), (e1 ρ μG) ^ 6)
      = ((thetaSupports (N := N)).card : ℝ) * (e1 ρ μG) ^ 6 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [step1, step2]

end Assembly6

/-! ## B6-2b-i: fiber expansion machinery and constant fibers

Fiber bookkeeping and constant evaluations only, at
order six, mirroring the order-five assembly's route:
the integrated sixth-power expansion is split fiberwise
by `multSupport` (B6-0's support), fibers over supports
of card `0` or `≥ 7` are empty, and the fibers over
supports of card `1`, `2`, `3` evaluate to the constant
pattern values of `kappa6Const` named in B6-2b's
scoping: card `1`: pattern `(6)`; card `2`: splits
`(5,1)`, `(4,2)`, `(3,3)` (with their reversals);
card `3`: `(4,1,1)`, `(3,2,1)`, `(2,2,2)`. **No total
assembly is asserted here, no `kappa6dep` identity, and
no sign is asserted anywhere.** NO CLAIM; dials 0/4. -/

section Fiber6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The sixth-power expansion, integrated.** The
multinomial expansion of `(layerDensSum)^6`, integrated
termwise: each exponent function `k` contributes its
multinomial coefficient times the integral of the
column-density monomial `∏ P, colDensC(P)^(k P)`.
Integrability of each monomial is by the uniform bound
`|colDensC| ≤ 2` (total mass `2^6 = 64`). -/
theorem integral_layerDensSum_pow_six (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 6
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ k ∈ Finset.piAntidiag Finset.univ 6,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG) := by
  classical
  have hmeas : ∀ P : LayerColumn N,
      Measurable fun α : LayerSite N → G =>
        colDensC ρ u u' P α :=
    fun P => measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2
  have hInt : ∀ k ∈ Finset.piAntidiag Finset.univ 6,
      Integrable (fun α : LayerSite N → G =>
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro k hk
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound
      (Finset.measurable_prod Finset.univ fun P _ =>
        (hmeas P).pow_const (k P)).aestronglyMeasurable
      (64 : ℝ) (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    have hsum6 : ∑ P ∈ Finset.univ, k P = 6 :=
      (Finset.mem_piAntidiag.mp hk).1
    have hle : ∏ P ∈ Finset.univ, |(colDensC ρ u u' P α) ^ (k P)|
        ≤ ∏ P ∈ Finset.univ, (2 : ℝ) ^ (k P) :=
      Finset.prod_le_prod₀ (fun P _ => abs_nonneg _)
        (fun P _ => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_colDensC_le ρ u u' P α) _)
    refine le_trans hle ?_
    rw [Finset.prod_pow_eq_pow_sum, hsum6]
    norm_num
  have hpt : ∀ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 6
      = ∑ k ∈ Finset.piAntidiag Finset.univ 6,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P) := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u']
    exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ
      (fun P => colDensC ρ u u' P α) 6
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ hInt,
    Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)]

/-- Summation over all columns collapses to the
multiplicity support: off-support exponents are zero.
The support is B6-0's `multSupport`. -/
theorem sum_univ_eq_sum_multSupport (k : LayerColumn N → ℕ) :
    ∑ P ∈ Finset.univ, k P = ∑ P ∈ multSupport k, k P := by
  unfold multSupport
  exact (Finset.sum_subset (Finset.filter_subset _ _)
    (fun P _ hP => not_not.mp (fun hne =>
      hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩)))).symm

/-- The monomial integral collapses to the multiplicity
support: off-support factors are `x^0 = 1`. -/
theorem integral_colDens_prod_pow_univ_six
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (k : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ∏ P ∈ multSupport k, (colDensC ρ u u' P α) ^ (k P)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hsub : multSupport k = Finset.univ.filter
      (fun P => k P ≠ 0) := rfl
  rw [hsub]
  exact integral_congr_ae (Filter.Eventually.of_forall fun α =>
    (Finset.prod_subset (Finset.filter_subset _ _)
      (fun P _ hP => by
        rw [not_not.mp (fun hne =>
          hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩))]
        exact pow_zero _)).symm)

/-- **Fiberwise split by support.** The integrated
expansion, regrouped by the multiplicity support of the
exponent function. -/
theorem sum_piAntidiag6_fiberwise (F : (LayerColumn N → ℕ) → ℝ) :
    ∑ k ∈ Finset.piAntidiag Finset.univ 6, F k
      = ∑ C ∈ Finset.univ.powerset,
          ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
              (fun k => multSupport k = C), F k := by
  have hsub : ∀ k : LayerColumn N → ℕ,
      multSupport k = Finset.univ.filter (fun P => k P ≠ 0) :=
    fun k => rfl
  exact (Finset.sum_fiberwise_of_maps_to (fun k _ => by
    rw [hsub k]
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)) F).symm

/-- **Fibers over supports of card `0` or `≥ 7` are
empty**: on its support every exponent is at least
`1`, so the support's card is at most the total
exponent sum `6` (B6-0's `card_multSupport_le_six` is
the same bound), and a card-`0` support carries sum
`0 ≠ 6`. -/
theorem fiber6_eq_empty_of_card_ne (C : Finset (LayerColumn N))
    (hC : C.card = 0 ∨ 7 ≤ C.card) :
    (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun k hk => ?_
  have hk6 : ∑ P ∈ Finset.univ, k P = 6 :=
    (Finset.mem_piAntidiag.mp
      (Finset.mem_filter.mp hk).1).1
  have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
  have hsumC : ∑ P ∈ C, k P = 6 := by
    rw [← hsupp, ← sum_univ_eq_sum_multSupport]
    exact hk6
  have hle : C.card ≤ ∑ P ∈ C, k P := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPC : P ∈ multSupport k := hsupp ▸ hP
    have hPC' := hPC
    rw [show multSupport k = Finset.univ.filter
      (fun Q => k Q ≠ 0) from rfl] at hPC'
    have : k P ≠ 0 :=
      (Finset.mem_filter.mp hPC').2
    exact Nat.one_le_iff_ne_zero.mpr this
  rw [hsumC] at hle
  rcases hC with h0 | h7
  · have : C = ∅ := Finset.card_eq_zero.mp h0
    rw [this, Finset.sum_empty] at hsumC
    exact absurd hsumC (by norm_num)
  · omega

/-- **Multinomial from the factorial product.** If
the factorials of the exponents of `k` multiply to
`p ≠ 0`, the multinomial coefficient is `720 / p`,
by `Nat.multinomial_spec` at total exponent `6`. -/
theorem multinomial6_univ_eq (k : LayerColumn N → ℕ)
    (hk6 : ∑ P ∈ Finset.univ, k P = 6) (p : ℕ)
    (hp : ∏ P ∈ Finset.univ, Nat.factorial (k P) = p)
    (hp0 : p ≠ 0) :
    (Nat.multinomial Finset.univ k : ℝ) = 720 / (p : ℝ) := by
  have h := Nat.multinomial_spec Finset.univ k
  rw [hp, hk6] at h
  have h720 : Nat.factorial 6 = 720 := by
    norm_num [Nat.factorial]
  rw [h720] at h
  have h' : (p : ℝ) * (Nat.multinomial Finset.univ k : ℝ)
      = 720 := by exact_mod_cast h
  rw [eq_div_iff (by exact_mod_cast hp0 : (p : ℝ) ≠ 0), mul_comm]
  exact h'

/-- **The card-1 fiber.** Over a 1-support `C`, the
fiber of the expansion is the single exponent `(6)`
on that column, its multinomial coefficient is `1`,
and its value is the pattern value `A₆` of
`kappa6Const`'s `(6)` pattern. -/
theorem fiber_card_one6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 1) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 6 := by
  classical
  obtain ⟨P, hPeq⟩ := Finset.card_eq_one.mp hC
  have hfib : (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C)
      = {fun Q => if Q = P then 6 else 0} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ?_
    constructor
    · refine ⟨fun Q => if Q = P then 6 else 0, ?_⟩
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun Q _ => Finset.mem_univ Q⟩, ?_⟩
      · rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 6)]
        simp
      · refine Finset.ext fun Q => ?_
        simp only [show multSupport (fun Q => if Q = P then 6 else 0)
            = Finset.univ.filter
              (fun Q => (if Q = P then 6 else 0) ≠ 0) from rfl,
          Finset.mem_filter, Finset.mem_univ,
          true_and, hPeq, Finset.mem_singleton]
        by_cases hQ : Q = P <;> simp [hQ]
    · intro k hk
      have hk6 : ∑ Q ∈ Finset.univ, k Q = 6 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hkP : k P = 6 := by
        have h1 : ∑ Q ∈ multSupport k, k Q = 6 := by
          rw [← sum_univ_eq_sum_multSupport]
          exact hk6
        rw [hsupp, hPeq, Finset.sum_singleton] at h1
        exact h1
      funext Q
      by_cases hQ : Q = P
      · rw [hQ, hkP]
        simp
      · have hk0 : k Q = 0 := by
          by_contra hne
          have hQs : Q ∈ multSupport k :=
            (show multSupport k = Finset.univ.filter
              (fun Q => k Q ≠ 0) from rfl) ▸
              Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hne⟩
          rw [hsupp, hPeq, Finset.mem_singleton] at hQs
          exact hQ hQs
        rw [hk0]
        simp [hQ]
  rw [hfib, Finset.sum_singleton]
  have hmult : (Nat.multinomial Finset.univ
        (fun Q => if Q = P then 6 else 0) : ℝ) = 1 := by
    have hp : ∏ Q ∈ Finset.univ,
        Nat.factorial ((fun Q => if Q = P then 6 else 0) Q)
          = 720 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial ((fun Q => if Q = P then 6 else 0) Q)
          = ∏ Q ∈ C,
            Nat.factorial ((fun Q => if Q = P then 6 else 0) Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := by
              rw [hPeq, Finset.mem_singleton] at hQ
              exact hQ
            simp [hQP])).symm
      rw [h1, hPeq, Finset.prod_singleton]
      simp
      norm_num [Nat.factorial]
    have hk6 : ∑ Q ∈ Finset.univ,
        (fun Q => if Q = P then 6 else 0) Q = 6 := by
      rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 6)]
      simp
    have h := multinomial6_univ_eq
      (fun Q => if Q = P then 6 else 0) hk6 720 hp
      (by norm_num)
    rw [h]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ Q ∈ Finset.univ,
          (colDensC ρ u u' Q α)
            ^ ((fun Q => if Q = P then 6 else 0) Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 6 := by
    have hsupp : multSupport (fun Q => if Q = P then 6 else 0)
        = C := by
      refine Finset.ext fun Q => ?_
      simp only [show multSupport (fun Q => if Q = P then 6 else 0)
          = Finset.univ.filter
            (fun Q => (if Q = P then 6 else 0) ≠ 0) from rfl,
        Finset.mem_filter, Finset.mem_univ,
        true_and, hPeq, Finset.mem_singleton]
      by_cases hQ : Q = P <;> simp [hQ]
    rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u'
      (fun Q => if Q = P then 6 else 0), hsupp, hPeq]
    have hpt : ∀ α : LayerSite N → G,
        ∏ Q ∈ ({P} : Finset (LayerColumn N)),
          (colDensC ρ u u' Q α)
            ^ ((fun Q => if Q = P then 6 else 0) Q)
        = (colDensC ρ u u' P α) ^ 6 := by
      intro α
      rw [Finset.prod_singleton]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact densMomentValue_eq ρ μG hN hρcont u u' P 6
  rw [hmult, hval, one_mul]

/-- The multiplicity support unfolds to its defining
filter (B6-0's `multSupport`); used as a simp normal
form in the fiber arguments below. -/
theorem multSupport_eq_filter (k : LayerColumn N → ℕ) :
    multSupport k = Finset.univ.filter (fun P => k P ≠ 0) :=
  rfl

/-- **Character power-moments factor on small supports.**
For `T` of card at most 3 and arbitrary exponents, the
integral of `∏ r_P^{aP}` is the product of the Haar
moments: at card 3 one of the three columns owns a
private site (`exists_private_site_triple`) and the
strip engine separates it; the rest is the two-column
factorization and the single-column Haar moment. -/
theorem integral_colRe_prod_pow_card_le_three6 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (T : Finset (LayerColumn N))
    (hT : T.card ≤ 3) (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, ∏ P ∈ T, (colRe ρ u u' P α) ^ (a P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∏ P ∈ T, realMoment ρ μG (a P) := by
  classical
  interval_cases hcard : T.card
  · have hT0 : T = ∅ := Finset.card_eq_zero.mp hcard
    simp only [hT0, Finset.prod_empty]
    rw [integral_const, probReal_univ, one_smul]
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
    rw [hP]
    simp only [Finset.prod_singleton]
    exact colMoment_eq ρ μG hN hρcont u u' P (a P)
  · obtain ⟨P, Q, hPQ, hT2⟩ := Finset.card_eq_two.mp hcard
    have hprod : ∀ α : LayerSite N → G,
        ∏ Z ∈ T, (colRe ρ u u' Z α) ^ (a Z)
        = (colRe ρ u u' P α) ^ (a P) * (colRe ρ u u' Q α) ^ (a Q) := by
      intro α
      rw [hT2]
      exact Finset.prod_pair hPQ
    have hRHS : ∏ Z ∈ T, realMoment ρ μG (a Z)
        = realMoment ρ μG (a P) * realMoment ρ μG (a Q) := by
      rw [hT2, Finset.prod_pair hPQ]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod), hRHS]
    exact integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPQ (a P) (a Q)
  · obtain ⟨P, Q, R, hPQ, hPR, hQR, hT3⟩ :=
      Finset.card_eq_three.mp hcard
    obtain (⟨s, hsP, hsQ, hsR⟩ | ⟨s, hsQ, hsP, hsR⟩
      | ⟨s, hsR, hsP, hsQ⟩) :=
      exists_private_site_triple hN hN3 hPQ hPR hQR
    · -- P owns a private site: strip P from `{Q, R}`.
      have hnotP : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hPQ, hPR⟩
      have heng := integral_colRe_pow_split_finset ρ μG hN hN3
        hρcont u u' {Q, R} a P hnotP s hsP
        (fun Y hY => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hY
          rcases hY with rfl | rfl
          · exact hsQ
          · exact hsR) (a P)
      have hprod : ∀ α : LayerSite N → G,
          ∏ Z ∈ T, (colRe ρ u u' Z α) ^ (a Z)
          = (∏ Z ∈ ({Q, R} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z))
            * (colRe ρ u u' P α) ^ (a P) := by
        intro α
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
        ring
      have hval : ∫ α : LayerSite N → G,
            ∏ Z ∈ ({Q, R} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = realMoment ρ μG (a Q) * realMoment ρ μG (a R) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
          Finset.prod_pair hQR)]
        exact integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hQR
          (a Q) (a R)
      have hRHS : ∏ Z ∈ T, realMoment ρ μG (a Z)
          = realMoment ρ μG (a P)
            * (realMoment ρ μG (a Q) * realMoment ρ μG (a R)) := by
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod), heng,
        hval, hRHS]
    · -- Q owns a private site: strip Q from `{P, R}`.
      have hnotQ : Q ∉ ({P, R} : Finset (LayerColumn N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hPQ h.symm, hQR⟩
      have heng := integral_colRe_pow_split_finset ρ μG hN hN3
        hρcont u u' {P, R} a Q hnotQ s hsQ
        (fun Y hY => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hY
          rcases hY with rfl | rfl
          · exact hsP
          · exact hsR) (a Q)
      have hprod : ∀ α : LayerSite N → G,
          ∏ Z ∈ T, (colRe ρ u u' Z α) ^ (a Z)
          = (∏ Z ∈ ({P, R} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z))
            * (colRe ρ u u' Q α) ^ (a Q) := by
        intro α
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_insert (by
          simp only [Finset.mem_singleton]
          exact hQR), Finset.prod_singleton, Finset.prod_insert (by
          simp only [Finset.mem_singleton]
          exact hPR), Finset.prod_singleton]
        ring
      have hval : ∫ α : LayerSite N → G,
            ∏ Z ∈ ({P, R} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = realMoment ρ μG (a P) * realMoment ρ μG (a R) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
          Finset.prod_pair hPR)]
        exact integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPR
          (a P) (a R)
      have hRHS : ∏ Z ∈ T, realMoment ρ μG (a Z)
          = realMoment ρ μG (a Q)
            * (realMoment ρ μG (a P) * realMoment ρ μG (a R)) := by
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod), heng,
        hval, hRHS]
    · -- R owns a private site: strip R from `{P, Q}`.
      have hnotR : R ∉ ({P, Q} : Finset (LayerColumn N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hPR h.symm, fun h => hQR h.symm⟩
      have heng := integral_colRe_pow_split_finset ρ μG hN hN3
        hρcont u u' {P, Q} a R hnotR s hsR
        (fun Y hY => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hY
          rcases hY with rfl | rfl
          · exact hsP
          · exact hsQ) (a R)
      have hprod : ∀ α : LayerSite N → G,
          ∏ Z ∈ T, (colRe ρ u u' Z α) ^ (a Z)
          = (∏ Z ∈ ({P, Q} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z))
            * (colRe ρ u u' R α) ^ (a R) := by
        intro α
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_insert (by
          simp only [Finset.mem_singleton]
          exact hQR), Finset.prod_singleton, Finset.prod_pair hPQ]
        ring
      have hval : ∫ α : LayerSite N → G,
            ∏ Z ∈ ({P, Q} : Finset (LayerColumn N)),
              (colRe ρ u u' Z α) ^ (a Z)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = realMoment ρ μG (a P) * realMoment ρ μG (a Q) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
          Finset.prod_pair hPQ)]
        exact integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPQ
          (a P) (a Q)
      have hRHS : ∏ Z ∈ T, realMoment ρ μG (a Z)
          = realMoment ρ μG (a R)
            * (realMoment ρ μG (a P) * realMoment ρ μG (a Q)) := by
        rw [hT3, Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod), heng,
        hval, hRHS]


/-- **Density moments of a triple of distinct columns
factor.** Pointwise binomial expansion of each density
power into character powers; the character triple
factors by the small-support factorization; the pieces
re-sum into the three `densMomentValue`s. -/
theorem integral_colDens_triple_pow6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ (a P)
          * (colDensC ρ u u' Q α) ^ (a Q)
          * (colDensC ρ u u' R α) ^ (a R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG (a P) * densMomentValue ρ μG (a Q)
        * densMomentValue ρ μG (a R) := by
  classical
  have hexp : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      (colDensC ρ u u' Z α) ^ (a Z)
        = ∑ b ∈ Finset.range (a Z + 1),
            (((a Z).choose b : ℝ) * (-(d : ℝ)⁻¹) ^ b)
              * (colRe ρ u u' Z α) ^ b := by
    intro Z α
    rw [colDensC_eq_one_add, add_comm (1 : ℝ)
      ((-(d : ℝ)⁻¹) * colRe ρ u u' Z α), add_pow]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_pow, one_pow, mul_one]
    ring
  have hnotP : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hPQ, hPR⟩
  have hnotQ : Q ∉ ({R} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_singleton]
    exact hQR
  have hcard3 : ({P, Q, R} : Finset (LayerColumn N)).card ≤ 3 :=
    le_of_eq (Finset.card_eq_three.mpr ⟨P, Q, R, hPQ, hPR, hQR, rfl⟩)
  have hfun : ∀ (bP bQ bR : ℕ) (α : LayerSite N → G),
      ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
          * (colRe ρ u u' P α) ^ bP)
        * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
          * (colRe ρ u u' Q α) ^ bQ)
        * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
          * (colRe ρ u u' R α) ^ bR)
      = ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
          * (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
          * (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR))
        * ∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
          (colRe ρ u u' Z α) ^ (if Z = R then bR
            else if Z = Q then bQ else bP) := by
    intro bP bQ bR α
    rw [Finset.prod_insert hnotP, Finset.prod_insert hnotQ,
      Finset.prod_singleton, if_neg hPR, if_neg hPQ, if_neg hQR,
      if_pos rfl, if_pos rfl]
    ring
  have hInt : ∀ bP ∈ Finset.range (a P + 1),
      ∀ bQ ∈ Finset.range (a Q + 1), ∀ bR ∈ Finset.range (a R + 1),
      Integrable (fun α : LayerSite N → G =>
        ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
            * (colRe ρ u u' P α) ^ bP)
          * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
            * (colRe ρ u u' Q α) ^ bQ)
          * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
            * (colRe ρ u u' R α) ^ bR))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro bP _ bQ _ bR _
    have hfun' : (fun α : LayerSite N → G =>
        ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
            * (colRe ρ u u' P α) ^ bP)
          * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
            * (colRe ρ u u' Q α) ^ bQ)
          * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
            * (colRe ρ u u' R α) ^ bR))
      = fun α => ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
            * (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
            * (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR))
          * ∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
            (colRe ρ u u' Z α) ^ (if Z = R then bR
              else if Z = Q then bQ else bP) := by
      funext α
      exact hfun bP bQ bR α
    rw [hfun']
    exact Integrable.const_mul (integrable_colRe_prod_pow ρ μG
      hρcont u u' {P, Q, R} _) _
  have hterm : ∀ bP ∈ Finset.range (a P + 1),
      ∀ bQ ∈ Finset.range (a Q + 1), ∀ bR ∈ Finset.range (a R + 1),
      ∫ α : LayerSite N → G,
          ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
              * (colRe ρ u u' P α) ^ bP)
            * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
              * (colRe ρ u u' Q α) ^ bQ)
            * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
              * (colRe ρ u u' R α) ^ bR)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP
              * realMoment ρ μG bP)
            * (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ
              * realMoment ρ μG bQ)
            * (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR
              * realMoment ρ μG bR) := by
    intro bP _ bQ _ bR _
    rw [integral_congr_ae (Filter.Eventually.of_forall
        fun α => hfun bP bQ bR α), integral_const_mul,
      integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3 hρcont
        u u' {P, Q, R} hcard3 _,
      Finset.prod_insert hnotP, Finset.prod_pair hQR, if_neg hPR,
      if_neg hPQ, if_neg hQR, if_pos rfl, if_pos rfl]
    ring
  have hswap : ∀ x y z : ℝ, (x * y) * z = (x * z) * y := by
    intro x y z
    ring
  have hpt1 : ∀ α : LayerSite N → G,
      (colDensC ρ u u' P α) ^ (a P) * (colDensC ρ u u' Q α) ^ (a Q)
          * (colDensC ρ u u' R α) ^ (a R)
        = (∑ bP ∈ Finset.range (a P + 1),
            (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
              * (colRe ρ u u' P α) ^ bP)
          * (∑ bQ ∈ Finset.range (a Q + 1),
            (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
              * (colRe ρ u u' Q α) ^ bQ)
          * (∑ bR ∈ Finset.range (a R + 1),
            (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
              * (colRe ρ u u' R α) ^ bR) := by
    intro α
    rw [hexp P α, hexp Q α, hexp R α]
  have hpt2 : ∀ α : LayerSite N → G,
      (∑ bP ∈ Finset.range (a P + 1),
          (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
            * (colRe ρ u u' P α) ^ bP)
        * (∑ bQ ∈ Finset.range (a Q + 1),
          (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
            * (colRe ρ u u' Q α) ^ bQ)
        * (∑ bR ∈ Finset.range (a R + 1),
          (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
            * (colRe ρ u u' R α) ^ bR)
      = ∑ bP ∈ Finset.range (a P + 1),
        ∑ bR ∈ Finset.range (a R + 1),
        ∑ bQ ∈ Finset.range (a Q + 1),
          ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
              * (colRe ρ u u' P α) ^ bP)
            * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
              * (colRe ρ u u' Q α) ^ bQ)
            * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
              * (colRe ρ u u' R α) ^ bR) := by
    intro α
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun bP _ => ?_
    refine Finset.sum_congr rfl fun bR _ => ?_
    rw [Finset.sum_mul]
  calc ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ (a P)
          * (colDensC ρ u u' Q α) ^ (a Q)
          * (colDensC ρ u u' R α) ^ (a R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          (∑ bP ∈ Finset.range (a P + 1),
            (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
              * (colRe ρ u u' P α) ^ bP)
          * (∑ bQ ∈ Finset.range (a Q + 1),
            (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
              * (colRe ρ u u' Q α) ^ bQ)
          * (∑ bR ∈ Finset.range (a R + 1),
            (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
              * (colRe ρ u u' R α) ^ bR)
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt1)
    _ = ∫ α : LayerSite N → G,
          ∑ bP ∈ Finset.range (a P + 1),
          ∑ bR ∈ Finset.range (a R + 1),
          ∑ bQ ∈ Finset.range (a Q + 1),
            ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP)
                * (colRe ρ u u' P α) ^ bP)
              * ((((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ)
                * (colRe ρ u u' Q α) ^ bQ)
              * ((((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR)
                * (colRe ρ u u' R α) ^ bR)
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt2)
    _ = ∑ bP ∈ Finset.range (a P + 1),
          ∑ bR ∈ Finset.range (a R + 1),
          ∑ bQ ∈ Finset.range (a Q + 1),
            (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP
                * realMoment ρ μG bP)
              * (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ
                * realMoment ρ μG bQ)
              * (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR
                * realMoment ρ μG bR) := by
        rw [integral_finsetSum _ (fun bP hbP =>
          integrable_finsetSum _ fun bR hbR =>
            integrable_finsetSum _ fun bQ hbQ =>
              hInt bP hbP bQ hbQ bR hbR)]
        refine Finset.sum_congr rfl fun bP hbP => ?_
        rw [integral_finsetSum _ (fun bR hbR =>
          integrable_finsetSum _ fun bQ hbQ =>
            hInt bP hbP bQ hbQ bR hbR)]
        refine Finset.sum_congr rfl fun bR hbR => ?_
        rw [integral_finsetSum _ (fun bQ hbQ =>
          hInt bP hbP bQ hbQ bR hbR)]
        exact Finset.sum_congr rfl fun bQ hbQ =>
          hterm bP hbP bQ hbQ bR hbR
    _ = ∑ bP ∈ Finset.range (a P + 1),
          ∑ bR ∈ Finset.range (a R + 1),
          ((((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP
              * realMoment ρ μG bP)
            * (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR
              * realMoment ρ μG bR))
          * (∑ bQ ∈ Finset.range (a Q + 1),
            (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ
              * realMoment ρ μG bQ)) := by
        refine Finset.sum_congr rfl fun bP _ => ?_
        refine Finset.sum_congr rfl fun bR _ => ?_
        rw [Finset.sum_congr rfl (fun bQ _ => hswap _ _ _),
          ← Finset.mul_sum]
    _ = ∑ bP ∈ Finset.range (a P + 1),
          (((a P).choose bP : ℝ) * (-(d : ℝ)⁻¹) ^ bP
              * realMoment ρ μG bP)
          * ((∑ bR ∈ Finset.range (a R + 1),
            (((a R).choose bR : ℝ) * (-(d : ℝ)⁻¹) ^ bR
              * realMoment ρ μG bR))
          * (∑ bQ ∈ Finset.range (a Q + 1),
            (((a Q).choose bQ : ℝ) * (-(d : ℝ)⁻¹) ^ bQ
              * realMoment ρ μG bQ))) := by
        refine Finset.sum_congr rfl fun bP _ => ?_
        rw [Finset.sum_congr rfl (fun bR _ => mul_assoc _ _ _),
          ← Finset.mul_sum, ← Finset.sum_mul]
    _ = densMomentValue ρ μG (a P) * densMomentValue ρ μG (a Q)
          * densMomentValue ρ μG (a R) := by
        rw [← Finset.sum_mul]
        show densMomentValue ρ μG (a P)
            * (densMomentValue ρ μG (a R)
              * densMomentValue ρ μG (a Q))
          = densMomentValue ρ μG (a P) * densMomentValue ρ μG (a Q)
            * densMomentValue ρ μG (a R)
        ring

/-- **Density power-moments factor on small supports**,
by the card of the support: the owned single and pair
density moments, and the triple factorization. -/
theorem integral_colDens_prod_pow_card_le_three6 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (T : Finset (LayerColumn N))
    (hT : T.card ≤ 3) (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, ∏ P ∈ T, (colDensC ρ u u' P α) ^ (a P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∏ P ∈ T, densMomentValue ρ μG (a P) := by
  classical
  interval_cases hcard : T.card
  · have hT0 : T = ∅ := Finset.card_eq_zero.mp hcard
    simp only [hT0, Finset.prod_empty]
    rw [integral_const, probReal_univ, one_smul]
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
    rw [hP]
    simp only [Finset.prod_singleton]
    exact densMomentValue_eq ρ μG hN hρcont u u' P (a P)
  · obtain ⟨P, Q, hPQ, hT2⟩ := Finset.card_eq_two.mp hcard
    have hprod : ∀ α : LayerSite N → G,
        ∏ Z ∈ T, (colDensC ρ u u' Z α) ^ (a Z)
        = (colDensC ρ u u' P α) ^ (a P)
          * (colDensC ρ u u' Q α) ^ (a Q) := by
      intro α
      rw [hT2]
      exact Finset.prod_pair hPQ
    have hRHS : ∏ Z ∈ T, densMomentValue ρ μG (a Z)
        = densMomentValue ρ μG (a P)
          * densMomentValue ρ μG (a Q) := by
      rw [hT2, Finset.prod_pair hPQ]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod), hRHS]
    exact integral_colDens_pow_mul_value ρ μG hN hN3 hρcont u u'
      hPQ (a P) (a Q)
  · obtain ⟨P, Q, R, hPQ, hPR, hQR, hT3⟩ :=
      Finset.card_eq_three.mp hcard
    have hprod : ∀ α : LayerSite N → G,
        ∏ Z ∈ T, (colDensC ρ u u' Z α) ^ (a Z)
        = (colDensC ρ u u' P α) ^ (a P)
          * (colDensC ρ u u' Q α) ^ (a Q)
          * (colDensC ρ u u' R α) ^ (a R) := by
      intro α
      rw [hT3, Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
      ring
    have hRHS : ∏ Z ∈ T, densMomentValue ρ μG (a Z)
        = densMomentValue ρ μG (a P) * densMomentValue ρ μG (a Q)
          * densMomentValue ρ μG (a R) := by
      rw [hT3, Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod), hRHS]
    exact integral_colDens_triple_pow6 ρ μG hN hN3 hρcont u u' hPQ hPR
      hQR a

/-- **The card-2 fiber.** Over a 2-support `{P, Q}`,
the fiber is the five exponent splits `(a, 6−a)`,
`a = 1..5` (parametrized by the ordered pair
`(k P, k Q)`); the fiber sum evaluates to
`6·A₁A₅ + 15·A₂A₄ + 20·A₃A₃ + 15·A₄A₂ + 6·A₅A₁`:
the `(5,1)`, `(4,2)`, `(3,3)` patterns of
`kappa6Const` with their reversals. -/
theorem fiber_card_two6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 2) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 6 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 5)
        + 15 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 4)
        + 20 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 3)
        + 15 * (densMomentValue ρ μG 4 * densMomentValue ρ μG 2)
        + 6 * (densMomentValue ρ μG 5 * densMomentValue ρ μG 1) := by
  classical
  obtain ⟨P, Q, hPQ, hCeq⟩ := Finset.card_eq_two.mp hC
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 5 ×ˢ Finset.Icc 1 5).filter
      (fun t => t.1 + t.2 = 6) with hS
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (720
            / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ) : ℝ))
          * (densMomentValue ρ μG t.1
            * densMomentValue ρ μG t.2) := by
    refine (Finset.sum_bij
      (fun t _ => fun X => if X = P then t.1
        else if X = Q then t.2 else 0) ?_ ?_ ?_ ?_).symm
    · intro t ht
      have htS : t.1 + t.2 = 6
          ∧ t.1 ∈ Finset.Icc 1 5 ∧ t.2 ∈ Finset.Icc 1 5 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2⟩
      have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
      have ht2 : 1 ≤ t.2 := (Finset.mem_Icc.mp htS.2.2).1
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun X _ => Finset.mem_univ X⟩, ?_⟩
      · have h1 : ∀ X ∈ Finset.univ,
            (if X = P then t.1 else if X = Q then t.2 else 0)
              = if X ∈ C then
                  (if X = P then t.1 else if X = Q then t.2 else 0)
                else 0 :=
          fun X _ => by
            by_cases hX : X ∈ C
            · rw [if_pos hX]
            · have hX0 : X ∉ C := hX
              rw [hCeq, Finset.mem_insert, Finset.mem_singleton]
                at hX
              push_neg at hX
              rw [if_neg hX0, if_neg hX.1, if_neg hX.2]
        rw [Finset.sum_congr rfl h1,
          ← Finset.sum_subset (Finset.subset_univ C)
            (fun X _ hX => if_neg hX)]
        rw [hCeq, Finset.sum_insert (by
          rw [Finset.mem_singleton]
          exact hPQ), Finset.sum_singleton]
        rw [if_pos (Finset.mem_insert_self P {Q}),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton_self Q))),
          if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl]
        exact htS.1
      · refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter, Finset.mem_filter, Finset.mem_univ,
          true_and, hCeq, Finset.mem_insert, Finset.mem_singleton]
        by_cases hXP : X = P
        · rw [hXP]
          simp [show t.1 ≠ 0 by omega]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            simp [hXP, Ne.symm hPQ, show t.2 ≠ 0 by omega]
          · simp [hXP, hXQ]
    · intro t ht t' ht' h
      have h1 : t.1 = t'.1 := by
        have hP := congrFun h P
        rw [if_pos rfl, if_pos rfl] at hP
        exact hP
      have h2 : t.2 = t'.2 := by
        have hQ := congrFun h Q
        rw [if_neg (Ne.symm hPQ), if_neg (Ne.symm hPQ),
          if_pos rfl, if_pos rfl] at hQ
        exact hQ
      exact Prod.ext h1 h2
    · intro k hk
      have hk6 : ∑ X ∈ Finset.univ, k X = 6 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 6 := by
        rw [← hsupp, ← sum_univ_eq_sum_multSupport]
        exact hk6
      have hge : ∀ X ∈ C, 1 ≤ k X := by
        intro X hX
        have hXs : X ∈ multSupport k := hsupp ▸ hX
        exact Nat.one_le_iff_ne_zero.mpr
          (Finset.mem_filter.mp hXs).2
      rw [hCeq, Finset.sum_insert (by
        rw [Finset.mem_singleton]
        exact hPQ), Finset.sum_singleton] at hsumC
      have hkP1 : 1 ≤ k P := hge P (by
        rw [hCeq, Finset.mem_insert]
        exact Or.inl rfl)
      have hkQ1 : 1 ≤ k Q := hge Q (by
        rw [hCeq, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr rfl)
      refine ⟨(k P, k Q), ?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc, Finset.mem_Icc]
        refine ⟨⟨⟨hkP1, by omega⟩, ⟨hkQ1, by omega⟩⟩, hsumC⟩
      · funext X
        by_cases hXP : X = P
        · rw [hXP]
          simp
        · by_cases hXQ : X = Q
          · rw [hXQ]
            have hQP : Q ≠ P := by
              rintro rfl
              exact hXP hXQ
            rw [if_neg hQP, if_pos rfl]
          · have hk0 : k X = 0 := by
              by_contra hne
              have hXs : X ∈ multSupport k := Finset.mem_filter.mpr
                ⟨Finset.mem_univ X, hne⟩
              rw [hsupp, hCeq, Finset.mem_insert,
                Finset.mem_singleton] at hXs
              exact hXs.elim (fun h => hXP h) (fun h => hXQ h)
            rw [hk0]
            simp [hXP, hXQ]
    · intro t ht
      have htS : t.1 + t.2 = 6
          ∧ t.1 ∈ Finset.Icc 1 5 ∧ t.2 ∈ Finset.Icc 1 5 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2⟩
      have hsum : ∑ X ∈ Finset.univ,
          (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) X = 6 := by
        have h1 : ∀ X ∈ Finset.univ,
            (if X = P then t.1 else if X = Q then t.2 else 0)
              = if X ∈ C then
                  (if X = P then t.1 else if X = Q then t.2 else 0)
                else 0 :=
          fun X _ => by
            by_cases hX : X ∈ C
            · rw [if_pos hX]
            · have hX0 : X ∉ C := hX
              rw [hCeq, Finset.mem_insert, Finset.mem_singleton]
                at hX
              push_neg at hX
              rw [if_neg hX0, if_neg hX.1, if_neg hX.2]
        rw [Finset.sum_congr rfl h1,
          ← Finset.sum_subset (Finset.subset_univ C)
            (fun X _ hX => if_neg hX),
          hCeq, Finset.sum_insert (by
            rw [Finset.mem_singleton]
            exact hPQ), Finset.sum_singleton]
        rw [if_pos (Finset.mem_insert_self P {Q}),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton_self Q))),
          if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl]
        exact htS.1
      have hfact : ∏ X ∈ Finset.univ,
          Nat.factorial ((fun X => if X = P then t.1
            else if X = Q then t.2 else 0) X)
            = Nat.factorial t.1 * Nat.factorial t.2 := by
        have h1 : ∏ X ∈ Finset.univ,
              Nat.factorial ((fun X => if X = P then t.1
                else if X = Q then t.2 else 0) X)
            = ∏ X ∈ C,
              Nat.factorial ((fun X => if X = P then t.1
                else if X = Q then t.2 else 0) X) :=
          (Finset.prod_subset (Finset.subset_univ C)
            (fun X _ hX => by
              rw [hCeq, Finset.mem_insert, Finset.mem_singleton]
                at hX
              push_neg at hX
              simp [hX.1, hX.2])).symm
        rw [h1, hCeq, Finset.prod_insert (by
          rw [Finset.mem_singleton]
          exact hPQ), Finset.prod_singleton]
        show Nat.factorial (if P = P then t.1
              else if P = Q then t.2 else 0)
            * Nat.factorial (if Q = P then t.1
              else if Q = Q then t.2 else 0)
          = Nat.factorial t.1 * Nat.factorial t.2
        rw [if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl]
      have hmult : (Nat.multinomial Finset.univ
            (fun X => if X = P then t.1
              else if X = Q then t.2 else 0) : ℝ)
           = 720 / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ)
            : ℝ) :=
        multinomial6_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : multSupport (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) = C := by
        have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
        have ht2 : 1 ≤ t.2 := (Finset.mem_Icc.mp htS.2.2).1
        refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter, Finset.mem_filter, Finset.mem_univ,
          true_and, hCeq, Finset.mem_insert, Finset.mem_singleton]
        by_cases hXP : X = P
        · rw [hXP]
          simp [show t.1 ≠ 0 by omega]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            simp [hXP, Ne.symm hPQ, show t.2 ≠ 0 by omega]
          · simp [hXP, hXQ]
      have hint : ∫ α : LayerSite N → G,
            ∏ X ∈ Finset.univ,
              (colDensC ρ u u' X α)
                ^ ((fun X => if X = P then t.1
                    else if X = Q then t.2 else 0) X)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = densMomentValue ρ μG t.1
            * densMomentValue ρ μG t.2 := by
        rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_card_le_three6 ρ μG hN hN3
            hρcont u u' C (by omega) _,
          hCeq, Finset.prod_insert (by
            rw [Finset.mem_singleton]
            exact hPQ), Finset.prod_singleton]
        show densMomentValue ρ μG
              (if P = P then t.1 else if P = Q then t.2 else 0)
            * densMomentValue ρ μG
              (if Q = P then t.1 else if Q = Q then t.2 else 0)
          = densMomentValue ρ μG t.1 * densMomentValue ρ μG t.2
        rw [if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl]
      rw [hmult, hint]
  rw [hbij]
  have hSeq : S = {(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)} := by
    refine Finset.ext fun t => ?_
    obtain ⟨a, b⟩ := t
    simp only [hS, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hSeq]
  rw [Finset.sum_insert (by
        simp [Prod.ext_iff]),
    Finset.sum_insert (by
        simp [Prod.ext_iff]),
    Finset.sum_insert (by
        simp [Prod.ext_iff]),
    Finset.sum_insert (by
        simp [Prod.ext_iff]),
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring
/-- **The card-3 fiber.** Over a 3-support
`{P, Q, R}`, the fiber is the ten positive exponent
triples summing to `6` (parametrized by
`(k P, k Q, k R)`); the fiber sum evaluates to the
`(4,1,1)` terms at coefficient `30`, the `(3,2,1)`
terms at coefficient `60`, and the `(2,2,2)` term
at coefficient `90` — the card-3 patterns of
`kappa6Const`. -/
theorem fiber_card_three6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 3) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 30 * (densMomentValue ρ μG 4
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
        + 30 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 4 * densMomentValue ρ μG 1))
        + 30 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4))
        + 60 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
        + 60 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
        + 60 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
        + 60 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
        + 60 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2))
        + 60 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3))
        + 90 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 2)) := by
  classical
  obtain ⟨P, Q, R, hPQ, hPR, hQR, hCeq⟩ :=
    Finset.card_eq_three.mp hC
  set S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 4 ×ˢ Finset.Icc 1 4 ×ˢ Finset.Icc 1 4).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 6) with hS
  have hnotP : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPR⟩
  have hnotQ : Q ∉ ({R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hQR
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (720
            / ((Nat.factorial t.1 * Nat.factorial t.2.1
              * Nat.factorial t.2.2 : ℕ) : ℝ))
          * (densMomentValue ρ μG t.1
            * (densMomentValue ρ μG t.2.1
              * densMomentValue ρ μG t.2.2)) := by
    refine (Finset.sum_bij
      (fun t _ => fun X => if X = P then t.1
        else if X = Q then t.2.1
        else if X = R then t.2.2 else 0) ?_ ?_ ?_ ?_).symm
    · intro t ht
      have htS : t.1 + t.2.1 + t.2.2 = 6
          ∧ t.1 ∈ Finset.Icc 1 4 ∧ t.2.1 ∈ Finset.Icc 1 4
          ∧ t.2.2 ∈ Finset.Icc 1 4 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).1,
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).2⟩
      have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
      have ht2 : 1 ≤ t.2.1 := (Finset.mem_Icc.mp htS.2.2.1).1
      have ht3 : 1 ≤ t.2.2 := (Finset.mem_Icc.mp htS.2.2.2).1
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun X _ => Finset.mem_univ X⟩, ?_⟩
      · have h1 : ∀ X ∈ Finset.univ,
            (if X = P then t.1 else if X = Q then t.2.1
              else if X = R then t.2.2 else 0)
              = if X ∈ C then
                  (if X = P then t.1 else if X = Q then t.2.1
                    else if X = R then t.2.2 else 0)
                else 0 :=
          fun X _ => by
            by_cases hX : X ∈ C
            · rw [if_pos hX]
            · have hX0 : X ∉ C := hX
              rw [hCeq, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hX
              push_neg at hX
              rw [if_neg hX0, if_neg hX.1, if_neg hX.2.1,
                if_neg hX.2.2]
        rw [Finset.sum_congr rfl h1,
          ← Finset.sum_subset (Finset.subset_univ C)
            (fun X _ hX => if_neg hX)]
        rw [hCeq, Finset.sum_insert hnotP,
          Finset.sum_insert hnotQ, Finset.sum_singleton]
        rw [if_pos (Finset.mem_insert_self P {Q, R}),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert_self Q {R}))),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton_self R))))),
          if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl,
          if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl]
        omega
      · refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter, Finset.mem_filter, Finset.mem_univ,
          true_and, hCeq, Finset.mem_insert, Finset.mem_singleton]
        by_cases hXP : X = P
        · rw [hXP]
          simp [show t.1 ≠ 0 by omega]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            simp [hXP, Ne.symm hPQ, show t.2.1 ≠ 0 by omega]
          · by_cases hXR : X = R
            · rw [hXR]
              simp [hXP, hXQ, Ne.symm hPR, Ne.symm hQR,
                show t.2.2 ≠ 0 by omega]
            · simp [hXP, hXQ, hXR]
    · intro t ht t' ht' h
      have h1 : t.1 = t'.1 := by
        have hP := congrFun h P
        rw [if_pos rfl, if_pos rfl] at hP
        exact hP
      have h2 : t.2.1 = t'.2.1 := by
        have hQ := congrFun h Q
        rw [if_neg (Ne.symm hPQ), if_neg (Ne.symm hPQ),
          if_pos rfl, if_pos rfl] at hQ
        exact hQ
      have h3 : t.2.2 = t'.2.2 := by
        have hR := congrFun h R
        rw [if_neg (Ne.symm hPR), if_neg (Ne.symm hPR),
          if_neg (Ne.symm hQR), if_neg (Ne.symm hQR),
          if_pos rfl, if_pos rfl] at hR
        exact hR
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro k hk
      have hk6 : ∑ X ∈ Finset.univ, k X = 6 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 6 := by
        rw [← hsupp, ← sum_univ_eq_sum_multSupport]
        exact hk6
      have hge : ∀ X ∈ C, 1 ≤ k X := by
        intro X hX
        have hXs : X ∈ multSupport k := hsupp ▸ hX
        exact Nat.one_le_iff_ne_zero.mpr
          (Finset.mem_filter.mp hXs).2
      rw [hCeq, Finset.sum_insert hnotP,
        Finset.sum_insert hnotQ, Finset.sum_singleton] at hsumC
      have hkP1 : 1 ≤ k P := hge P (by
        rw [hCeq, Finset.mem_insert]
        exact Or.inl rfl)
      have hkQ1 : 1 ≤ k Q := hge Q (by
        rw [hCeq, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton]
        exact Or.inr (Or.inl rfl))
      have hkR1 : 1 ≤ k R := hge R (by
        rw [hCeq, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton]
        exact Or.inr (Or.inr rfl))
      have hkP4 : k P ≤ 4 := by omega
      have hkQ4 : k Q ≤ 4 := by omega
      have hkR4 : k R ≤ 4 := by omega
      have hsumC' : k P + k Q + k R = 6 := by omega
      refine ⟨(k P, k Q, k R), ?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_product,
          Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          Finset.mem_Icc]
        exact ⟨⟨⟨hkP1, hkP4⟩, ⟨hkQ1, hkQ4⟩, ⟨hkR1, hkR4⟩⟩,
          hsumC'⟩
      · funext X
        by_cases hXP : X = P
        · rw [hXP, if_pos rfl]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            have hQP : Q ≠ P := by
              rintro rfl
              exact hXP hXQ
            rw [if_neg hQP, if_pos rfl]
          · by_cases hXR : X = R
            · rw [hXR]
              have hRP : R ≠ P := by
                rintro rfl
                exact hXP hXR
              have hRQ : R ≠ Q := by
                rintro rfl
                exact hXQ hXR
              rw [if_neg hRP, if_neg hRQ, if_pos rfl]
            · have hk0 : k X = 0 := by
                by_contra hne
                have hXs : X ∈ multSupport k := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ X, hne⟩
                rw [hsupp, hCeq, Finset.mem_insert,
                  Finset.mem_insert, Finset.mem_singleton]
                  at hXs
                exact hXs.elim hXP
                  (fun h => h.elim hXQ hXR)
              rw [hk0]
              simp [hXP, hXQ, hXR]
    · intro t ht
      have htS : t.1 + t.2.1 + t.2.2 = 6
          ∧ t.1 ∈ Finset.Icc 1 4 ∧ t.2.1 ∈ Finset.Icc 1 4
          ∧ t.2.2 ∈ Finset.Icc 1 4 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).1,
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).2⟩
      have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
      have ht2 : 1 ≤ t.2.1 := (Finset.mem_Icc.mp htS.2.2.1).1
      have ht3 : 1 ≤ t.2.2 := (Finset.mem_Icc.mp htS.2.2.2).1
      have hsum : ∑ X ∈ Finset.univ,
          (fun X => if X = P then t.1 else if X = Q then t.2.1
            else if X = R then t.2.2 else 0) X = 6 := by
        have h1 : ∀ X ∈ Finset.univ,
            (if X = P then t.1 else if X = Q then t.2.1
              else if X = R then t.2.2 else 0)
              = if X ∈ C then
                  (if X = P then t.1 else if X = Q then t.2.1
                    else if X = R then t.2.2 else 0)
                else 0 :=
          fun X _ => by
            by_cases hX : X ∈ C
            · rw [if_pos hX]
            · have hX0 : X ∉ C := hX
              rw [hCeq, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hX
              push_neg at hX
              rw [if_neg hX0, if_neg hX.1, if_neg hX.2.1,
                if_neg hX.2.2]
        rw [Finset.sum_congr rfl h1,
          ← Finset.sum_subset (Finset.subset_univ C)
            (fun X _ hX => if_neg hX),
          hCeq, Finset.sum_insert hnotP,
          Finset.sum_insert hnotQ, Finset.sum_singleton]
        rw [if_pos (Finset.mem_insert_self P {Q, R}),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert_self Q {R}))),
          if_pos (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton_self R))))),
          if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl,
          if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl]
        omega
      have hfact : ∏ X ∈ Finset.univ,
          Nat.factorial ((fun X => if X = P then t.1
            else if X = Q then t.2.1
            else if X = R then t.2.2 else 0) X)
            = Nat.factorial t.1 * Nat.factorial t.2.1
              * Nat.factorial t.2.2 := by
        have h1 : ∏ X ∈ Finset.univ,
              Nat.factorial ((fun X => if X = P then t.1
                else if X = Q then t.2.1
                else if X = R then t.2.2 else 0) X)
            = ∏ X ∈ C,
              Nat.factorial ((fun X => if X = P then t.1
                else if X = Q then t.2.1
                else if X = R then t.2.2 else 0) X) :=
          (Finset.prod_subset (Finset.subset_univ C)
            (fun X _ hX => by
              rw [hCeq, Finset.mem_insert, Finset.mem_insert,
                Finset.mem_singleton] at hX
              push_neg at hX
              simp [hX.1, hX.2.1, hX.2.2])).symm
        rw [h1, hCeq, Finset.prod_insert hnotP,
          Finset.prod_insert hnotQ, Finset.prod_singleton]
        show Nat.factorial (if P = P then t.1
              else if P = Q then t.2.1
              else if P = R then t.2.2 else 0)
            * (Nat.factorial (if Q = P then t.1
              else if Q = Q then t.2.1
              else if Q = R then t.2.2 else 0)
            * Nat.factorial (if R = P then t.1
              else if R = Q then t.2.1
              else if R = R then t.2.2 else 0))
          = Nat.factorial t.1 * Nat.factorial t.2.1
            * Nat.factorial t.2.2
        rw [if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl,
          if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl,
          mul_assoc]
      have hmult : (Nat.multinomial Finset.univ
            (fun X => if X = P then t.1 else if X = Q then t.2.1
              else if X = R then t.2.2 else 0) : ℝ)
          = 720 / ((Nat.factorial t.1 * Nat.factorial t.2.1
              * Nat.factorial t.2.2 : ℕ) : ℝ) :=
        multinomial6_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : multSupport (fun X => if X = P then t.1
            else if X = Q then t.2.1
            else if X = R then t.2.2 else 0) = C := by
        refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter, Finset.mem_filter, Finset.mem_univ,
          true_and, hCeq, Finset.mem_insert, Finset.mem_singleton]
        by_cases hXP : X = P
        · rw [hXP]
          simp [show t.1 ≠ 0 by omega]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            simp [hXP, Ne.symm hPQ, show t.2.1 ≠ 0 by omega]
          · by_cases hXR : X = R
            · rw [hXR]
              simp [hXP, hXQ, Ne.symm hPR, Ne.symm hQR,
                show t.2.2 ≠ 0 by omega]
            · simp [hXP, hXQ, hXR]
      have hint : ∫ α : LayerSite N → G,
            ∏ X ∈ Finset.univ,
              (colDensC ρ u u' X α)
                ^ ((fun X => if X = P then t.1
                    else if X = Q then t.2.1
                    else if X = R then t.2.2 else 0) X)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = densMomentValue ρ μG t.1
            * (densMomentValue ρ μG t.2.1
              * densMomentValue ρ μG t.2.2) := by
        rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_card_le_three6 ρ μG hN hN3
            hρcont u u' C (by omega) _,
          hCeq, Finset.prod_insert hnotP,
          Finset.prod_insert hnotQ, Finset.prod_singleton]
        show densMomentValue ρ μG
              (if P = P then t.1 else if P = Q then t.2.1
                else if P = R then t.2.2 else 0)
            * (densMomentValue ρ μG
              (if Q = P then t.1 else if Q = Q then t.2.1
                else if Q = R then t.2.2 else 0)
            * densMomentValue ρ μG
              (if R = P then t.1 else if R = Q then t.2.1
                else if R = R then t.2.2 else 0))
          = densMomentValue ρ μG t.1
            * (densMomentValue ρ μG t.2.1
              * densMomentValue ρ μG t.2.2)
        rw [if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl,
          if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl]
      rw [hmult, hint]
  rw [hbij]
  have hSeq : S = {(4, 1, 1), (1, 4, 1), (1, 1, 4),
      (3, 2, 1), (3, 1, 2), (2, 3, 1), (2, 1, 3),
      (1, 3, 2), (1, 2, 3), (2, 2, 2)} := by
    refine Finset.ext fun t => ?_
    obtain ⟨a, b, c⟩ := t
    simp only [hS, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · intro h
      obtain ⟨⟨⟨ha1, ha4⟩, ⟨hb1, hb4⟩, ⟨hc1, hc4⟩⟩, hsum⟩ := h
      interval_cases a <;> interval_cases b <;>
        interval_cases c <;> simp at hsum ⊢
    · intro h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
        exact ⟨⟨⟨by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩,
          by norm_num⟩
  rw [hSeq]
  rw [Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring
end Fiber6

/-! ## B6-2b-ii: fibers over cards 5 and 4

The remaining nonconstant fibers of the sixth-power
expansion. Card 5 carries the single pattern
`(2,1,1,1,1)` (one doubled column, multinomial weight
`360`); card 4 carries `(3,1,1,1)` (weight `120` per
distinguished column) and `(2,2,1,1)` (weight `180`).
Each fiber is evaluated in raw form through its
pattern-value lemma: the density pattern integral is
expanded by the subset/strip engine into the moment
objects (the doubled 5-support moment below, the
`pentaReMoment` and erasure moments at card 5; the
tripled and doubled-doubled quad moments of B6-1 at
card 4, whose baseline-subtracted forms are B6-2a's
channel excesses). **No total assembly is asserted
here, no `kappa6dep` identity, and no sign is asserted
anywhere.** NO CLAIM; dials 0/4. -/

section Fiber6b

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The raw `(2,1,1,1,1)` moment at a 5-support `C`
with distinguished doubled column `P`: the stratum
integral of `(colRe P)² · ∏_{Q ∈ C.erase P} colRe Q`
— the character moment of the multiset `C + {P}`.
This is `doubledQuadReMoment`'s construction at
support size 5, named for the card-5 fiber as
`pentaReMoment` names the all-distinct moment at
support size 5. -/
noncomputable def doubledPentaReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The doubled 5-support moment is
`doubledQuadReMoment` itself: the moment construction
is support-size blind. -/
theorem doubledPentaReMoment_eq_doubledQuadReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) :
    doubledPentaReMoment ρ μG C P u u'
      = doubledQuadReMoment ρ μG C P u u' :=
  rfl

/-- The `(2,1,1,1,1)` pattern at `(C, P)`: exponent
`2` at `P`, exponent `1` on the rest of `C`, `0` off
`C`. -/
noncomputable def doubledPentaPattern (C : Finset (LayerColumn N))
    (P : LayerColumn N) : LayerColumn N → ℕ :=
  fun Q => if Q = P then 2 else if Q ∈ C then 1 else 0

/-- **The doubled quintuple pattern value.** For a
5-support `C` and a distinguished column `P ∈ C`, the
`(2,1,1,1,1)` density pattern value splits into its
fully-split baseline `A₂B⁴`, the order-4 excess of the
erased support `C.erase P` at weight `d⁻⁴`, twice the
sum of the order-4 excesses of the 4-subsupports
through `P` at weight `d⁻⁴`, minus the sum of their
doubled excesses at weight `d⁻⁵`, minus twice the
fivefold excess at weight `d⁻⁵`, and the doubled
5-support excess at weight `d⁻⁶`. Proved by the
two-level subset expansion: `x_P²` by `add_pow` over
`range 3`, the remaining four densities by the
powerset expansion — the mirror of
`integral_colDens_prod_quadruple_doubled` at one
support size up, with the extra subset level (the
3-subsets of `C.erase P`) contributing the two
erasure sums. -/
theorem integral_colDens_prod_quintuple_doubled (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C.erase P,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hRcard : (C.erase P).card = 4 := by
    rw [Finset.card_erase_of_mem hP, hC]
  have hnotP : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hx : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      colDensC ρ u u' Z α = c * colRe ρ u u' Z α + 1 := by
    intro Z α
    rw [colDensC_eq, div_eq_inv_mul]
    ring
  have hxP2 : ∀ α : LayerSite N → G,
      (colDensC ρ u u' P α) ^ 2
        = ∑ j ∈ Finset.range 3,
            (((2 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j := by
    intro α
    rw [hx P α, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, one_pow, mul_one]
    ring
  have hptS : ∀ α : LayerSite N → G,
      ∏ Q ∈ C.erase P, colDensC ρ u u' Q α
        = ∑ T ∈ (C.erase P).powerset, c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α := by
    intro α
    have h1 : ∏ Q ∈ C.erase P, colDensC ρ u u' Q α
        = ∏ Q ∈ C.erase P, (c * colRe ρ u u' Q α + 1) :=
      Finset.prod_congr rfl fun Q _ => hx Q α
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const]
  have hcong : ∀ (T : Finset (LayerColumn N))
      (hT : T ⊆ C.erase P) (j : ℕ) (α : LayerSite N → G),
      (colRe ρ u u' P α) ^ j * ∏ Q ∈ T, colRe ρ u u' Q α
      = ∏ Q ∈ insert P T,
          (colRe ρ u u' Q α) ^ (if Q = P then j else 1) := by
    intro T hT j α
    have hPT : P ∉ T := fun h => hnotP (hT h)
    rw [Finset.prod_insert hPT, if_pos rfl]
    refine congrArg₂ _ rfl ?_
    refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := fun h => (Finset.mem_erase.mp (hT hQ)).1 h
    rw [if_neg hQP, pow_one]
  have hA : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G, ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (e1 ρ μG) ^ T.card
          + (if T = C.erase P then
              (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    by_cases hTS : T = C.erase P
    · subst hTS
      rw [if_pos rfl, hRcard]
      show quadReMoment ρ μG (C.erase P) u u'
        = (e1 ρ μG) ^ 4
          + (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
      ring
    · rw [if_neg hTS]
      have hcardT : T.card ≤ 3 := by
        have h1 : T.card ≤ 4 := le_trans (Finset.card_le_card hsub)
          (le_of_eq hRcard)
        have hne4 : T.card ≠ 4 := fun h4 => hTS
          (Finset.eq_of_subset_of_card_le hsub
            (by rw [hRcard]; omega))
        omega
      rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
        u u' T hcardT, add_zero]
  have hB : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (e1 ρ μG) ^ (T.card + 1)
          + (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
             else 0)
          + (if T = C.erase P then
              (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    have hPT : P ∉ T := fun h => hnotP (hsub h)
    by_cases hTS : T = C.erase P
    · subst hTS
      have hnotpc : (C.erase P) ∉ Finset.powersetCard 3 (C.erase P) :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h4
          omega
      rw [if_neg hnotpc, if_pos rfl, hRcard]
      have hpt : ∀ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
          = ∏ Q ∈ C, colRe ρ u u' Q α := fun α =>
        Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hP
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      show pentaReMoment ρ μG C u u'
        = (e1 ρ μG) ^ (4 + 1) + 0
          + (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
      ring
    · rw [if_neg hTS]
      by_cases hT3 : T ∈ Finset.powersetCard 3 (C.erase P)
      · rw [if_pos hT3]
        have hcardT : T.card = 3 :=
          (Finset.mem_powersetCard.mp hT3).2
        have hpt : ∀ α : LayerSite N → G,
            colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
            = ∏ Q ∈ insert P T, colRe ρ u u' Q α := fun α => by
          rw [← Finset.mul_prod_erase (insert P T)
            (fun Q => colRe ρ u u' Q α)
            (Finset.mem_insert_self P T),
            Finset.erase_insert hPT]
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
          hcardT]
        show quadReMoment ρ μG (insert P T) u u'
          = (e1 ρ μG) ^ (3 + 1)
            + (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 4) + 0
        ring
      · rw [if_neg hT3, add_zero, add_zero]
        have hcardT : T.card ≤ 2 := by
          have h1 : T.card ≤ 4 := le_trans (Finset.card_le_card hsub)
            (le_of_eq hRcard)
          have hne4 : T.card ≠ 4 := fun h4 => hTS
            (Finset.eq_of_subset_of_card_le hsub
              (by rw [hRcard]; omega))
          have hne3 : T.card ≠ 3 := fun h3 => hT3
            (Finset.mem_powersetCard.mpr ⟨hsub, h3⟩)
          omega
        have hpt1 : ∀ α : LayerSite N → G,
            colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
            = ∏ Q ∈ insert P T,
                (colRe ρ u u' Q α) ^ (if Q = P then 1 else 1) := by
          intro α
          have h := hcong T hsub 1 α
          rwa [pow_one] at h
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
          integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
            hρcont u u' (insert P T) (by
              rw [Finset.card_insert_of_notMem hPT]
              omega) _,
          Finset.prod_insert hPT, if_pos rfl]
        have hprod1 : (∏ Q ∈ T,
              realMoment ρ μG (if Q = P then 1 else 1))
            = ∏ _Q ∈ T, realMoment ρ μG 1 :=
          Finset.prod_congr rfl fun Q hQ => by
            rw [if_neg (fun h =>
              (Finset.mem_erase.mp (hsub hQ)).1 h)]
        rw [hprod1]
        simp only [realMoment_one, Finset.prod_const]
        exact (pow_succ' _ _).symm
  have hCval : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          (colRe ρ u u' P α) ^ 2 * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
          + (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0)
          + (if T = C.erase P then
              (doubledPentaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    have hPT : P ∉ T := fun h => hnotP (hsub h)
    by_cases hTS : T = C.erase P
    · subst hTS
      have hnotpc : (C.erase P) ∉ Finset.powersetCard 3 (C.erase P) :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h4
          omega
      rw [if_neg hnotpc, if_pos rfl, hRcard]
      show doubledPentaReMoment ρ μG C P u u'
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 4 + 0
          + (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      ring
    · rw [if_neg hTS]
      by_cases hT3 : T ∈ Finset.powersetCard 3 (C.erase P)
      · rw [if_pos hT3]
        have hcardT : T.card = 3 :=
          (Finset.mem_powersetCard.mp hT3).2
        have hpt : ∀ α : LayerSite N → G,
            (colRe ρ u u' P α) ^ 2 * ∏ Q ∈ T, colRe ρ u u' Q α
            = ∏ Q ∈ insert P T,
                (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1) :=
          fun α => hcong T hsub 2 α
        have hpt2 : ∀ α : LayerSite N → G,
            ∏ Q ∈ insert P T,
                (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1)
            = (colRe ρ u u' P α) ^ 2
              * ∏ Q ∈ T, colRe ρ u u' Q α := fun α => by
          rw [Finset.prod_insert hPT, if_pos rfl]
          refine congrArg₂ _ rfl ?_
          exact Finset.prod_congr rfl fun Q hQ => by
            rw [if_neg (fun h =>
              (Finset.mem_erase.mp (hsub hQ)).1 h), pow_one]
        have hdef : doubledQuadReMoment ρ μG (insert P T) P u u'
            = ∫ α : LayerSite N → G,
                ∏ Q ∈ insert P T,
                  (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1)
                ∂(Measure.pi fun _ : LayerSite N => μG) := by
          show (∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ 2
              * ∏ Q ∈ (insert P T).erase P, colRe ρ u u' Q α
              ∂(Measure.pi fun _ : LayerSite N => μG)) = _
          rw [Finset.erase_insert hPT]
          exact integral_congr_ae
            (Filter.Eventually.of_forall fun α => (hpt2 α).symm)
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
          hcardT, ← hdef]
        ring
      · rw [if_neg hT3, add_zero, add_zero]
        have hcardT : T.card ≤ 2 := by
          have h1 : T.card ≤ 4 := le_trans (Finset.card_le_card hsub)
            (le_of_eq hRcard)
          have hne4 : T.card ≠ 4 := fun h4 => hTS
            (Finset.eq_of_subset_of_card_le hsub
              (by rw [hRcard]; omega))
          have hne3 : T.card ≠ 3 := fun h3 => hT3
            (Finset.mem_powersetCard.mpr ⟨hsub, h3⟩)
          omega
        rw [integral_congr_ae (Filter.Eventually.of_forall
            fun α => hcong T hsub 2 α),
          integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
            hρcont u u' (insert P T) (by
              rw [Finset.card_insert_of_notMem hPT]
              omega) _,
          Finset.prod_insert hPT, if_pos rfl]
        have hprod1 : (∏ Q ∈ T,
              realMoment ρ μG (if Q = P then 2 else 1))
            = ∏ _Q ∈ T, realMoment ρ μG 1 :=
          Finset.prod_congr rfl fun Q hQ => by
            rw [if_neg (fun h =>
              (Finset.mem_erase.mp (hsub hQ)).1 h)]
        rw [hprod1]
        simp only [realMoment_one, Finset.prod_const]
  have hIntTerm : ∀ j ∈ Finset.range 3,
      ∀ T ∈ (C.erase P).powerset,
      Integrable (fun α : LayerSite N → G =>
        ((((2 : ℕ).choose j : ℝ) * c ^ j) * (colRe ρ u u' P α) ^ j)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro j hj T hT
    have hj3 : j < 3 := Finset.mem_range.mp hj
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    interval_cases j
    · have hfun : (fun α : LayerSite N → G =>
          ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α := by
        funext α
        simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero,
          mul_one, one_mul]
      rw [hfun]
      exact Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl fun Q _ =>
              pow_one (colRe ρ u u' Q α))) _
    · have hfun : (fun α : LayerSite N → G =>
          ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => (((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card))
            * ∏ Q ∈ insert P T, colRe ρ u u' Q α := by
        funext α
        rw [Finset.prod_insert (fun h => hnotP (hsub h))]
        simp only [pow_one]
        rw [pow_add]
        ring
      rw [hfun]
      exact Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' (insert P T)
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl fun Q _ =>
              pow_one (colRe ρ u u' Q α))) _
    · have hfun : (fun α : LayerSite N → G =>
          ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => (((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card))
            * ∏ Q ∈ insert P T,
              (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1) := by
        funext α
        rw [← hcong T hsub 2 α, pow_add]
        ring
      rw [hfun]
      exact Integrable.const_mul (integrable_colRe_prod_pow ρ μG
        hρcont u u' (insert P T) _) _
  have hval0 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * ((e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
            * (colRe ρ u u' P α) ^ 0)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α := by
      intro α
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, one_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hA T hT]
    simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
      one_mul]
  have hval1 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
            * (colRe ρ u u' P α) ^ 1)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = (((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card))
          * (colRe ρ u u' P α
            * ∏ Q ∈ T, colRe ρ u u' Q α) := by
      intro α
      simp only [pow_one]
      rw [pow_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hB T hT]
  have hval2 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = C.erase P then
                (doubledPentaReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
            * (colRe ρ u u' P α) ^ 2)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = (((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card))
          * ((colRe ρ u u' P α) ^ 2
            * ∏ Q ∈ T, colRe ρ u u' Q α) := by
      intro α
      rw [pow_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hCval T hT]
  have hpt3 : ∀ α : LayerSite N → G,
      ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
      = (∑ T ∈ (C.erase P).powerset,
          ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        + (∑ T ∈ (C.erase P).powerset,
          ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        + (∑ T ∈ (C.erase P).powerset,
          ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)) := by
    intro α
    have h0 : ∏ Q ∈ C,
          (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
        = (colDensC ρ u u' P α) ^ 2
          * ∏ Q ∈ C.erase P, colDensC ρ u u' Q α := by
      conv_lhs => rw [← Finset.insert_erase hP]
      rw [Finset.prod_insert hnotP, if_pos rfl]
      refine congrArg₂ _ rfl ?_
      refine Finset.prod_congr rfl fun Q hQ => ?_
      have hQP : Q ≠ P := fun h => (Finset.mem_erase.mp hQ).1 h
      rw [if_neg hQP, pow_one]
    rw [h0, hxP2 α, hptS α]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [add_mul, add_mul]
    simp only [Finset.mul_sum]
  have hBS : ∑ T ∈ (C.erase P).powerset, (c * e1 ρ μG) ^ T.card
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    calc ∑ T ∈ (C.erase P).powerset, (c * e1 ρ μG) ^ T.card
        = ∑ T ∈ (C.erase P).powerset,
            (∏ Q ∈ T, (c * e1 ρ μG))
              * ∏ Q ∈ (C.erase P) \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const, Finset.prod_const_one, mul_one]
      _ = ∏ Q ∈ C.erase P, (c * e1 ρ μG + 1) :=
          (Finset.prod_add _ _ _).symm
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
          rw [Finset.prod_const, hRcard]
          congr 1
          rw [div_eq_inv_mul]
          ring
  have hbijF : ∀ F : Finset (LayerColumn N) → ℝ,
      ∑ x ∈ C.erase P, F (C.erase x)
        = ∑ T ∈ Finset.powersetCard 3 (C.erase P), F (insert P T) := by
    intro F
    refine Finset.sum_bij (fun x _ => (C.erase P).erase x) ?_ ?_ ?_ ?_
    · intro x hx
      have hxR : x ∈ C.erase P := hx
      refine Finset.mem_powersetCard.mpr
        ⟨Finset.erase_subset x (C.erase P), ?_⟩
      rw [Finset.card_erase_of_mem hxR, hRcard]
    · intro x hx y hy hxy
      by_contra hne
      have hxR : x ∈ C.erase P := hx
      have hmem : x ∈ (C.erase P).erase y :=
        Finset.mem_erase.mpr ⟨hne, hxR⟩
      rw [← hxy] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    · intro T hT
      have hsub : T ⊆ C.erase P :=
        (Finset.mem_powersetCard.mp hT).1
      have hcardT : T.card = 3 :=
        (Finset.mem_powersetCard.mp hT).2
      have hsd : ((C.erase P) \ T).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
          hRcard, hcardT]
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsd
      have hxmem : x ∈ (C.erase P) \ T := by
        rw [hx]
        exact Finset.mem_singleton_self x
      have hxR : x ∈ C.erase P := (Finset.mem_sdiff.mp hxmem).1
      have hxT : x ∉ T := (Finset.mem_sdiff.mp hxmem).2
      refine ⟨x, hxR, ?_⟩
      have hsub2 : T ⊆ (C.erase P).erase x := by
        intro Q hQ
        exact Finset.mem_erase.mpr
          ⟨fun h => hxT (h ▸ hQ), hsub hQ⟩
      have hcardx : ((C.erase P).erase x).card = 3 := by
        rw [Finset.card_erase_of_mem hxR, hRcard]
      have hEq : T = (C.erase P).erase x :=
        Finset.eq_of_subset_of_card_le hsub2
          (by rw [hcardx, hcardT])
      exact hEq.symm
    · intro x hx
      have hxR : x ∈ C.erase P := hx
      have hxP : x ≠ P := (Finset.mem_erase.mp hxR).1
      have hset : insert P ((C.erase P).erase x) = C.erase x := by
        have hsub1 : C.erase x
            ⊆ insert P ((C.erase P).erase x) := by
          intro Q hQ
          have hQx : Q ≠ x := (Finset.mem_erase.mp hQ).1
          have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
          by_cases hQP : Q = P
          · rw [hQP]
            exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem ?_
            exact Finset.mem_erase.mpr
              ⟨hQx, Finset.mem_erase.mpr ⟨hQP, hQC⟩⟩
        have hsub2 : insert P ((C.erase P).erase x)
            ⊆ C.erase x := by
          intro Q hQ
          rcases Finset.mem_insert.mp hQ with rfl | hQ
          · exact Finset.mem_erase.mpr ⟨Ne.symm hxP, hP⟩
          · exact Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hQ).1,
                (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hQ).2).2⟩
        exact Finset.Subset.antisymm hsub2 hsub1
      rw [hset]
  have hB0base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    have hT0 : ∀ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (e1 ρ μG) ^ T.card
          = (c * e1 ρ μG) ^ T.card := by
      intro T _
      simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
        one_mul]
      exact (mul_pow _ _ _).symm
    exact (Finset.sum_congr rfl hT0).trans hBS
  have hB0corr : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (if T = C.erase P then
              (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
             else 0))
      = ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [show (0 + 4 : ℕ) = 4 from rfl, hc4]
  have hB0 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * ((e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
               else 0)))
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB0base, hB0corr]
  have hB1base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (e1 ρ μG) ^ (T.card + 1))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    have hT1 : ∀ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (e1 ρ μG) ^ (T.card + 1)
          = (2 * c * e1 ρ μG) * (c * e1 ρ μG) ^ T.card := by
      intro T _
      rw [mul_pow, pow_add, pow_add]
      simp only [Nat.choose_one_right, Nat.cast_ofNat, pow_one]
      ring
    exact (Finset.sum_congr rfl hT1).trans
      ((Finset.mul_sum _ _ _).symm.trans (congrArg _ hBS))
  have hB1mid : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
             else 0))
      = 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C.erase P,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
    have hsubpc : Finset.powersetCard 3 (C.erase P)
        ⊆ (C.erase P).powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ (C.erase P).powerset,
          ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 4)
               else 0))
        = ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
              * (quadReMoment ρ μG (insert P T) u u'
                - (e1 ρ μG) ^ 4) :=
      (Finset.sum_subset hsubpc (fun T _ hT => by
        rw [if_neg hT, mul_zero])).symm.trans
        (Finset.sum_congr rfl fun T hT => by rw [if_pos hT])
    have step2 : (∑ T ∈ Finset.powersetCard 3 (C.erase P),
          ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 4))
        = 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 4) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 3 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (1 + 3 : ℕ) = 4 from rfl, hc4]
      simp only [Nat.choose_one_right, Nat.cast_ofNat]
    rw [step1, step2]
    exact congrArg (fun z => 2 * ((d : ℝ)⁻¹) ^ 4 * z)
      (hbijF (fun S => quadReMoment ρ μG S u u'
        - (e1 ρ μG) ^ 4)).symm
  have hB1top : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T = C.erase P then
              (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
             else 0))
      = -(2 * ((d : ℝ)⁻¹) ^ 5
          * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard]
    rw [show (1 + 4 : ℕ) = 5 from rfl, hc5]
    simp only [Nat.choose_one_right, Nat.cast_ofNat]
    ring
  have hB1 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
               else 0)))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C.erase P,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5) := by
    rw [Finset.sum_congr rfl (fun T _ => by
        rw [mul_add, mul_add]),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hB1base,
      hB1mid, hB1top]
    ring
  have hB2base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    have hT2 : ∀ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card)
          = (c ^ 2 * realMoment ρ μG 2)
            * (c * e1 ρ μG) ^ T.card := by
      intro T _
      rw [mul_pow, pow_add]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
      ring
    exact (Finset.sum_congr rfl hT2).trans
      ((Finset.mul_sum _ _ _).symm.trans (congrArg _ hBS))
  have hB2mid : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
      = -(((d : ℝ)⁻¹) ^ 5
          * ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    have hsubpc : Finset.powersetCard 3 (C.erase P)
        ⊆ (C.erase P).powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ (C.erase P).powerset,
          ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0))
        = ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
              * (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
      (Finset.sum_subset hsubpc (fun T _ hT => by
        rw [if_neg hT, mul_zero])).symm.trans
        (Finset.sum_congr rfl fun T hT => by rw [if_pos hT])
    have step2 : (∑ T ∈ Finset.powersetCard 3 (C.erase P),
          ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = c ^ 5
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 3 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (2 + 3 : ℕ) = 5 from rfl]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
    rw [step1, step2, hc5]
    have hsum := (hbijF (fun S =>
      doubledQuadReMoment ρ μG S P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)).symm
    have h2 := congrArg (fun z => (-((d : ℝ)⁻¹) ^ 5) * z) hsum
    simpa only [neg_mul] using h2
  have hB2top : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T = C.erase P then
              (doubledPentaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
             else 0))
      = ((d : ℝ)⁻¹) ^ 6
          * (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show (2 + 4 : ℕ) = 6 from rfl, hc6]
  have hB2 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = C.erase P then
                (doubledPentaReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
               else 0)))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => by
        rw [mul_add, mul_add]),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hB2base,
      hB2mid, hB2top]
    simp only [sub_eq_add_neg]
  have hA2 : densMomentValue ρ μG 2
      = 1 + 2 * c * (e1 ρ μG) + c ^ 2 * realMoment ρ μG 2 := by
    have h2 : densMomentValue ρ μG 2
        = 1 - 2 * (e1 ρ μG) * ((d : ℝ)⁻¹)
          + realMoment ρ μG 2 * ((d : ℝ)⁻¹) ^ 2 := by
      unfold densMomentValue
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      simp only [Nat.choose_self, Nat.choose_one_right, pow_zero,
        pow_one, Nat.cast_ofNat, Nat.cast_one]
      rw [show Nat.choose 2 0 = 1 from rfl, realMoment_zero,
        realMoment_one]
      ring
    rw [h2, hc]
    ring
  have hI0 : Integrable (fun α : LayerSite N → G =>
      ∑ T ∈ (C.erase P).powerset,
        ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
            * (colRe ρ u u' P α) ^ 0)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_finsetSum _ (fun T hT =>
      hIntTerm 0 (by decide) T hT)
  have hI1 : Integrable (fun α : LayerSite N → G =>
      ∑ T ∈ (C.erase P).powerset,
        ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
            * (colRe ρ u u' P α) ^ 1)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_finsetSum _ (fun T hT =>
      hIntTerm 1 (by decide) T hT)
  have hI2 : Integrable (fun α : LayerSite N → G =>
      ∑ T ∈ (C.erase P).powerset,
        ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
            * (colRe ρ u u' P α) ^ 2)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_finsetSum _ (fun T hT =>
      hIntTerm 2 (by decide) T hT)
  calc ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          (∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                * (colRe ρ u u' P α) ^ 0)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
          + (∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                * (colRe ρ u u' P α) ^ 1)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
          + (∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
                * (colRe ρ u u' P α) ^ 2)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt3)
    _ = (∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                * (colRe ρ u u' P α) ^ 0)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        + ∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                * (colRe ρ u u' P α) ^ 1)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        + ∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
                * (colRe ρ u u' P α) ^ 2)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
        have h1 : (∫ α : LayerSite N → G,
              (∑ T ∈ (C.erase P).powerset,
                ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                    * (colRe ρ u u' P α) ^ 0)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              + (∑ T ∈ (C.erase P).powerset,
                ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                    * (colRe ρ u u' P α) ^ 1)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              ∂(Measure.pi fun _ : LayerSite N => μG))
            = (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                      * (colRe ρ u u' P α) ^ 0)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                      * (colRe ρ u u' P α) ^ 1)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)) :=
          integral_add hI0 hI1
        have h2 : (∫ α : LayerSite N → G,
              ((∑ T ∈ (C.erase P).powerset,
                ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                    * (colRe ρ u u' P α) ^ 0)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              + (∑ T ∈ (C.erase P).powerset,
                ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                    * (colRe ρ u u' P α) ^ 1)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
              + (∑ T ∈ (C.erase P).powerset,
                ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
                    * (colRe ρ u u' P α) ^ 2)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              ∂(Measure.pi fun _ : LayerSite N => μG))
            = (∫ α : LayerSite N → G,
                (∑ T ∈ (C.erase P).powerset,
                  ((((2 : ℕ).choose 0 : ℝ) * c ^ 0)
                      * (colRe ρ u u' P α) ^ 0)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
                + (∑ T ∈ (C.erase P).powerset,
                  ((((2 : ℕ).choose 1 : ℝ) * c ^ 1)
                      * (colRe ρ u u' P α) ^ 1)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
                ∂(Measure.pi fun _ : LayerSite N => μG))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((2 : ℕ).choose 2 : ℝ) * c ^ 2)
                      * (colRe ρ u u' P α) ^ 2)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)) := by
          simpa only [Pi.add_apply] using
            integral_add (hI0.add hI1) hI2
        rw [h2, h1]
    _ = ((1 - e1 ρ μG / (d : ℝ)) ^ 4
          + ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4))
          + ((2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 4
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ x ∈ C.erase P,
                (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))
          + ((c ^ 2 * realMoment ρ μG 2)
              * (1 - e1 ρ μG / (d : ℝ)) ^ 4
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ x ∈ C.erase P,
                (doubledQuadReMoment ρ μG (C.erase x) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledPentaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) := by
        rw [integral_finsetSum _
            (fun T hT => hIntTerm 0 (by decide) T hT),
          integral_finsetSum _
            (fun T hT => hIntTerm 1 (by decide) T hT),
          integral_finsetSum _
            (fun T hT => hIntTerm 2 (by decide) T hT),
          Finset.sum_congr rfl (fun T hT => hval0 T hT),
          Finset.sum_congr rfl (fun T hT => hval1 T hT),
          Finset.sum_congr rfl (fun T hT => hval2 T hT),
          hB0, hB1, hB2]
    _ = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
          + ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * ∑ x ∈ C.erase P,
              (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ x ∈ C.erase P,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
        rw [hA2]
        ring
/-- **The card-5 fiber.** Over a 5-support `C`, the
fiber of the expansion is the five doubled patterns
(one per `P ∈ C`): classification by the
excess-exponent sum `∑ (k Q − 1) = 1` over `C`, whose
support in `C` is a singleton. Each pattern has
multinomial coefficient `360` and value the doubled
quintuple pattern value. -/
theorem fiber_card_five6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (360 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
            + ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ x ∈ C.erase P,
                (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ x ∈ C.erase P,
                (doubledQuadReMoment ρ μG (C.erase x) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledPentaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) := by
  classical
  have hsuppPat : ∀ P ∈ C,
      multSupport (doubledPentaPattern C P) = C := by
    intro P hP
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hQP : Q = P
    · subst hQP
      simp [doubledPentaPattern, hP]
    · by_cases hQC : Q ∈ C <;>
        simp [doubledPentaPattern, hQP, hQC]
  have hsumPat : ∀ P ∈ C,
      ∑ Q ∈ Finset.univ, doubledPentaPattern C P Q = 6 := by
    intro P hP
    have h1 : ∑ Q ∈ Finset.univ, doubledPentaPattern C P Q
        = ∑ Q ∈ C, doubledPentaPattern C P Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
          simp [doubledPentaPattern, hQ, hQP])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP]
    have h2 : ∀ Q ∈ C.erase P, doubledPentaPattern C P Q = 1 :=
      fun Q hQ => by
        simp [doubledPentaPattern, (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP, hC]
    have hPP : doubledPentaPattern C P P = 2 := by
      simp [doubledPentaPattern]
    rw [hPP]
    decide
  have hmemPat : ∀ P ∈ C, doubledPentaPattern C P
      ∈ (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C) := by
    intro P hP
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsumPat P hP, fun Q _ => Finset.mem_univ Q⟩,
      hsuppPat P hP⟩
  have hvalPat : ∀ P ∈ C,
      ((Nat.multinomial Finset.univ (doubledPentaPattern C P) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ Q ∈ Finset.univ,
                (colDensC ρ u u' Q α) ^ (doubledPentaPattern C P Q)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (360 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
            + ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ x ∈ C.erase P,
                (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ x ∈ C.erase P,
                (doubledQuadReMoment ρ μG (C.erase x) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledPentaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) := by
    intro P hP
    have hfact : ∏ Q ∈ Finset.univ,
        Nat.factorial (doubledPentaPattern C P Q) = 2 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial (doubledPentaPattern C P Q)
          = ∏ Q ∈ C, Nat.factorial (doubledPentaPattern C P Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
            simp [doubledPentaPattern, hQ, hQP])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP]
      have h2 : ∀ Q ∈ C.erase P,
          Nat.factorial (doubledPentaPattern C P Q) = 1 :=
        fun Q hQ => by
          simp [doubledPentaPattern, (Finset.mem_erase.mp hQ).1,
            (Finset.mem_erase.mp hQ).2]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      simp [doubledPentaPattern]
    have hmult : (Nat.multinomial Finset.univ
          (doubledPentaPattern C P) : ℝ) = 360 := by
      have h := multinomial6_univ_eq (doubledPentaPattern C P)
        (hsumPat P hP) 2 hfact two_ne_zero
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ Q ∈ Finset.univ,
            (colDensC ρ u u' Q α) ^ (doubledPentaPattern C P Q)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
          + ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * ∑ x ∈ C.erase P,
              (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ x ∈ C.erase P,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
      rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u'
        (doubledPentaPattern C P), hsuppPat P hP]
      have hprod : ∀ α : LayerSite N → G,
          ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (doubledPentaPattern C P Q)
            = ∏ Q ∈ C,
              (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1) :=
        fun α => Finset.prod_congr rfl fun Q hQ => by
          by_cases hQP : Q = P <;> simp [doubledPentaPattern, hQP, hQ]
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
      exact integral_colDens_prod_quintuple_doubled ρ μG hN hN3
        hρcont u u' C hC P hP
    rw [hmult, hint]
  have hsurj : ∀ k ∈ (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C),
      ∃ P, ∃ _ : P ∈ C, doubledPentaPattern C P = k := by
    intro k hk
    have hk6 : ∑ Q ∈ Finset.univ, k Q = 6 :=
      (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
    have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
    have hge : ∀ Q ∈ C, 1 ≤ k Q := by
      intro Q hQ
      have hQs : Q ∈ multSupport k := hsupp ▸ hQ
      exact Nat.one_le_iff_ne_zero.mpr
        (Finset.mem_filter.mp hQs).2
    have hsumC : ∑ Q ∈ C, k Q = 6 := by
      rw [← hsupp, ← sum_univ_eq_sum_multSupport]
      exact hk6
    have hm : ∑ Q ∈ C, (k Q - 1) = 1 := by
      have h1 : ∑ Q ∈ C, ((k Q - 1) + 1) = ∑ Q ∈ C, k Q :=
        Finset.sum_congr rfl fun Q hQ =>
          Nat.sub_add_cancel (hge Q hQ)
      rw [Finset.sum_add_distrib] at h1
      have hsc : ∑ Q ∈ C, (1 : ℕ) = 5 := by simp [hC]
      omega
    set D := C.filter (fun Q => k Q ≠ 1) with hD
    have hsumD : ∑ Q ∈ D, (k Q - 1) = 1 := by
      have hsub : ∑ Q ∈ D, (k Q - 1) = ∑ Q ∈ C, (k Q - 1) :=
        Finset.sum_subset (Finset.filter_subset _ _)
          fun Q hQC hQ => by
            have hkQ : k Q = 1 := by
              by_contra hne
              exact hQ (Finset.mem_filter.mpr ⟨hQC, hne⟩)
            exact Nat.sub_eq_zero_of_le (le_of_eq hkQ)
      rw [hsub]
      exact hm
    have hDne : D.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne,
        Finset.sum_empty] at hsumD
      exact one_ne_zero hsumD.symm
    have hDcard : D.card = 1 := by
      by_contra hne1
      have h0 : D.card ≠ 0 :=
        ne_of_gt (Finset.card_pos.mpr hDne)
      have hge2 : 2 ≤ D.card := by omega
      have hle : D.card ≤ ∑ Q ∈ D, (k Q - 1) := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum fun Q hQ => ?_
        have hQD : Q ∈ C ∧ k Q ≠ 1 := Finset.mem_filter.mp hQ
        have h1 := hge Q hQD.1
        omega
      omega
    obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hDcard
    have hPD : P ∈ D := by
      rw [hP]
      exact Finset.mem_singleton_self P
    have hPC : P ∈ C := (Finset.mem_filter.mp hPD).1
    refine ⟨P, hPC, ?_⟩
    funext Q
    by_cases hQP : Q = P
    · rw [hQP]
      have hothers : ∀ Q ∈ C.erase P, k Q = 1 := by
        intro Q hQ
        have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
        have hQne : Q ≠ P := (Finset.mem_erase.mp hQ).1
        by_contra hne
        have hQD : Q ∈ D := Finset.mem_filter.mpr ⟨hQC, hne⟩
        rw [hP] at hQD
        exact hQne (Finset.mem_singleton.mp hQD)
      have hsumErase : ∑ Q ∈ C.erase P, k Q = 4 := by
        rw [Finset.sum_congr rfl hothers, Finset.sum_const,
          Finset.card_erase_of_mem hPC, hC]
        simp [nsmul_eq_mul]
      have hkP : k P = 2 := by
        have h := Finset.add_sum_erase C k hPC
        omega
      rw [hkP]
      simp [doubledPentaPattern]
    · by_cases hQC : Q ∈ C
      · have hkQ : k Q = 1 := by
          by_contra hne
          have hQD : Q ∈ D := Finset.mem_filter.mpr ⟨hQC, hne⟩
          rw [hP] at hQD
          exact hQP (Finset.mem_singleton.mp hQD)
        rw [hkQ]
        simp [doubledPentaPattern, hQP, hQC]
      · have hkQ : k Q = 0 := by
          by_contra hne
          have hQs : Q ∈ multSupport k := Finset.mem_filter.mpr
            ⟨Finset.mem_univ Q, hne⟩
          rw [hsupp] at hQs
          exact hQC hQs
        rw [hkQ]
        simp [doubledPentaPattern, hQP, hQC]
  exact (Finset.sum_bij (fun P _ => doubledPentaPattern C P)
    hmemPat
    (fun P hP P' hP' h => by
      by_contra hne
      have h2 := congrFun h P
      simp [doubledPentaPattern, hne, hP] at h2)
    hsurj
    (fun P hP => (hvalPat P hP).symm)).symm

/-- **The tripled pattern value.** For a 4-support
`C` and a distinguished column `P ∈ C`, the
`(3,1,1,1)` pattern value splits into its fully-split
baseline `A₃B³`, three times the order-4 excess of
the support at weight `d⁻⁴`, minus three times the
doubled excess at weight `d⁻⁵`, and the tripled
excess at weight `d⁻⁶` — the baseline-subtracted
tripled term is exactly a summand of B6-2a's
`kappa6chan3111Excess`. Proved by the two-level
subset expansion: `x_P³` by `add_pow` over
`range 4`, the remaining three densities by the
powerset expansion, following
`integral_colDens_prod_quadruple_doubled` with the
distinguished exponent raised from `2` to `3`. -/
theorem integral_colDens_prod_quadruple_tripled (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 3 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hScard : (C.erase P).card = 3 := by
    rw [Finset.card_erase_of_mem hP, hC]
  have hnotP : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hx : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      colDensC ρ u u' Z α = c * colRe ρ u u' Z α + 1 := by
    intro Z α
    rw [colDensC_eq, div_eq_inv_mul]
    ring
  have hxP3 : ∀ α : LayerSite N → G,
      (colDensC ρ u u' P α) ^ 3
        = ∑ j ∈ Finset.range 4,
            (((3 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j := by
    intro α
    rw [hx P α, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, one_pow, mul_one]
    ring
  have hptS : ∀ α : LayerSite N → G,
      ∏ Q ∈ C.erase P, colDensC ρ u u' Q α
        = ∑ T ∈ (C.erase P).powerset, c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α := by
    intro α
    have h1 : ∏ Q ∈ C.erase P, colDensC ρ u u' Q α
        = ∏ Q ∈ C.erase P, (c * colRe ρ u u' Q α + 1) :=
      Finset.prod_congr rfl fun Q _ => hx Q α
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const]
  have hcong : ∀ (T : Finset (LayerColumn N))
      (hT : T ⊆ C.erase P) (j : ℕ) (α : LayerSite N → G),
      (colRe ρ u u' P α) ^ j * ∏ Q ∈ T, colRe ρ u u' Q α
      = ∏ Q ∈ insert P T,
          (colRe ρ u u' Q α) ^ (if Q = P then j else 1) := by
    intro T hT j α
    have hPT : P ∉ T := fun h => hnotP (hT h)
    rw [Finset.prod_insert hPT, if_pos rfl]
    refine congrArg₂ _ rfl ?_
    refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := fun h => (Finset.mem_erase.mp (hT hQ)).1 h
    rw [if_neg hQP, pow_one]
  have hA : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G, ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (e1 ρ μG) ^ T.card := by
    intro T hT
    refine integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
      u u' T (le_trans (Finset.card_le_card
        (Finset.mem_powerset.mp hT)) (le_of_eq hScard))
  have hB : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (e1 ρ μG) ^ (T.card + 1)
          + (if T = C.erase P then
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    by_cases hTS : T = C.erase P
    · subst hTS
      rw [if_pos rfl]
      have hpt : ∀ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
          = ∏ Q ∈ C, colRe ρ u u' Q α := fun α =>
        Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hP
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        hScard]
      show quadReMoment ρ μG C u u'
        = (e1 ρ μG) ^ 4
          + (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
      ring
    · rw [if_neg hTS]
      have hcardT : T.card ≤ 2 := by
        have h1 : T.card ≤ 3 := le_trans (Finset.card_le_card hsub)
          (le_of_eq hScard)
        rcases Nat.lt_or_ge T.card 3 with hlt | hge
        · omega
        · exfalso
          exact hTS (Finset.eq_of_subset_of_card_le hsub
            (by rw [hScard]; exact hge))
      have hpt : ∀ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
          = ∏ Q ∈ insert P T, colRe ρ u u' Q α := by
        intro α
        rw [Finset.prod_insert (fun h => hnotP (hsub h))]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
          u u' (insert P T) (by
            rw [Finset.card_insert_of_notMem
              (fun h => hnotP (hsub h))]
            omega),
        Finset.card_insert_of_notMem (fun h => hnotP (hsub h)),
        add_zero]
  have hCval : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          (colRe ρ u u' P α) ^ 2 * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
          + (if T = C.erase P then
              (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    by_cases hTS : T = C.erase P
    · subst hTS
      rw [if_pos rfl, hScard]
      show doubledQuadReMoment ρ μG C P u u'
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 3
          + (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      ring
    · rw [if_neg hTS]
      have hcardT : T.card ≤ 2 := by
        have h1 : T.card ≤ 3 := le_trans (Finset.card_le_card hsub)
          (le_of_eq hScard)
        rcases Nat.lt_or_ge T.card 3 with hlt | hge
        · omega
        · exfalso
          exact hTS (Finset.eq_of_subset_of_card_le hsub
            (by rw [hScard]; exact hge))
      rw [integral_congr_ae (Filter.Eventually.of_forall
          fun α => hcong T hsub 2 α),
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' (insert P T) (by
            rw [Finset.card_insert_of_notMem
              (fun h => hnotP (hsub h))]
            omega) _,
        Finset.prod_insert (fun h => hnotP (hsub h)), if_pos rfl]
      have hprod1 : (∏ Q ∈ T,
            realMoment ρ μG (if Q = P then 2 else 1))
          = ∏ _Q ∈ T, realMoment ρ μG 1 :=
        Finset.prod_congr rfl fun Q hQ => by
          rw [if_neg (fun h =>
            (Finset.mem_erase.mp (hsub hQ)).1 h)]
      rw [hprod1]
      simp only [realMoment_one, Finset.prod_const, add_zero]
  have hDval : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          (colRe ρ u u' P α) ^ 3 * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 3 * (e1 ρ μG) ^ T.card
          + (if T = C.erase P then
              (tripledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    by_cases hTS : T = C.erase P
    · subst hTS
      rw [if_pos rfl, hScard]
      show tripledQuadReMoment ρ μG C P u u'
        = realMoment ρ μG 3 * (e1 ρ μG) ^ 3
          + (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      ring
    · rw [if_neg hTS]
      have hcardT : T.card ≤ 2 := by
        have h1 : T.card ≤ 3 := le_trans (Finset.card_le_card hsub)
          (le_of_eq hScard)
        rcases Nat.lt_or_ge T.card 3 with hlt | hge
        · omega
        · exfalso
          exact hTS (Finset.eq_of_subset_of_card_le hsub
            (by rw [hScard]; exact hge))
      rw [integral_congr_ae (Filter.Eventually.of_forall
          fun α => hcong T hsub 3 α),
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' (insert P T) (by
            rw [Finset.card_insert_of_notMem
              (fun h => hnotP (hsub h))]
            omega) _,
        Finset.prod_insert (fun h => hnotP (hsub h)), if_pos rfl]
      have hprod1 : (∏ Q ∈ T,
            realMoment ρ μG (if Q = P then 3 else 1))
          = ∏ _Q ∈ T, realMoment ρ μG 1 :=
        Finset.prod_congr rfl fun Q hQ => by
          rw [if_neg (fun h =>
            (Finset.mem_erase.mp (hsub hQ)).1 h)]
      rw [hprod1]
      simp only [realMoment_one, Finset.prod_const, add_zero]
  have hIntTerm : ∀ j ∈ Finset.range 4,
      ∀ T ∈ (C.erase P).powerset,
      Integrable (fun α : LayerSite N → G =>
        ((((3 : ℕ).choose j : ℝ) * c ^ j) * (colRe ρ u u' P α) ^ j)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro j hj T hT
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    interval_cases j
    · have hfun : (fun α : LayerSite N → G =>
          ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α := by
        funext α
        simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero,
          mul_one, one_mul]
      rw [hfun]
      exact Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl fun Q _ =>
              pow_one (colRe ρ u u' Q α))) _
    · have hfun : (fun α : LayerSite N → G =>
          ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => (((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card))
            * ∏ Q ∈ insert P T, colRe ρ u u' Q α := by
        funext α
        rw [Finset.prod_insert (fun h => hnotP (hsub h))]
        simp only [pow_one]
        rw [pow_add]
        ring
      rw [hfun]
      exact Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' (insert P T)
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl fun Q _ =>
              pow_one (colRe ρ u u' Q α))) _
    · have hfun : (fun α : LayerSite N → G =>
          ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => (((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card))
            * ∏ Q ∈ insert P T,
              (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1) := by
        funext α
        rw [← hcong T hsub 2 α, pow_add]
        ring
      rw [hfun]
      exact Integrable.const_mul (integrable_colRe_prod_pow ρ μG
        hρcont u u' (insert P T) _) _
    · have hfun : (fun α : LayerSite N → G =>
          ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
              * (colRe ρ u u' P α) ^ 3)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        = fun α => (((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card))
            * ∏ Q ∈ insert P T,
              (colRe ρ u u' Q α) ^ (if Q = P then 3 else 1) := by
        funext α
        rw [← hcong T hsub 3 α, pow_add]
        ring
      rw [hfun]
      exact Integrable.const_mul (integrable_colRe_prod_pow ρ μG
        hρcont u u' (insert P T) _) _
  have hval0 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((3 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (e1 ρ μG) ^ T.card := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
            * (colRe ρ u u' P α) ^ 0)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α := by
      intro α
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, one_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hA T hT]
    simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
      one_mul]
  have hval1 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T = C.erase P then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
            * (colRe ρ u u' P α) ^ 1)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = (((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card))
          * (colRe ρ u u' P α
            * ∏ Q ∈ T, colRe ρ u u' Q α) := by
      intro α
      simp only [pow_one]
      rw [pow_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hB T hT]
  have hval2 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
            * (colRe ρ u u' P α) ^ 2)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = (((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card))
          * ((colRe ρ u u' P α) ^ 2
            * ∏ Q ∈ T, colRe ρ u u' Q α) := by
      intro α
      rw [pow_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hCval T hT]
  have hval3 : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
              * (colRe ρ u u' P α) ^ 3)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
          * (realMoment ρ μG 3 * (e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (tripledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
               else 0)) := by
    intro T hT
    have hW : ∀ α : LayerSite N → G,
        ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
            * (colRe ρ u u' P α) ^ 3)
          * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
        = (((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card))
          * ((colRe ρ u u' P α) ^ 3
            * ∏ Q ∈ T, colRe ρ u u' Q α) := by
      intro α
      rw [pow_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hW),
      integral_const_mul, hDval T hT]
  have hpt4 : ∀ α : LayerSite N → G,
      ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 3 else 1)
      = ((∑ T ∈ (C.erase P).powerset,
          ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
              * (colRe ρ u u' P α) ^ 0)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        + (∑ T ∈ (C.erase P).powerset,
          ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
              * (colRe ρ u u' P α) ^ 1)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
        + (∑ T ∈ (C.erase P).powerset,
          ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
              * (colRe ρ u u' P α) ^ 2)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        + (∑ T ∈ (C.erase P).powerset,
          ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
              * (colRe ρ u u' P α) ^ 3)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)) := by
    intro α
    have h0 : ∏ Q ∈ C,
          (colDensC ρ u u' Q α) ^ (if Q = P then 3 else 1)
        = (colDensC ρ u u' P α) ^ 3
          * ∏ Q ∈ C.erase P, colDensC ρ u u' Q α := by
      conv_lhs => rw [← Finset.insert_erase hP]
      rw [Finset.prod_insert hnotP, if_pos rfl]
      refine congrArg₂ _ rfl ?_
      refine Finset.prod_congr rfl fun Q hQ => ?_
      have hQP : Q ≠ P := fun h => (Finset.mem_erase.mp hQ).1 h
      rw [if_neg hQP, pow_one]
    rw [h0, hxP3 α, hptS α]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [add_mul, add_mul, add_mul]
    simp only [Finset.mul_sum]
  have hBS : ∑ T ∈ (C.erase P).powerset, (c * e1 ρ μG) ^ T.card
      = (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    calc ∑ T ∈ (C.erase P).powerset, (c * e1 ρ μG) ^ T.card
        = ∑ T ∈ (C.erase P).powerset,
            (∏ Q ∈ T, (c * e1 ρ μG))
              * ∏ Q ∈ (C.erase P) \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const, Finset.prod_const_one, mul_one]
      _ = ∏ Q ∈ C.erase P, (c * e1 ρ μG + 1) :=
          (Finset.prod_add _ _ _).symm
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
          rw [Finset.prod_const, hScard]
          congr 1
          rw [div_eq_inv_mul]
          ring
  have hB0 : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    have hT0 : ∀ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (e1 ρ μG) ^ T.card
          = (c * e1 ρ μG) ^ T.card := by
      intro T _
      simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
        one_mul]
      exact (mul_pow _ _ _).symm
    exact (Finset.sum_congr rfl hT0).trans hBS
  have hB1base : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (e1 ρ μG) ^ (T.card + 1))
      = (3 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    have hT1 : ∀ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (e1 ρ μG) ^ (T.card + 1)
          = (3 * c * e1 ρ μG) * (c * e1 ρ μG) ^ T.card := by
      intro T _
      rw [mul_pow, pow_add, pow_add]
      simp only [Nat.choose_one_right, Nat.cast_ofNat, pow_one]
      ring
    exact (Finset.sum_congr rfl hT1).trans
      ((Finset.mul_sum _ _ _).symm.trans (congrArg _ hBS))
  have hB1corr : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T = C.erase P then
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0))
      = 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hScard]
    rw [show (1 + 3 : ℕ) = 4 from rfl, hc4]
    simp only [Nat.choose_one_right, Nat.cast_ofNat]
  have hB1 : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T = C.erase P then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)))
      = (3 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB1base, hB1corr]
  have hB2base : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card))
      = (3 * c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    have hT2 : ∀ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card)
          = (3 * c ^ 2 * realMoment ρ μG 2)
            * (c * e1 ρ μG) ^ T.card := by
      intro T _
      rw [mul_pow, pow_add]
      simp only [show Nat.choose 3 2 = 3 from rfl, Nat.cast_ofNat]
      ring
    exact (Finset.sum_congr rfl hT2).trans
      ((Finset.mul_sum _ _ _).symm.trans (congrArg _ hBS))
  have hB2corr : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T = C.erase P then
              (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
      = -(3 * (((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hScard]
    rw [show (2 + 3 : ℕ) = 5 from rfl, hc5]
    simp only [show Nat.choose 3 2 = 3 from rfl, Nat.cast_ofNat]
    ring
  have hB2 : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)))
      = (3 * c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB2base, hB2corr]
    simp only [sub_eq_add_neg]
    ring
  have hB3base : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
          * (realMoment ρ μG 3 * (e1 ρ μG) ^ T.card))
      = (c ^ 3 * realMoment ρ μG 3)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    have hT3 : ∀ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
            * (realMoment ρ μG 3 * (e1 ρ μG) ^ T.card)
          = (c ^ 3 * realMoment ρ μG 3)
            * (c * e1 ρ μG) ^ T.card := by
      intro T _
      rw [mul_pow, pow_add]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
      ring
    exact (Finset.sum_congr rfl hT3).trans
      ((Finset.mul_sum _ _ _).symm.trans (congrArg _ hBS))
  have hB3corr : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
          * (if T = C.erase P then
              (tripledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
             else 0))
      = ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hScard, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show (3 + 3 : ℕ) = 6 from rfl, hc6]
  have hB3 : (∑ T ∈ (C.erase P).powerset,
        ((3 : ℕ).choose 3 : ℝ) * c ^ (3 + T.card)
          * (realMoment ρ μG 3 * (e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (tripledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
               else 0)))
      = (c ^ 3 * realMoment ρ μG 3)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB3base, hB3corr]
  have hA3 : densMomentValue ρ μG 3
      = 1 + 3 * c * (e1 ρ μG) + 3 * c ^ 2 * realMoment ρ μG 2
        + c ^ 3 * realMoment ρ μG 3 := by
    have h3 : densMomentValue ρ μG 3
        = 1 - 3 * (e1 ρ μG) * ((d : ℝ)⁻¹)
          + 3 * realMoment ρ μG 2 * ((d : ℝ)⁻¹) ^ 2
          - realMoment ρ μG 3 * ((d : ℝ)⁻¹) ^ 3 := by
      unfold densMomentValue
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      simp only [Nat.choose_self, Nat.choose_one_right, pow_zero,
        pow_one, Nat.cast_ofNat, Nat.cast_one]
      rw [show Nat.choose 3 0 = 1 from rfl,
        show Nat.choose 3 2 = 3 from rfl, realMoment_zero,
        realMoment_one]
      simp only [Nat.cast_ofNat]
      ring
    rw [h3, hc]
    ring
  have hI : ∀ j ∈ Finset.range 4,
      Integrable (fun α : LayerSite N → G =>
        ∑ T ∈ (C.erase P).powerset,
          ((((3 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j)
            * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        (Measure.pi fun _ : LayerSite N => μG) :=
    fun j hj => integrable_finsetSum _ (fun T hT =>
      hIntTerm j hj T hT)
  have hI0 := hI 0 (by decide)
  have hI1 := hI 1 (by decide)
  have hI2 := hI 2 (by decide)
  have hI3 := hI 3 (by decide)
  calc ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 3 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ((∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                * (colRe ρ u u' P α) ^ 0)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
          + (∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                * (colRe ρ u u' P α) ^ 1)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
          + (∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                * (colRe ρ u u' P α) ^ 2)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
          + (∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
                * (colRe ρ u u' P α) ^ 3)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt4)
    _ = ((∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                * (colRe ρ u u' P α) ^ 0)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        + ∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                * (colRe ρ u u' P α) ^ 1)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        + ∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                * (colRe ρ u u' P α) ^ 2)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        + ∫ α : LayerSite N → G,
          ∑ T ∈ (C.erase P).powerset,
            ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
                * (colRe ρ u u' P α) ^ 3)
              * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
        have h01 : (∫ α : LayerSite N → G,
              (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                    * (colRe ρ u u' P α) ^ 0)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                    * (colRe ρ u u' P α) ^ 1)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              ∂(Measure.pi fun _ : LayerSite N => μG))
            = (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                      * (colRe ρ u u' P α) ^ 0)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                      * (colRe ρ u u' P α) ^ 1)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)) :=
          integral_add hI0 hI1
        have h012 : (∫ α : LayerSite N → G,
              ((∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                    * (colRe ρ u u' P α) ^ 0)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                    * (colRe ρ u u' P α) ^ 1)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                    * (colRe ρ u u' P α) ^ 2)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              ∂(Measure.pi fun _ : LayerSite N => μG))
            = ((∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                      * (colRe ρ u u' P α) ^ 0)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                      * (colRe ρ u u' P α) ^ 1)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                      * (colRe ρ u u' P α) ^ 2)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)) := by
          have h := integral_add (hI0.add hI1) hI2
          simpa only [Pi.add_apply] using h.trans
            (congrArg₂ _ h01 rfl)
        have h0123 : (∫ α : LayerSite N → G,
              (((∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                    * (colRe ρ u u' P α) ^ 0)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                    * (colRe ρ u u' P α) ^ 1)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                    * (colRe ρ u u' P α) ^ 2)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)))
              + (∑ T ∈ (C.erase P).powerset,
                ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
                    * (colRe ρ u u' P α) ^ 3)
                  * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α))
              ∂(Measure.pi fun _ : LayerSite N => μG))
            = (((∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 0 : ℝ) * c ^ 0)
                      * (colRe ρ u u' P α) ^ 0)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 1 : ℝ) * c ^ 1)
                      * (colRe ρ u u' P α) ^ 1)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 2 : ℝ) * c ^ 2)
                      * (colRe ρ u u' P α) ^ 2)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)))
              + (∫ α : LayerSite N → G,
                ∑ T ∈ (C.erase P).powerset,
                  ((((3 : ℕ).choose 3 : ℝ) * c ^ 3)
                      * (colRe ρ u u' P α) ^ 3)
                    * (c ^ T.card * ∏ Q ∈ T, colRe ρ u u' Q α)
                ∂(Measure.pi fun _ : LayerSite N => μG)) := by
          have h := integral_add ((hI0.add hI1).add hI2) hI3
          simpa only [Pi.add_apply] using h.trans
            (congrArg₂ _ h012 rfl)
        exact h0123
    _ = ((1 - e1 ρ μG / (d : ℝ)) ^ 3
          + ((3 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)))
          + ((3 * c ^ 2 * realMoment ρ μG 2)
              * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
          + ((c ^ 3 * realMoment ρ μG 3)
              * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)) := by
        rw [integral_finsetSum _
            (fun T hT => hIntTerm 0 (by decide) T hT),
          integral_finsetSum _
            (fun T hT => hIntTerm 1 (by decide) T hT),
          integral_finsetSum _
            (fun T hT => hIntTerm 2 (by decide) T hT),
          integral_finsetSum _
            (fun T hT => hIntTerm 3 (by decide) T hT),
          Finset.sum_congr rfl (fun T hT => hval0 T hT),
          Finset.sum_congr rfl (fun T hT => hval1 T hT),
          Finset.sum_congr rfl (fun T hT => hval2 T hT),
          Finset.sum_congr rfl (fun T hT => hval3 T hT),
          hB0, hB1, hB2, hB3]
    _ = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
        rw [hA3]
        ring
/-- **The doubled-doubled pattern value.** For a
4-support `C` and distinct distinguished columns
`P, Q ∈ C`, the `(2,2,1,1)` pattern value splits
into its fully-split baseline `A₂²B²`, four times
the order-4 excess of the support at weight `d⁻⁴`,
minus twice each doubled excess at weight `d⁻⁵`,
and the doubled-doubled excess at weight `d⁻⁶` —
the baseline-subtracted doubled-doubled term is
exactly a summand of B6-2a's
`kappa6chan2211Excess`. Proved by the three-level
subset expansion: `x_P²` and `x_Q²` by `add_pow`
over `range 3`, the remaining two densities by the
powerset expansion; a character term factors unless
both doubled columns appear and the full rest
support is present, where the four moment objects
of the pattern occur. -/
theorem integral_colDens_prod_quadruple_doubled_doubled
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P Q : LayerColumn N) (hP : P ∈ C)
    (hQ : Q ∈ C) (hQP : Q ≠ P) :
    ∫ α : LayerSite N → G,
        ∏ Z ∈ C, (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hScard : ((C.erase P).erase Q).card = 2 := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hQP, hQ⟩),
      Finset.card_erase_of_mem hP, hC]
  have hQmem : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQ⟩
  have hPmem : P ∈ C.erase Q :=
    Finset.mem_erase.mpr ⟨Ne.symm hQP, hP⟩
  have hnotP : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hcomm : (C.erase P).erase Q = (C.erase Q).erase P := by
    ext R
    simp only [Finset.mem_erase]
    tauto
  have hPS : ∀ R ∈ (C.erase P).erase Q, R ≠ P ∧ R ≠ Q := by
    intro R hR
    exact ⟨(Finset.mem_erase.mp
      (Finset.mem_erase.mp hR).2).1,
      (Finset.mem_erase.mp hR).1⟩
  have hV : ∀ j ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
      ∀ T ∈ ((C.erase P).erase Q).powerset,
      ∫ α : LayerSite N → G,
          ((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ l)
            * ∏ Z ∈ T, colRe ρ u u' Z α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG j * realMoment ρ μG l * (e1 ρ μG) ^ T.card
          + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0)
          + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
              (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0)
          + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
              (doubledQuadReMoment ρ μG C Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0)
          + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
              (doubledDoubledQuadReMoment ρ μG C P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
             else 0) := by
    intro j hj l hl T hT
    have hj2 : j ≤ 2 := by
      have := Finset.mem_range.mp hj
      omega
    have hl2 : l ≤ 2 := by
      have := Finset.mem_range.mp hl
      omega
    have hsub : T ⊆ (C.erase P).erase Q :=
      Finset.mem_powerset.mp hT
    have hPT : P ∉ T := fun h =>
      hnotP (Finset.mem_erase.mp (hsub h)).2
    have hQT : Q ∉ T := fun h =>
      (Finset.mem_erase.mp (hsub h)).1 rfl
    have hQS : Q ∉ (C.erase P).erase Q :=
      fun h => (Finset.mem_erase.mp h).1 rfl
    have hPQS : P ∉ insert Q ((C.erase P).erase Q) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hQP h.symm
      · exact hnotP (Finset.mem_erase.mp h).2
    by_cases hTS : T = (C.erase P).erase Q
    · subst hTS
      by_cases hj0 : j = 0
      · subst hj0
        have hInt : ∫ α : LayerSite N → G,
              ((colRe ρ u u' P α) ^ 0 * (colRe ρ u u' Q α) ^ l)
                * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
              ∂(Measure.pi fun _ : LayerSite N => μG)
            = realMoment ρ μG l
              * (e1 ρ μG) ^ ((C.erase P).erase Q).card := by
          have hpt : ∀ α : LayerSite N → G,
              ((colRe ρ u u' P α) ^ 0 * (colRe ρ u u' Q α) ^ l)
                  * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
              = ∏ Z ∈ insert Q ((C.erase P).erase Q),
                  (colRe ρ u u' Z α) ^ (if Z = Q then l else 1) := by
            intro α
            rw [Finset.prod_insert hQS]
            have e2 : ∀ Z ∈ (C.erase P).erase Q,
                (colRe ρ u u' Z α) ^ (if Z = Q then l else 1)
                = colRe ρ u u' Z α :=
              fun Z hZ => by
                rw [if_neg (hPS Z hZ).2, pow_one]
            rw [Finset.prod_congr rfl e2, if_pos rfl]
            simp only [pow_zero, one_mul]
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
            integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
              hρcont u u' (insert Q ((C.erase P).erase Q)) (by
                rw [Finset.card_insert_of_notMem hQS, hScard]) _,
            Finset.prod_insert hQS, if_pos rfl]
          have hprod1 : (∏ Z ∈ (C.erase P).erase Q,
                realMoment ρ μG (if Z = Q then l else 1))
              = ∏ _Z ∈ (C.erase P).erase Q, realMoment ρ μG 1 :=
            Finset.prod_congr rfl fun Z hZ => by
              rw [if_neg (hPS Z hZ).2]
          rw [hprod1]
          simp only [realMoment_one, Finset.prod_const]
        rw [hInt, if_neg (fun h => absurd h.2.1 (by decide)),
          if_neg (fun h => absurd h.2.1 (by decide)),
          if_neg (fun h => absurd h.2.1 (by decide)),
          if_neg (fun h => absurd h.2.1 (by decide)),
          realMoment_zero]
        ring
      · by_cases hl0 : l = 0
        · subst hl0
          have hInt : ∫ α : LayerSite N → G,
                ((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ 0)
                  * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                ∂(Measure.pi fun _ : LayerSite N => μG)
              = realMoment ρ μG j
                * (e1 ρ μG) ^ ((C.erase P).erase Q).card := by
            have hpt : ∀ α : LayerSite N → G,
                ((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ 0)
                    * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                = ∏ Z ∈ insert P ((C.erase P).erase Q),
                    (colRe ρ u u' Z α) ^ (if Z = P then j else 1) := by
              intro α
              rw [Finset.prod_insert hPT]
              have e2 : ∀ Z ∈ (C.erase P).erase Q,
                  (colRe ρ u u' Z α) ^ (if Z = P then j else 1)
                  = colRe ρ u u' Z α :=
                fun Z hZ => by
                  rw [if_neg (hPS Z hZ).1, pow_one]
              rw [Finset.prod_congr rfl e2, if_pos rfl]
              simp only [pow_zero, mul_one]
            rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
              integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
                hρcont u u' (insert P ((C.erase P).erase Q)) (by
                  rw [Finset.card_insert_of_notMem hPT, hScard]) _,
              Finset.prod_insert hPT, if_pos rfl]
            have hprod1 : (∏ Z ∈ (C.erase P).erase Q,
                  realMoment ρ μG (if Z = P then j else 1))
                = ∏ _Z ∈ (C.erase P).erase Q, realMoment ρ μG 1 :=
              Finset.prod_congr rfl fun Z hZ => by
                rw [if_neg (hPS Z hZ).1]
            rw [hprod1]
            simp only [realMoment_one, Finset.prod_const]
          rw [hInt, if_neg (fun h => absurd h.2.2 (by decide)),
            if_neg (fun h => absurd h.2.2 (by decide)),
            if_neg (fun h => absurd h.2.2 (by decide)),
            if_neg (fun h => absurd h.2.2 (by decide)),
            realMoment_zero]
          ring
        · have hj1 : 1 ≤ j := by omega
          have hl1 : 1 ≤ l := by omega
          interval_cases j <;> interval_cases l
          · -- (1,1): the all-distinct moment of `C`.
            have hInt : ∫ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 1 * (colRe ρ u u' Q α) ^ 1)
                    * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                  ∂(Measure.pi fun _ : LayerSite N => μG)
                = quadReMoment ρ μG C u u' := by
              have hpt : ∀ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 1 * (colRe ρ u u' Q α) ^ 1)
                      * ∏ Z ∈ (C.erase P).erase Q,
                        colRe ρ u u' Z α
                  = ∏ Z ∈ C, colRe ρ u u' Z α := by
                intro α
                rw [← Finset.mul_prod_erase C
                  (fun Z => colRe ρ u u' Z α) hP,
                  ← Finset.mul_prod_erase (C.erase P)
                  (fun Z => colRe ρ u u' Z α) hQmem]
                simp only [pow_one]
                ring
              exact integral_congr_ae
                (Filter.Eventually.of_forall hpt)
            rw [hInt, if_pos ⟨rfl, rfl, rfl⟩,
              if_neg (fun h => absurd h.2.1 (by decide)),
              if_neg (fun h => absurd h.2.2 (by decide)),
              if_neg (fun h => absurd h.2.1 (by decide)),
              realMoment_one, hScard]
            ring
          · -- (1,2): the doubled moment at `Q`.
            have hInt : ∫ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 1 * (colRe ρ u u' Q α) ^ 2)
                    * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                  ∂(Measure.pi fun _ : LayerSite N => μG)
                = doubledQuadReMoment ρ μG C Q u u' := by
              have hpt : ∀ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 1 * (colRe ρ u u' Q α) ^ 2)
                      * ∏ Z ∈ (C.erase P).erase Q,
                        colRe ρ u u' Z α
                  = (colRe ρ u u' Q α) ^ 2
                    * ∏ Z ∈ C.erase Q, colRe ρ u u' Z α := by
                intro α
                have hprod : ∏ Z ∈ C.erase Q, colRe ρ u u' Z α
                    = colRe ρ u u' P α
                      * ∏ Z ∈ (C.erase P).erase Q,
                        colRe ρ u u' Z α := by
                  rw [← Finset.mul_prod_erase (C.erase Q)
                    (fun Z => colRe ρ u u' Z α) hPmem, ← hcomm]
                rw [hprod]
                simp only [pow_one]
                ring
              exact integral_congr_ae
                (Filter.Eventually.of_forall hpt)
            rw [hInt, if_neg (fun h => absurd h.2.2 (by decide)),
              if_neg (fun h => absurd h.2.1 (by decide)),
              if_pos ⟨rfl, rfl, rfl⟩,
              if_neg (fun h => absurd h.2.1 (by decide)),
              realMoment_one, hScard]
            ring
          · -- (2,1): the doubled moment at `P`.
            have hInt : ∫ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 1)
                    * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                  ∂(Measure.pi fun _ : LayerSite N => μG)
                = doubledQuadReMoment ρ μG C P u u' := by
              have hpt : ∀ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 1)
                      * ∏ Z ∈ (C.erase P).erase Q,
                        colRe ρ u u' Z α
                  = (colRe ρ u u' P α) ^ 2
                    * ∏ Z ∈ C.erase P, colRe ρ u u' Z α := by
                intro α
                rw [← Finset.mul_prod_erase (C.erase P)
                  (fun Z => colRe ρ u u' Z α) hQmem]
                simp only [pow_one]
                ring
              exact integral_congr_ae
                (Filter.Eventually.of_forall hpt)
            rw [hInt, if_neg (fun h => absurd h.2.1 (by decide)),
              if_pos ⟨rfl, rfl, rfl⟩,
              if_neg (fun h => absurd h.2.1 (by decide)),
              if_neg (fun h => absurd h.2.2 (by decide)),
              realMoment_one, hScard]
            ring
          · -- (2,2): the doubled-doubled moment, by definition.
            have hInt : ∫ α : LayerSite N → G,
                  ((colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2)
                    * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
                  ∂(Measure.pi fun _ : LayerSite N => μG)
                = doubledDoubledQuadReMoment ρ μG C P Q u u' :=
              rfl
            rw [hInt, if_neg (fun h => absurd h.2.1 (by decide)),
              if_neg (fun h => absurd h.2.2 (by decide)),
              if_neg (fun h => absurd h.2.1 (by decide)),
              if_pos ⟨rfl, rfl, rfl⟩, hScard]
            ring
    · -- `T` is a proper subset of the rest support: the
      -- character term factors on at most three columns.
      have hcardT : T.card ≤ 1 := by
        have h1 : T.card ≤ 2 := le_trans (Finset.card_le_card hsub)
          (le_of_eq hScard)
        have hne2 : T.card ≠ 2 := fun h2 => hTS
          (Finset.eq_of_subset_of_card_le hsub
            (by rw [hScard]; omega))
        omega
      have hPnot : P ∉ insert Q T := by
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hQP h.symm
        · exact hPT h
      have hcongDD : ∀ α : LayerSite N → G,
          ((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ l)
              * ∏ Z ∈ T, colRe ρ u u' Z α
          = ∏ Z ∈ insert P (insert Q T),
              (colRe ρ u u' Z α)
                ^ (if Z = P then j else if Z = Q then l else 1) := by
        intro α
        rw [Finset.prod_insert hPnot, Finset.prod_insert hQT,
          if_pos rfl, if_neg hQP, if_pos rfl]
        have hprod1 : (∏ Z ∈ T,
              (colRe ρ u u' Z α)
                ^ (if Z = P then j else if Z = Q then l else 1))
            = ∏ Z ∈ T, colRe ρ u u' Z α :=
          Finset.prod_congr rfl fun Z hZ => by
            rw [if_neg (hPS Z (hsub hZ)).1,
              if_neg (hPS Z (hsub hZ)).2, pow_one]
        rw [hprod1]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hcongDD),
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' (insert P (insert Q T)) (by
            rw [Finset.card_insert_of_notMem hPnot,
              Finset.card_insert_of_notMem hQT]
            omega) _,
        Finset.prod_insert hPnot, Finset.prod_insert hQT,
        if_pos rfl, if_neg hQP, if_pos rfl]
      have hprod1 : (∏ Z ∈ T,
            realMoment ρ μG
              (if Z = P then j else if Z = Q then l else 1))
          = ∏ _Z ∈ T, realMoment ρ μG 1 :=
        Finset.prod_congr rfl fun Z hZ => by
          rw [if_neg (hPS Z (hsub hZ)).1,
            if_neg (hPS Z (hsub hZ)).2]
      rw [hprod1,
        if_neg (fun h => hTS h.1), if_neg (fun h => hTS h.1),
        if_neg (fun h => hTS h.1), if_neg (fun h => hTS h.1)]
      simp only [realMoment_one, Finset.prod_const]
      ring
  have hfactor : ∀ (j l : ℕ) (T : Finset (LayerColumn N))
      (hT : T ∈ ((C.erase P).erase Q).powerset)
      (α : LayerSite N → G),
      ((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ l)
          * ∏ Z ∈ T, colRe ρ u u' Z α
      = ∏ Z ∈ insert P (insert Q T),
          (colRe ρ u u' Z α)
            ^ (if Z = P then j else if Z = Q then l else 1) := by
    intro j l T hT α
    have hsub : T ⊆ (C.erase P).erase Q :=
      Finset.mem_powerset.mp hT
    have hPT' : P ∉ T := fun h =>
      hnotP (Finset.mem_erase.mp (hsub h)).2
    have hQT' : Q ∉ T := fun h =>
      (Finset.mem_erase.mp (hsub h)).1 rfl
    have hPnot : P ∉ insert Q T := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hQP h.symm
      · exact hPT' h
    rw [Finset.prod_insert hPnot, Finset.prod_insert hQT',
      if_pos rfl, if_neg hQP, if_pos rfl]
    have hprod1 : (∏ Z ∈ T, (colRe ρ u u' Z α)
          ^ (if Z = P then j else if Z = Q then l else 1))
        = ∏ Z ∈ T, colRe ρ u u' Z α :=
      Finset.prod_congr rfl fun Z hZ => by
        rw [if_neg (hPS Z (hsub hZ)).1,
          if_neg (hPS Z (hsub hZ)).2, pow_one]
    rw [hprod1]
    ring
  have hcong2 : ∀ (j l : ℕ) (T : Finset (LayerColumn N))
      (α : LayerSite N → G),
      ((((2 : ℕ).choose j : ℝ) * c ^ j) * (colRe ρ u u' P α) ^ j
          * (((2 : ℕ).choose l : ℝ) * c ^ l)
            * (colRe ρ u u' Q α) ^ l)
        * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α)
      = (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
          * c ^ (j + l + T.card)
        * (((colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ l)
          * ∏ Z ∈ T, colRe ρ u u' Z α) := by
    intro j l T α
    rw [pow_add, pow_add]
    ring
  have hIntDD : ∀ j ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
      ∀ T ∈ ((C.erase P).erase Q).powerset,
      Integrable (fun α : LayerSite N → G =>
        ((((2 : ℕ).choose j : ℝ) * c ^ j) * (colRe ρ u u' P α) ^ j
            * (((2 : ℕ).choose l : ℝ) * c ^ l)
              * (colRe ρ u u' Q α) ^ l)
          * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro j _hj l _hl T hT
    refine Integrable.congr
      ((integrable_colRe_prod_pow ρ μG hρcont u u'
        (insert P (insert Q T))
        (fun Z => if Z = P then j else if Z = Q then l else 1)).const_mul
        ((((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
          * c ^ (j + l + T.card))) ?_
    exact Filter.Eventually.of_forall fun α =>
      (congrArg (fun y : ℝ =>
        ((((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
          * c ^ (j + l + T.card)) * y)
        (hfactor j l T hT α).symm).trans (hcong2 j l T α).symm
  have hval : ∀ j ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
      ∀ T ∈ ((C.erase P).erase Q).powerset,
      ∫ α : LayerSite N → G,
          ((((2 : ℕ).choose j : ℝ) * c ^ j) * (colRe ρ u u' P α) ^ j
              * (((2 : ℕ).choose l : ℝ) * c ^ l)
                * (colRe ρ u u' Q α) ^ l)
            * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (realMoment ρ μG j * realMoment ρ μG l
              * (e1 ρ μG) ^ T.card
            + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
                (doubledQuadReMoment ρ μG C Q u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
                (doubledDoubledQuadReMoment ρ μG C P Q u u'
                  - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
               else 0)) := by
    intro j hj l hl T hT
    rw [integral_congr_ae
        (Filter.Eventually.of_forall (hcong2 j l T)),
      integral_const_mul, hV j hj l hl T hT]
  have hx : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      colDensC ρ u u' Z α = c * colRe ρ u u' Z α + 1 := by
    intro Z α
    rw [colDensC_eq, div_eq_inv_mul]
    ring
  have hxP2 : ∀ α : LayerSite N → G,
      (colDensC ρ u u' P α) ^ 2
        = ∑ j ∈ Finset.range 3,
            (((2 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j := by
    intro α
    rw [hx P α, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, one_pow, mul_one]
    ring
  have hxQ2 : ∀ α : LayerSite N → G,
      (colDensC ρ u u' Q α) ^ 2
        = ∑ l ∈ Finset.range 3,
            (((2 : ℕ).choose l : ℝ) * c ^ l)
              * (colRe ρ u u' Q α) ^ l := by
    intro α
    rw [hx Q α, add_pow]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, one_pow, mul_one]
    ring
  have hptS : ∀ α : LayerSite N → G,
      ∏ Z ∈ (C.erase P).erase Q, colDensC ρ u u' Z α
        = ∑ T ∈ ((C.erase P).erase Q).powerset, c ^ T.card
            * ∏ Z ∈ T, colRe ρ u u' Z α := by
    intro α
    have h1 : ∏ Z ∈ (C.erase P).erase Q, colDensC ρ u u' Z α
        = ∏ Z ∈ (C.erase P).erase Q, (c * colRe ρ u u' Z α + 1) :=
      Finset.prod_congr rfl fun Z _ => hx Z α
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const]
  have h0 : ∀ α : LayerSite N → G,
      ∏ Z ∈ C, (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1)
        = ((colDensC ρ u u' P α) ^ 2 * (colDensC ρ u u' Q α) ^ 2)
          * ∏ Z ∈ (C.erase P).erase Q, colDensC ρ u u' Z α := by
    intro α
    rw [← Finset.mul_prod_erase C
        (fun Z => (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1)) hP,
      ← Finset.mul_prod_erase (C.erase P)
        (fun Z => (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1)) hQmem,
      if_pos rfl, if_neg hQP, if_pos rfl]
    have eS : (∏ Z ∈ (C.erase P).erase Q, (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1))
        = ∏ Z ∈ (C.erase P).erase Q, colDensC ρ u u' Z α :=
      Finset.prod_congr rfl fun Z hZ => by
        rw [if_neg (hPS Z hZ).1, if_neg (hPS Z hZ).2, pow_one]
    rw [eS]
    ring
  have hpe : ∀ α : LayerSite N → G,
      ((colDensC ρ u u' P α) ^ 2 * (colDensC ρ u u' Q α) ^ 2)
          * ∏ Z ∈ (C.erase P).erase Q, colDensC ρ u u' Z α
        = ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
            ∑ T ∈ ((C.erase P).erase Q).powerset,
              ((((2 : ℕ).choose j : ℝ) * c ^ j)
                  * (colRe ρ u u' P α) ^ j
                * (((2 : ℕ).choose l : ℝ) * c ^ l)
                  * (colRe ρ u u' Q α) ^ l)
              * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α) := by
    intro α
    have hsm : ((∑ j ∈ Finset.range 3,
          (((2 : ℕ).choose j : ℝ) * c ^ j)
            * (colRe ρ u u' P α) ^ j)
        * (∑ l ∈ Finset.range 3,
          (((2 : ℕ).choose l : ℝ) * c ^ l)
            * (colRe ρ u u' Q α) ^ l))
      = ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ((((2 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j)
            * ((((2 : ℕ).choose l : ℝ) * c ^ l)
              * (colRe ρ u u' Q α) ^ l) :=
      Finset.sum_mul_sum (Finset.range 3) (Finset.range 3)
        (fun j => (((2 : ℕ).choose j : ℝ) * c ^ j)
          * (colRe ρ u u' P α) ^ j)
        (fun l => (((2 : ℕ).choose l : ℝ) * c ^ l)
          * (colRe ρ u u' Q α) ^ l)
    have hsm1 : ((∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ((((2 : ℕ).choose j : ℝ) * c ^ j)
              * (colRe ρ u u' P α) ^ j)
            * ((((2 : ℕ).choose l : ℝ) * c ^ l)
              * (colRe ρ u u' Q α) ^ l))
        * (∑ T ∈ ((C.erase P).erase Q).powerset, c ^ T.card
            * ∏ Z ∈ T, colRe ρ u u' Z α))
      = ∑ j ∈ Finset.range 3,
          ((∑ l ∈ Finset.range 3,
            ((((2 : ℕ).choose j : ℝ) * c ^ j)
                * (colRe ρ u u' P α) ^ j)
              * ((((2 : ℕ).choose l : ℝ) * c ^ l)
                * (colRe ρ u u' Q α) ^ l))
          * (∑ T ∈ ((C.erase P).erase Q).powerset, c ^ T.card
              * ∏ Z ∈ T, colRe ρ u u' Z α)) :=
      Finset.sum_mul _ _ _
    have hsm2 : ∀ j : ℕ,
        ((∑ l ∈ Finset.range 3,
            ((((2 : ℕ).choose j : ℝ) * c ^ j)
                * (colRe ρ u u' P α) ^ j)
              * ((((2 : ℕ).choose l : ℝ) * c ^ l)
                * (colRe ρ u u' Q α) ^ l))
          * (∑ T ∈ ((C.erase P).erase Q).powerset, c ^ T.card
              * ∏ Z ∈ T, colRe ρ u u' Z α))
      = ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
            ((((2 : ℕ).choose j : ℝ) * c ^ j)
                * (colRe ρ u u' P α) ^ j)
              * ((((2 : ℕ).choose l : ℝ) * c ^ l)
                * (colRe ρ u u' Q α) ^ l)
            * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α) :=
      fun j => Finset.sum_mul_sum (Finset.range 3)
        ((C.erase P).erase Q).powerset
        (fun l => ((((2 : ℕ).choose j : ℝ) * c ^ j)
            * (colRe ρ u u' P α) ^ j)
          * ((((2 : ℕ).choose l : ℝ) * c ^ l)
            * (colRe ρ u u' Q α) ^ l))
        (fun T => c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α)
    rw [hxP2 α, hxQ2 α, hptS α, hsm, hsm1]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hsm2 j).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hBS2 : ∑ T ∈ ((C.erase P).erase Q).powerset,
        (c * e1 ρ μG) ^ T.card
      = (1 - e1 ρ μG / (d : ℝ)) ^ 2 := by
    have h2 : (∑ j ∈ Finset.range (2 + 1),
          ((2 : ℕ).choose j : ℝ) * (c * e1 ρ μG) ^ j)
        = (1 + c * e1 ρ μG) ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      simp only [show (2 : ℕ).choose 0 = 1 from rfl,
        show (2 : ℕ).choose 1 = 2 from rfl,
        show (2 : ℕ).choose 2 = 1 from rfl, Nat.cast_one,
        Nat.cast_ofNat, pow_zero, pow_one, mul_one, one_mul,
        add_zero, zero_add]
      ring
    rw [Finset.sum_powerset_apply_card]
    simp only [nsmul_eq_mul, hScard]
    rw [h2, hc, div_eq_inv_mul]
    ring
  have hA2sum : (∑ j ∈ Finset.range 3,
        ((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
      = densMomentValue ρ μG 2 := by
    have e : ∀ j : ℕ, ((2 : ℕ).choose j : ℝ) * c ^ j
          * realMoment ρ μG j
        = ((2 : ℕ).choose j : ℝ) * (-(d : ℝ)⁻¹) ^ j
          * realMoment ρ μG j := by
      intro j
      rw [hc]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    rfl
  have htermid : ∀ (j l : ℕ) (T : Finset (LayerColumn N)),
      (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
          * c ^ (j + l + T.card)
        * (realMoment ρ μG j * realMoment ρ μG l
          * (e1 ρ μG) ^ T.card)
      = (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
        * ((((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
          * (c * e1 ρ μG) ^ T.card) := by
    intro j l T
    rw [mul_pow, pow_add, pow_add]
    ring
  have hTsum : ∀ j l : ℕ,
      ∑ T ∈ ((C.erase P).erase Q).powerset,
        (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
          * ((((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
            * (c * e1 ρ μG) ^ T.card)
      = (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
        * ((((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2) := by
    intro j l
    rw [← Finset.mul_sum, ← Finset.mul_sum, hBS2]
  have hLsum : ∀ j : ℕ,
      ∑ l ∈ Finset.range 3,
        (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
          * ((((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
      = (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
        * ((∑ l ∈ Finset.range 3,
            ((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2) := by
    intro j
    rw [← Finset.mul_sum]
    refine congrArg _ ?_
    exact (Finset.sum_mul _ _ _).symm
  have hBase : ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (realMoment ρ μG j * realMoment ρ μG l
              * (e1 ρ μG) ^ T.card)
      = (∑ j ∈ Finset.range 3,
          ((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
        * ((∑ l ∈ Finset.range 3,
            ((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2) := by
    calc ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                * c ^ (j + l + T.card)
              * (realMoment ρ μG j * realMoment ρ μG l
                * (e1 ρ μG) ^ T.card)
        = ∑ j ∈ Finset.range 3,
            (((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
              * ((∑ l ∈ Finset.range 3,
                  ((2 : ℕ).choose l : ℝ) * c ^ l
                    * realMoment ρ μG l)
                * (1 - e1 ρ μG / (d : ℝ)) ^ 2) :=
          Finset.sum_congr rfl fun j _ =>
            (Finset.sum_congr rfl fun l _ =>
              (Finset.sum_congr rfl fun T _ =>
                htermid j l T).trans (hTsum j l)).trans (hLsum j)
      _ = (∑ j ∈ Finset.range 3,
            ((2 : ℕ).choose j : ℝ) * c ^ j * realMoment ρ μG j)
          * ((∑ l ∈ Finset.range 3,
              ((2 : ℕ).choose l : ℝ) * c ^ l * realMoment ρ μG l)
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2) :=
          (Finset.sum_mul _ _ _).symm
  have hCorrGen : ∀ (a b : ℕ) (ha : a ∈ Finset.range 3)
      (hb : b ∈ Finset.range 3) (X : ℝ),
      ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = a ∧ l = b then X
               else 0)
        = (((2 : ℕ).choose a : ℝ) * ((2 : ℕ).choose b : ℝ))
          * c ^ (a + b + ((C.erase P).erase Q).card) * X := by
    intro a b ha hb X
    have hstep1 : ∀ j ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = a ∧ l = b then X
               else 0)
        = if j = a ∧ l = b then
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + ((C.erase P).erase Q).card) * X
          else 0 := by
      intro j _ l _
      have hterm : ∀ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = a ∧ l = b then X
               else 0)
          = if T = (C.erase P).erase Q then
              (if j = a ∧ l = b then
                (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                  * c ^ (j + l + T.card) * X
               else 0)
            else 0 := by
        intro T _
        by_cases hT : T = (C.erase P).erase Q <;>
          by_cases hR : (j = a ∧ l = b) <;> simp [hT, hR]
      calc ∑ T ∈ ((C.erase P).erase Q).powerset,
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                * c ^ (j + l + T.card)
              * (if T = (C.erase P).erase Q ∧ j = a ∧ l = b then X
                 else 0)
          = ∑ T ∈ ((C.erase P).erase Q).powerset,
              (if T = (C.erase P).erase Q then
                (if j = a ∧ l = b then
                  (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                    * c ^ (j + l + T.card) * X
                 else 0)
               else 0) :=
            Finset.sum_congr rfl hterm
        _ = if (C.erase P).erase Q
                ∈ ((C.erase P).erase Q).powerset then
              (if j = a ∧ l = b then
                (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                  * c ^ (j + l + ((C.erase P).erase Q).card) * X
               else 0)
            else 0 :=
            Finset.sum_ite_eq' _ _ _
        _ = if j = a ∧ l = b then
              (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                * c ^ (j + l + ((C.erase P).erase Q).card) * X
            else 0 := by
            rw [if_pos (Finset.mem_powerset.mpr
              (Finset.Subset.refl _))]
    have hstep2 : ∀ j ∈ Finset.range 3,
        ∑ l ∈ Finset.range 3,
          (if j = a ∧ l = b then
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + ((C.erase P).erase Q).card) * X
           else 0)
        = if j = a then
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose b : ℝ))
              * c ^ (j + b + ((C.erase P).erase Q).card) * X
          else 0 := by
      intro j _
      have hterm : ∀ l ∈ Finset.range 3,
          (if j = a ∧ l = b then
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + ((C.erase P).erase Q).card) * X
           else 0)
          = if l = b then
              (if j = a then
                (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
                  * c ^ (j + l + ((C.erase P).erase Q).card) * X
               else 0)
            else 0 := by
        intro l _
        by_cases hR : (j = a) <;> by_cases hL : l = b <;>
          simp [hR, hL]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _,
        if_pos hb]
    refine ((Finset.sum_congr rfl fun j hj =>
      (Finset.sum_congr rfl fun l hl => hstep1 j hj l hl)).trans
      (Finset.sum_congr rfl fun j hj => hstep2 j hj)).trans ?_
    rw [Finset.sum_ite_eq' _ _ _, if_pos ha]
  have hCorr1 : ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)
      = 4 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    refine (hCorrGen 1 1 (by decide) (by decide) _).trans ?_
    rw [hScard]
    simp only [show (2 : ℕ).choose 1 = 2 from rfl, Nat.cast_ofNat]
    rw [show (1 + 1 + 2 : ℕ) = 4 from rfl, hc4]
    ring
  have hCorr2 : ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
      = -(2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    refine (hCorrGen 2 1 (by decide) (by decide) _).trans ?_
    rw [hScard]
    simp only [show (2 : ℕ).choose 2 = 1 from rfl,
      show (2 : ℕ).choose 1 = 2 from rfl, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show (2 + 1 + 2 : ℕ) = 5 from rfl, hc5]
    ring
  have hCorr3 : ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
                (doubledQuadReMoment ρ μG C Q u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
      = -(2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    refine (hCorrGen 1 2 (by decide) (by decide) _).trans ?_
    rw [hScard]
    simp only [show (2 : ℕ).choose 2 = 1 from rfl,
      show (2 : ℕ).choose 1 = 2 from rfl, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show (1 + 2 + 2 : ℕ) = 5 from rfl, hc5]
    ring
  have hCorr4 : ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
                (doubledDoubledQuadReMoment ρ μG C P Q u u'
                  - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
               else 0)
      = ((d : ℝ)⁻¹) ^ 6
        * (doubledDoubledQuadReMoment ρ μG C P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    refine (hCorrGen 2 2 (by decide) (by decide) _).trans ?_
    rw [hScard]
    simp only [show (2 : ℕ).choose 2 = 1 from rfl, Nat.cast_one]
    rw [show (2 + 2 + 2 : ℕ) = 6 from rfl, hc6]
    ring
  have distrib3 : ∀ (F G : ℕ → ℕ → Finset (LayerColumn N) → ℝ),
      (∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset, (F j l T + G j l T))
      = (∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset, F j l T)
        + (∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset, G j l T) := by
    intro F G
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      Finset.sum_add_distrib
    refine (Finset.sum_congr rfl fun l _ => ?_).trans
      Finset.sum_add_distrib
    exact Finset.sum_add_distrib
  calc ∫ α : LayerSite N → G,
        ∏ Z ∈ C, (colDensC ρ u u' Z α)
          ^ (if Z = P then 2 else if Z = Q then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
            ∑ T ∈ ((C.erase P).erase Q).powerset,
              ((((2 : ℕ).choose j : ℝ) * c ^ j)
                  * (colRe ρ u u' P α) ^ j
                * (((2 : ℕ).choose l : ℝ) * c ^ l)
                  * (colRe ρ u u' Q α) ^ l)
              * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall fun α =>
          (h0 α).trans (hpe α))
    _ = ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          ∫ α : LayerSite N → G,
            ((((2 : ℕ).choose j : ℝ) * c ^ j)
                * (colRe ρ u u' P α) ^ j
              * (((2 : ℕ).choose l : ℝ) * c ^ l)
                * (colRe ρ u u' Q α) ^ l)
            * (c ^ T.card * ∏ Z ∈ T, colRe ρ u u' Z α)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
        rw [integral_finsetSum _ (fun j hj =>
          integrable_finsetSum _ fun l hl =>
            integrable_finsetSum _ fun T hT =>
              hIntDD j hj l hl T hT)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [integral_finsetSum _ (fun l hl =>
            integrable_finsetSum _ fun T hT =>
              hIntDD j hj l hl T hT)]
        refine Finset.sum_congr rfl fun l hl => ?_
        exact integral_finsetSum _ (fun T hT =>
          hIntDD j hj l hl T hT)
    _ = ∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (realMoment ρ μG j * realMoment ρ μG l
              * (e1 ρ μG) ^ T.card
            + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
                (doubledQuadReMoment ρ μG C Q u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
                (doubledDoubledQuadReMoment ρ μG C P Q u u'
                  - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
               else 0)) :=
        Finset.sum_congr rfl fun j hj =>
          Finset.sum_congr rfl fun l hl =>
            Finset.sum_congr rfl fun T hT => hval j hj l hl T hT
    _ = (∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (realMoment ρ μG j * realMoment ρ μG l
            * (e1 ρ μG) ^ T.card))
        + ((∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0))
        + ((∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
              (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
        + ((∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
              (doubledQuadReMoment ρ μG C Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
        + (∑ j ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
          ∑ T ∈ ((C.erase P).erase Q).powerset,
          (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
            * c ^ (j + l + T.card)
          * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
              (doubledDoubledQuadReMoment ρ μG C P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
             else 0))))) := by
        have hsplit : ∀ (j l : ℕ) (T : Finset (LayerColumn N)),
            (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
            * (realMoment ρ μG j * realMoment ρ μG l
                * (e1 ρ μG) ^ T.card
              + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
                  (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
                 else 0)
              + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
                  (doubledQuadReMoment ρ μG C P u u'
                    - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
                 else 0)
              + (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
                  (doubledQuadReMoment ρ μG C Q u u'
                    - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
                 else 0)
              + (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
                  (doubledDoubledQuadReMoment ρ μG C P Q u u'
                    - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
                 else 0))
          = (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
              * (realMoment ρ μG j * realMoment ρ μG l
                * (e1 ρ μG) ^ T.card)
            + ((((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
              * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 1 then
                  (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
                 else 0)
            + ((((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
              * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 1 then
                  (doubledQuadReMoment ρ μG C P u u'
                    - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
                 else 0)
            + ((((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
              * (if T = (C.erase P).erase Q ∧ j = 1 ∧ l = 2 then
                  (doubledQuadReMoment ρ μG C Q u u'
                    - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
                 else 0)
            + (((2 : ℕ).choose j : ℝ) * ((2 : ℕ).choose l : ℝ))
              * c ^ (j + l + T.card)
              * (if T = (C.erase P).erase Q ∧ j = 2 ∧ l = 2 then
                  (doubledDoubledQuadReMoment ρ μG C P Q u u'
                    - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
                 else 0)))) := by
          intro j l T
          ring
        rw [Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun l _ =>
            Finset.sum_congr rfl (fun T _ =>
              hsplit j l T)))]
        refine (distrib3 _ _).trans ?_
        refine congrArg _ ((distrib3 _ _).trans ?_)
        refine congrArg _ ((distrib3 _ _).trans ?_)
        exact congrArg _ (distrib3 _ _)
    _ = (densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C P Q u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
        rw [hBase, hCorr1, hCorr2, hCorr3, hCorr4, hA2sum]
        ring

set_option maxHeartbeats 1600000 in
/-- **The card-4 fiber.** Over a 4-support `C`, the
fiber of the sixth-power expansion is the patterns
`(3,1,1,1)` (multinomial `6!/3! = 120` per
distinguished column) and `(2,2,1,1)` (multinomial
`6!/(2!·2!) = 180` per distinct exponent function),
expressed through the two pattern values above. The
`(2,2,1,1)` part is summed over ordered pairs of
distinct columns at weight `90 = 180 / 2`: each
`(2,2,1,1)` exponent function is named by two
ordered pairs, and the doubled-doubled pattern
value is symmetric in its two distinguished
columns, so the ordered-pair sum at `90` is the
fiber's `180` per pattern function. Raw fiber
evaluation only: no total assembly, no
`kappa6dep` identity, no sign. -/
theorem fiber_card_four6 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ X ∈ C, (120 : ℝ)
          * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C X u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG C X u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        + ∑ X ∈ C, ∑ Y ∈ C.erase X, (90 : ℝ)
          * ((densMomentValue ρ μG 2) ^ 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + 4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C X u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C Y u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG C X Y u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
  classical
  obtain ⟨P, Q, R, S, hPQ, hPR, hPS, hQR, hQS, hRS, hCeq⟩ :=
    Finset.card_eq_four.mp hC
  have hnotP : P ∉ ({Q, R, S} : Finset (LayerColumn N)) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPR, hPS⟩
  have hnotQ : Q ∉ ({R, S} : Finset (LayerColumn N)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hQR, hQS⟩
  have hnotR : R ∉ ({S} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hRS
  have hPmem : P ∈ C := by
    rw [hCeq]
    exact Finset.mem_insert_self P _
  have hQmem : Q ∈ C := by
    rw [hCeq]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self Q _))
  have hRmem : R ∈ C := by
    rw [hCeq]
    exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self R _))))
  have hSmem : S ∈ C := by
    rw [hCeq]
    exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self S))))))
  set S6 : Finset (ℕ × ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 3 ×ˢ Finset.Icc 1 3 ×ˢ Finset.Icc 1 3
      ×ˢ Finset.Icc 1 3).filter
      (fun t => t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = 6) with hS6
  have htS : ∀ t ∈ S6, t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = 6
      ∧ t.1 ∈ Finset.Icc 1 3 ∧ t.2.1 ∈ Finset.Icc 1 3
      ∧ t.2.2.1 ∈ Finset.Icc 1 3 ∧ t.2.2.2 ∈ Finset.Icc 1 3 :=
    fun t ht =>
      ⟨(Finset.mem_filter.mp ht).2,
        (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
        (Finset.mem_product.mp
          (Finset.mem_product.mp
            (Finset.mem_filter.mp ht).1).2).1,
        (Finset.mem_product.mp
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).2).1,
        (Finset.mem_product.mp
          (Finset.mem_product.mp
            (Finset.mem_product.mp
              (Finset.mem_filter.mp ht).1).2).2).2⟩
  have hsumT : ∀ t ∈ S6,
      ∑ X ∈ Finset.univ, (fun X => if X = P then t.1
          else if X = Q then t.2.1
          else if X = R then t.2.2.1
          else if X = S then t.2.2.2 else 0) X = 6 := by
    intro t ht
    have htsum : t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = 6 :=
      (htS t ht).1
    have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp (htS t ht).2.1).1
    have ht2 : 1 ≤ t.2.1 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.1).1
    have ht3 : 1 ≤ t.2.2.1 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.2.1).1
    have ht4 : 1 ≤ t.2.2.2 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.2.2).1
    have h1 : ∀ X ∈ Finset.univ,
        (if X = P then t.1 else if X = Q then t.2.1
          else if X = R then t.2.2.1
          else if X = S then t.2.2.2 else 0)
          = if X ∈ C then
              (if X = P then t.1 else if X = Q then t.2.1
                else if X = R then t.2.2.1
                else if X = S then t.2.2.2 else 0)
            else 0 :=
      fun X _ => by
        by_cases hX : X ∈ C
        · rw [if_pos hX]
        · have hX0 : X ∉ C := hX
          rw [hCeq, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_singleton] at hX
          push_neg at hX
          rw [if_neg hX0, if_neg hX.1, if_neg hX.2.1,
            if_neg hX.2.2.1, if_neg hX.2.2.2]
    rw [Finset.sum_congr rfl h1,
      ← Finset.sum_subset (Finset.subset_univ C)
        (fun X _ hX => if_neg hX),
      hCeq, Finset.sum_insert hnotP, Finset.sum_insert hnotQ,
      Finset.sum_insert hnotR, Finset.sum_singleton]
    rw [if_pos (Finset.mem_insert_self P {Q, R, S}), if_pos rfl,
      if_pos (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self Q {R, S}))),
      if_neg (Ne.symm hPQ), if_pos rfl,
      if_pos (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert_self R {S}))))),
      if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl,
      if_pos (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton_self S))))))),
      if_neg (Ne.symm hPS), if_neg (Ne.symm hQS),
      if_neg (Ne.symm hRS), if_pos rfl]
    omega
  have hsuppT : ∀ t ∈ S6, multSupport
      (fun X => if X = P then t.1 else if X = Q then t.2.1
        else if X = R then t.2.2.1
        else if X = S then t.2.2.2 else 0) = C := by
    intro t ht
    have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp (htS t ht).2.1).1
    have ht2 : 1 ≤ t.2.1 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.1).1
    have ht3 : 1 ≤ t.2.2.1 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.2.1).1
    have ht4 : 1 ≤ t.2.2.2 :=
      (Finset.mem_Icc.mp (htS t ht).2.2.2.2).1
    refine Finset.ext fun X => ?_
    simp only [multSupport_eq_filter, Finset.mem_filter,
      Finset.mem_univ, true_and, hCeq, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hXP : X = P
    · rw [hXP]
      simp [show t.1 ≠ 0 by omega]
    · by_cases hXQ : X = Q
      · rw [hXQ]
        simp [hXP, Ne.symm hPQ, show t.2.1 ≠ 0 by omega]
      · by_cases hXR : X = R
        · rw [hXR]
          simp [hXP, hXQ, Ne.symm hPR, Ne.symm hQR,
            show t.2.2.1 ≠ 0 by omega]
        · by_cases hXS : X = S
          · rw [hXS]
            simp [hXP, hXQ, hXR, Ne.symm hPS, Ne.symm hQS,
              Ne.symm hRS, show t.2.2.2 ≠ 0 by omega]
          · simp [hXP, hXQ, hXR, hXS]
  have hfactT : ∀ t ∈ S6,
      ∏ X ∈ Finset.univ, Nat.factorial
          ((fun X => if X = P then t.1 else if X = Q then t.2.1
            else if X = R then t.2.2.1
            else if X = S then t.2.2.2 else 0) X)
        = Nat.factorial t.1 * Nat.factorial t.2.1
          * Nat.factorial t.2.2.1 * Nat.factorial t.2.2.2 := by
    intro t ht
    have h1 : ∏ X ∈ Finset.univ, Nat.factorial
            ((fun X => if X = P then t.1 else if X = Q then t.2.1
              else if X = R then t.2.2.1
              else if X = S then t.2.2.2 else 0) X)
        = ∏ X ∈ C, Nat.factorial
            ((fun X => if X = P then t.1 else if X = Q then t.2.1
              else if X = R then t.2.2.1
              else if X = S then t.2.2.2 else 0) X) :=
      (Finset.prod_subset (Finset.subset_univ C)
        (fun X _ hX => by
          rw [hCeq, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_singleton] at hX
          push_neg at hX
          simp [hX.1, hX.2.1, hX.2.2.1, hX.2.2.2])).symm
    rw [h1, hCeq, Finset.prod_insert hnotP,
      Finset.prod_insert hnotQ, Finset.prod_insert hnotR,
      Finset.prod_singleton]
    show Nat.factorial (if P = P then t.1
          else if P = Q then t.2.1
          else if P = R then t.2.2.1
          else if P = S then t.2.2.2 else 0)
        * (Nat.factorial (if Q = P then t.1
            else if Q = Q then t.2.1
            else if Q = R then t.2.2.1
            else if Q = S then t.2.2.2 else 0)
        * (Nat.factorial (if R = P then t.1
            else if R = Q then t.2.1
            else if R = R then t.2.2.1
            else if R = S then t.2.2.2 else 0)
        * Nat.factorial (if S = P then t.1
            else if S = Q then t.2.1
            else if S = R then t.2.2.1
            else if S = S then t.2.2.2 else 0)))
      = Nat.factorial t.1 * Nat.factorial t.2.1
        * Nat.factorial t.2.2.1 * Nat.factorial t.2.2.2
    rw [if_pos rfl, if_neg (Ne.symm hPQ), if_pos rfl,
      if_neg (Ne.symm hPR), if_neg (Ne.symm hQR), if_pos rfl,
      if_neg (Ne.symm hPS), if_neg (Ne.symm hQS),
      if_neg (Ne.symm hRS), if_pos rfl]
    ring
  have hbij :
      ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
                ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ t ∈ S6, (720 / ((Nat.factorial t.1
              * Nat.factorial t.2.1 * Nat.factorial t.2.2.1
              * Nat.factorial t.2.2.2 : ℕ) : ℝ))
            * ∫ α : LayerSite N → G, ∏ X ∈ C,
                (colDensC ρ u u' X α)
                  ^ ((fun X => if X = P then t.1
                    else if X = Q then t.2.1
                    else if X = R then t.2.2.1
                    else if X = S then t.2.2.2 else 0) X)
                ∂(Measure.pi fun _ : LayerSite N => μG) := by
    refine (Finset.sum_bij
      (fun t _ => fun X => if X = P then t.1
        else if X = Q then t.2.1
        else if X = R then t.2.2.1
        else if X = S then t.2.2.2 else 0) ?_ ?_ ?_ ?_).symm
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      exact ⟨⟨hsumT t ht, fun X _ => Finset.mem_univ X⟩,
        hsuppT t ht⟩
    · intro t _ t' _ h
      have e1 : t.1 = t'.1 := by
        have h2 : (if P = P then t.1 else if P = Q then t.2.1
              else if P = R then t.2.2.1
              else if P = S then t.2.2.2 else 0)
            = (if P = P then t'.1 else if P = Q then t'.2.1
              else if P = R then t'.2.2.1
              else if P = S then t'.2.2.2 else 0) :=
          congrFun h P
        rw [if_pos rfl, if_pos rfl] at h2
        exact h2
      have e2 : t.2.1 = t'.2.1 := by
        have h2 : (if Q = P then t.1 else if Q = Q then t.2.1
              else if Q = R then t.2.2.1
              else if Q = S then t.2.2.2 else 0)
            = (if Q = P then t'.1 else if Q = Q then t'.2.1
              else if Q = R then t'.2.2.1
              else if Q = S then t'.2.2.2 else 0) :=
          congrFun h Q
        rw [if_neg (Ne.symm hPQ), if_pos rfl,
          if_neg (Ne.symm hPQ), if_pos rfl] at h2
        exact h2
      have e3 : t.2.2.1 = t'.2.2.1 := by
        have h2 : (if R = P then t.1 else if R = Q then t.2.1
              else if R = R then t.2.2.1
              else if R = S then t.2.2.2 else 0)
            = (if R = P then t'.1 else if R = Q then t'.2.1
              else if R = R then t'.2.2.1
              else if R = S then t'.2.2.2 else 0) :=
          congrFun h R
        rw [if_neg (Ne.symm hPR), if_neg (Ne.symm hQR),
          if_pos rfl, if_neg (Ne.symm hPR),
          if_neg (Ne.symm hQR), if_pos rfl] at h2
        exact h2
      have e4 : t.2.2.2 = t'.2.2.2 := by
        have h2 : (if S = P then t.1 else if S = Q then t.2.1
              else if S = R then t.2.2.1
              else if S = S then t.2.2.2 else 0)
            = (if S = P then t'.1 else if S = Q then t'.2.1
              else if S = R then t'.2.2.1
              else if S = S then t'.2.2.2 else 0) :=
          congrFun h S
        rw [if_neg (Ne.symm hPS), if_neg (Ne.symm hQS),
          if_neg (Ne.symm hRS), if_pos rfl,
          if_neg (Ne.symm hPS), if_neg (Ne.symm hQS),
          if_neg (Ne.symm hRS), if_pos rfl] at h2
        exact h2
      obtain ⟨a, b, c, d⟩ := t
      obtain ⟨a', b', c', d'⟩ := t'
      simp only [Prod.mk.injEq]
      exact ⟨e1, e2, e3, e4⟩
    · intro k hk
      have hk6 : ∑ X ∈ Finset.univ, k X = 6 :=
        (Finset.mem_piAntidiag.mp
          (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C :=
        (Finset.mem_filter.mp hk).2
      have hge : ∀ X ∈ C, 1 ≤ k X := by
        intro X hX
        have hXs : X ∈ multSupport k := hsupp ▸ hX
        exact Nat.one_le_iff_ne_zero.mpr
          (Finset.mem_filter.mp hXs).2
      have hsumC : ∑ X ∈ C, k X = 6 := by
        rw [← hsupp, ← sum_univ_eq_sum_multSupport]
        exact hk6
      have hsumC' : k P + k Q + k R + k S = 6 := by
        have h := hsumC
        rw [hCeq, Finset.sum_insert hnotP,
          Finset.sum_insert hnotQ, Finset.sum_insert hnotR,
          Finset.sum_singleton] at h
        omega
      have hkP1 : 1 ≤ k P := hge P hPmem
      have hkQ1 : 1 ≤ k Q := hge Q hQmem
      have hkR1 : 1 ≤ k R := hge R hRmem
      have hkS1 : 1 ≤ k S := hge S hSmem
      have hkP3 : k P ≤ 3 := by omega
      have hkQ3 : k Q ≤ 3 := by omega
      have hkR3 : k R ≤ 3 := by omega
      have hkS3 : k S ≤ 3 := by omega
      refine ⟨(k P, k Q, k R, k S), ?_, ?_⟩
      · rw [hS6, Finset.mem_filter, Finset.mem_product,
          Finset.mem_product, Finset.mem_product,
          Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc,
          Finset.mem_Icc]
        exact ⟨⟨⟨hkP1, hkP3⟩, ⟨hkQ1, hkQ3⟩, ⟨hkR1, hkR3⟩,
          ⟨hkS1, hkS3⟩⟩, hsumC'⟩
      · funext X
        by_cases hXP : X = P
        · rw [hXP, if_pos rfl]
        · by_cases hXQ : X = Q
          · rw [hXQ]
            have hQP : Q ≠ P := by
              rintro rfl
              exact hXP hXQ
            rw [if_neg hQP, if_pos rfl]
          · by_cases hXR : X = R
            · rw [hXR]
              have hRP : R ≠ P := by
                rintro rfl
                exact hXP hXR
              have hRQ : R ≠ Q := by
                rintro rfl
                exact hXQ hXR
              rw [if_neg hRP, if_neg hRQ, if_pos rfl]
            · by_cases hXS : X = S
              · rw [hXS]
                have hSP : S ≠ P := by
                  rintro rfl
                  exact hXP hXS
                have hSQ : S ≠ Q := by
                  rintro rfl
                  exact hXQ hXS
                have hSR : S ≠ R := by
                  rintro rfl
                  exact hXR hXS
                rw [if_neg hSP, if_neg hSQ, if_neg hSR,
                  if_pos rfl]
              · have hk0 : k X = 0 := by
                  by_contra hne
                  have hXs : X ∈ multSupport k :=
                    Finset.mem_filter.mpr
                      ⟨Finset.mem_univ X, hne⟩
                  rw [hsupp, hCeq, Finset.mem_insert,
                    Finset.mem_insert, Finset.mem_insert,
                    Finset.mem_singleton] at hXs
                  exact hXs.elim hXP
                    (fun h => h.elim hXQ
                      (fun h => h.elim hXR hXS))
                rw [hk0]
                simp [hXP, hXQ, hXR, hXS]
    · intro t ht
      have hmult : (Nat.multinomial Finset.univ
            (fun X => if X = P then t.1
              else if X = Q then t.2.1
              else if X = R then t.2.2.1
              else if X = S then t.2.2.2 else 0) : ℝ)
          = 720 / ((Nat.factorial t.1 * Nat.factorial t.2.1
            * Nat.factorial t.2.2.1 * Nat.factorial t.2.2.2
            : ℕ) : ℝ) :=
        multinomial6_univ_eq _ (hsumT t ht) _ (hfactT t ht)
          (by positivity)
      have hint : ∫ α : LayerSite N → G, ∏ X ∈ Finset.univ,
            (colDensC ρ u u' X α)
              ^ ((fun X => if X = P then t.1
                else if X = Q then t.2.1
                else if X = R then t.2.2.1
                else if X = S then t.2.2.2 else 0) X)
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = ∫ α : LayerSite N → G, ∏ X ∈ C,
              (colDensC ρ u u' X α)
                ^ ((fun X => if X = P then t.1
                  else if X = Q then t.2.1
                  else if X = R then t.2.2.1
                  else if X = S then t.2.2.2 else 0) X)
              ∂(Measure.pi fun _ : LayerSite N => μG) := by
        rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u'
          _, hsuppT t ht]
      rw [hmult, hint]
  have hSeq : S6 = {(3, 1, 1, 1), (1, 3, 1, 1), (1, 1, 3, 1),
      (1, 1, 1, 3), (2, 2, 1, 1), (2, 1, 2, 1), (2, 1, 1, 2),
      (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} := by
    apply Finset.ext
    intro t
    obtain ⟨a, b, c, d⟩ := t
    simp only [hS6, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, ha3⟩, ⟨hb1, hb3⟩, ⟨hc1, hc3⟩,
        ⟨hd1, hd3⟩⟩, hsum⟩
      interval_cases a <;> interval_cases b <;>
        interval_cases c <;> interval_cases d <;>
        simp at hsum ⊢
    · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
        exact ⟨⟨⟨by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num⟩⟩, by norm_num⟩
  have hDDsymm : ∀ X Y : LayerColumn N,
      doubledDoubledQuadReMoment ρ μG C X Y u u'
        = doubledDoubledQuadReMoment ρ μG C Y X u u' := by
    intro X Y
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun α => ?_
    have hcomm : (C.erase Y).erase X = (C.erase X).erase Y := by
      refine Finset.ext fun Z => ?_
      simp only [Finset.mem_erase]
      exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩,
        fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
    show (colRe ρ u u' X α) ^ 2 * (colRe ρ u u' Y α) ^ 2
        * ∏ Z ∈ (C.erase X).erase Y, colRe ρ u u' Z α
      = (colRe ρ u u' Y α) ^ 2 * (colRe ρ u u' X α) ^ 2
        * ∏ Z ∈ (C.erase Y).erase X, colRe ρ u u' Z α
    rw [hcomm]
    ring
  have hDDvalsymm : ∀ X Y : LayerColumn N,
      ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C X u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Y u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C X Y u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((densMomentValue ρ μG 2) ^ 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Y u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C X u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Y X u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    intro X Y
    rw [hDDsymm X Y]
    ring
  have hTord : ∑ X ∈ C, (120 : ℝ)
        * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = 120 * ((densMomentValue ρ μG 3
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        + (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        + (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C R u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C R u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        + (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C S u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C S u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))) := by
    rw [hCeq, Finset.sum_insert hnotP, Finset.sum_insert hnotQ,
      Finset.sum_insert hnotR, Finset.sum_singleton]
    ring
  have hsumCeq : ∀ (F : LayerColumn N → ℝ),
      ∑ X ∈ C, F X = F P + (F Q + (F R + F S)) := by
    intro F
    rw [hCeq, Finset.sum_insert hnotP, Finset.sum_insert hnotQ,
      Finset.sum_insert hnotR, Finset.sum_singleton]
  have hnotPR : P ∉ ({R, S} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPR, hPS⟩
  have hnotPS' : P ∉ ({Q, S} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPS⟩
  have hnotQs : Q ∉ ({S} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hQS
  have hnotPQ : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPR⟩
  have hnotQr : Q ∉ ({R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hQR
  have hCeqQ : C = {Q, P, R, S} := by
    rw [hCeq]
    exact Finset.insert_comm P Q {R, S}
  have hCeqR : C = {R, P, Q, S} := by
    rw [hCeq, Finset.insert_comm Q R, Finset.insert_comm P R]
  have hCeqS : C = {S, P, Q, R} := by
    rw [hCeq]
    refine Finset.ext fun Z => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hnotQ' : Q ∉ ({P, R, S} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨Ne.symm hPQ, hQR, hQS⟩
  have hnotR' : R ∉ ({P, Q, S} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨Ne.symm hPR, Ne.symm hQR, hRS⟩
  have hnotS' : S ∉ ({P, Q, R} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨Ne.symm hPS, Ne.symm hQS, Ne.symm hRS⟩
  have heraseP : C.erase P = {Q, R, S} := by
    rw [hCeq]
    exact Finset.erase_insert hnotP
  have heraseQ : C.erase Q = {P, R, S} := by
    rw [hCeqQ]
    exact Finset.erase_insert hnotQ'
  have heraseR : C.erase R = {P, Q, S} := by
    rw [hCeqR]
    exact Finset.erase_insert hnotR'
  have heraseS : C.erase S = {P, Q, R} := by
    rw [hCeqS]
    exact Finset.erase_insert hnotS'
  have hDDord : ∑ X ∈ C, ∑ Y ∈ C.erase X, (90 : ℝ)
        * ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Y u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 180 * (((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C P Q u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        + ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C R u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C P R u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        + ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C S u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C P S u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        + ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C R u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C Q R u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        + ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C S u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C Q S u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        + ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C R u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C S u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C R S u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))) := by
    rw [hsumCeq]
    rw [heraseP, heraseQ, heraseR, heraseS,
      Finset.sum_insert hnotQ, Finset.sum_insert hnotR,
      Finset.sum_singleton,
      Finset.sum_insert hnotPR, Finset.sum_insert hnotR,
      Finset.sum_singleton,
      Finset.sum_insert hnotPS', Finset.sum_insert hnotQs,
      Finset.sum_singleton,
      Finset.sum_insert hnotPQ, Finset.sum_insert hnotQr,
      Finset.sum_singleton,
      hDDvalsymm Q P, hDDvalsymm R P, hDDvalsymm S P,
      hDDvalsymm R Q, hDDvalsymm S Q, hDDvalsymm S R]
    ring
  have hni1 : (3, 1, 1, 1) ∉ ({(1, 3, 1, 1), (1, 1, 3, 1), (1, 1, 1, 3), (2, 2, 1, 1), (2, 1, 2, 1), (2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni2 : (1, 3, 1, 1) ∉ ({(1, 1, 3, 1), (1, 1, 1, 3), (2, 2, 1, 1), (2, 1, 2, 1), (2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni3 : (1, 1, 3, 1) ∉ ({(1, 1, 1, 3), (2, 2, 1, 1), (2, 1, 2, 1), (2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni4 : (1, 1, 1, 3) ∉ ({(2, 2, 1, 1), (2, 1, 2, 1), (2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni5 : (2, 2, 1, 1) ∉ ({(2, 1, 2, 1), (2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni6 : (2, 1, 2, 1) ∉ ({(2, 1, 1, 2), (1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni7 : (2, 1, 1, 2) ∉ ({(1, 2, 2, 1), (1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni8 : (1, 2, 2, 1) ∉ ({(1, 2, 1, 2), (1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hni9 : (1, 2, 1, 2) ∉ ({(1, 1, 2, 2)} : Finset (ℕ × ℕ × ℕ × ℕ)) := by decide
  have hExpand : ∀ (F : ℕ × ℕ × ℕ × ℕ → ℝ),
      ∑ t ∈ S6, F t = F (3, 1, 1, 1) + (F (1, 3, 1, 1) + (F (1, 1, 3, 1) + (F (1, 1, 1, 3) + (F (2, 2, 1, 1) + (F (2, 1, 2, 1) + (F (2, 1, 1, 2) + (F (1, 2, 2, 1) + (F (1, 2, 1, 2) + (F (1, 1, 2, 2)))))))))) := by
    intro F
    rw [hSeq, Finset.sum_insert hni1, Finset.sum_insert hni2,
      Finset.sum_insert hni3, Finset.sum_insert hni4,
      Finset.sum_insert hni5, Finset.sum_insert hni6,
      Finset.sum_insert hni7, Finset.sum_insert hni8,
      Finset.sum_insert hni9, Finset.sum_singleton]
  have hJ3111 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 3 else if X = Q then 1
          else if X = R then 1 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 3 else if X = Q then 1
          else if X = R then 1 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = P then 3 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp
      · simp [Ne.symm hPQ]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_tripled ρ μG hN hN3
      hρcont u u' C hC P hPmem
  have hJ1311 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 3
          else if X = R then 1 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 3
          else if X = R then 1 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = Q then 3 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPQ]
      · simp [Ne.symm hPQ]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_tripled ρ μG hN hN3
      hρcont u u' C hC Q hQmem
  have hJ1131 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 3 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 3 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = R then 3 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPR]
      · simp [Ne.symm hPQ, hQR]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_tripled ρ μG hN hN3
      hρcont u u' C hC R hRmem
  have hJ1113 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 1 else if X = S then 3 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 3 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C S u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C S u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 1 else if X = S then 3 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = S then 3 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPS]
      · simp [Ne.symm hPQ, hQS]
      · simp [Ne.symm hPR, Ne.symm hQR, hRS]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_tripled ρ μG hN hN3
      hρcont u u' C hC S hSmem
  have hJ2211 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 2
          else if X = R then 1 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 2
          else if X = R then 1 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = P then 2 else if X = Q then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp
      · simp [Ne.symm hPQ]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC P Q hPmem hQmem (Ne.symm hPQ)
  have hJ2121 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 1
          else if X = R then 2 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 1
          else if X = R then 2 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = P then 2 else if X = R then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp
      · simp [Ne.symm hPQ, hQR]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC P R hPmem hRmem (Ne.symm hPR)
  have hJ2112 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 1
          else if X = R then 1 else if X = S then 2 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C S u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P S u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 2 else if X = Q then 1
          else if X = R then 1 else if X = S then 2 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = P then 2 else if X = S then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp
      · simp [Ne.symm hPQ, hQS]
      · simp [Ne.symm hPR, Ne.symm hQR, hRS]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC P S hPmem hSmem (Ne.symm hPS)
  have hJ1221 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 2
          else if X = R then 2 else if X = S then 1 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 2
          else if X = R then 2 else if X = S then 1 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = Q then 2 else if X = R then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPQ, hPR]
      · simp [Ne.symm hPQ]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC Q R hQmem hRmem (Ne.symm hQR)
  have hJ1212 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 2
          else if X = R then 1 else if X = S then 2 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C S u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q S u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 2
          else if X = R then 1 else if X = S then 2 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = Q then 2 else if X = S then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPQ, hPS]
      · simp [Ne.symm hPQ]
      · simp [Ne.symm hPR, Ne.symm hQR, hRS]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC Q S hQmem hSmem (Ne.symm hQS)
  have hJ1122 : ∫ α : LayerSite N → G, ∏ X ∈ C,
        (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 2 else if X = S then 2 else 0)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C S u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C R S u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    have hprod : ∀ α : LayerSite N → G,
        ∏ X ∈ C, (colDensC ρ u u' X α) ^ (if X = P then 1 else if X = Q then 1
          else if X = R then 2 else if X = S then 2 else 0)
          = ∏ X ∈ C, (colDensC ρ u u' X α)
              ^ (if X = R then 2 else if X = S then 2 else 1) := by
      intro α
      refine Finset.prod_congr rfl fun X hX => ?_
      rw [hCeq, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · simp [hPR, hPS]
      · simp [Ne.symm hPQ, hQR, hQS]
      · simp [Ne.symm hPR, Ne.symm hQR]
      · simp [Ne.symm hPS, Ne.symm hQS, Ne.symm hRS]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quadruple_doubled_doubled ρ μG
      hN hN3 hρcont u u' C hC R S hRmem hSmem (Ne.symm hRS)
  rw [hbij, hExpand]
  dsimp only
  rw [hJ3111, hJ1311, hJ1131, hJ1113, hJ2211, hJ2121, hJ2112,
    hJ1221, hJ1212, hJ1122, hTord, hDDord]
  norm_num [Nat.factorial]
  ring
end Fiber6b

/-! ## B6-2b-iii: the card-6 fiber, the six-support split,
and the total decomposition

The last fiber of the sixth-power expansion and the
assembly of the total in fiber language. Card `6`
carries the single all-ones pattern `(1,1,1,1,1,1)`
(multinomial weight `720`); its pattern value is the
sextuple value below, whose top subset is the
all-distinct order-6 moment `hexaReMoment` and whose
lower subset levels are the order-4 and order-5
excesses of the support's subsets. The six-support sum
of the top excess then splits by B6-0's classification
into the `C₆` family, the `Θ(2,2,2)` family, and the
remaining supports, every one of which has a private
column and whose moment factors through order-4
content by two erasure strips. The total
`betaCoeff6_total` is stated in fiber language only:
`kappa6Const` plus the fiber sums of cards `4`, `5`,
`6`, with the coefficients exactly as they emerge from
the fiber lemmas. **No `kappa6dep` identity is asserted
here (that conversion is B6-2c's), and no sign is
asserted for any term.** NO CLAIM; dials 0/4. -/

section Fiber6c

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The sextuple pattern value.** For a 6-support
`C`, the all-distinct density value is the fully-split
baseline `B⁶` plus `d⁻⁴` times the sum of the order-4
excesses of its 4-subsupports, minus `d⁻⁵` times the
sum of the order-5 excesses of its 5-subsupports, plus
`d⁻⁶` times the sixfold excess
`hexaReMoment C − e₁⁶`. Proved by the subset expansion
over the powerset of `C`: subsets of size at most `3`
factor, the 4- and 5-subsets contribute their excesses
at weights `c⁴`, `c⁵`, and the top subset contributes
the sixfold excess at weight `c⁶`, with
`c = −d⁻¹`. The mirror of
`integral_colDens_prod_quintuple` at one support size
up, with one extra subset level. -/
theorem integral_colDens_prod_sextuple (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) :
    ∫ α : LayerSite N → G, ∏ Q ∈ C, colDensC ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 6
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + ((d : ℝ)⁻¹) ^ 6
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hx : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      colDensC ρ u u' Z α = c * colRe ρ u u' Z α + 1 := by
    intro Z α
    rw [colDensC_eq, div_eq_inv_mul]
    ring
  have hpt : ∀ α : LayerSite N → G,
      ∏ Q ∈ C, colDensC ρ u u' Q α
        = ∑ T ∈ C.powerset, c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α := by
    intro α
    have h1 : ∏ Q ∈ C, colDensC ρ u u' Q α
        = ∏ Q ∈ C, (c * colRe ρ u u' Q α + 1) :=
      Finset.prod_congr rfl fun Q _ => hx Q α
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const]
  have hval : ∀ T ∈ C.powerset,
      ∫ α : LayerSite N → G, c ^ T.card
            * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = c ^ T.card * (e1 ρ μG) ^ T.card
          + (if T ∈ Finset.powersetCard 4 C then
              c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
             else 0)
          + (if T ∈ Finset.powersetCard 5 C then
              c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
             else 0)
          + (if T = C then
              c ^ 6 * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C := Finset.mem_powerset.mp hT
    rw [integral_const_mul]
    by_cases hT6 : T = C
    · subst hT6
      have hnotpc4 : T ∉ Finset.powersetCard 4 T :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hC] at h4
          exact absurd h4 (by norm_num)
      have hnotpc5 : T ∉ Finset.powersetCard 5 T :=
        fun h => by
          have h5 := (Finset.mem_powersetCard.mp h).2
          rw [hC] at h5
          exact absurd h5 (by norm_num)
      rw [if_neg hnotpc4, if_neg hnotpc5, if_pos rfl, hC]
      show c ^ 6 * hexaReMoment ρ μG T u u'
        = c ^ 6 * (e1 ρ μG) ^ 6 + 0 + 0
          + c ^ 6 * (hexaReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
      ring
    · rw [if_neg hT6]
      by_cases hT5 : T ∈ Finset.powersetCard 5 C
      · have hcard5 : T.card = 5 :=
          (Finset.mem_powersetCard.mp hT5).2
        have hnotpc4 : T ∉ Finset.powersetCard 4 C :=
          fun h => by
            have h4 := (Finset.mem_powersetCard.mp h).2
            rw [hcard5] at h4
            exact absurd h4 (by norm_num)
        rw [if_neg hnotpc4, if_pos hT5, hcard5]
        show c ^ 5 * quadReMoment ρ μG T u u'
          = c ^ 5 * (e1 ρ μG) ^ 5 + 0
            + c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
            + 0
        ring
      · rw [if_neg hT5]
        by_cases hT4 : T ∈ Finset.powersetCard 4 C
        · rw [if_pos hT4]
          have hcard4 : T.card = 4 :=
            (Finset.mem_powersetCard.mp hT4).2
          rw [hcard4]
          show c ^ 4 * quadReMoment ρ μG T u u'
            = c ^ 4 * (e1 ρ μG) ^ 4
              + c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
              + 0 + 0
          ring
        · rw [if_neg hT4, add_zero, add_zero, add_zero]
          have hcard : T.card ≤ 3 := by
            have h1 : T.card ≤ 6 := le_trans
              (Finset.card_le_card hsub) (le_of_eq hC)
            have hne4 : T.card ≠ 4 := fun h4 =>
              hT4 (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
            have hne5 : T.card ≠ 5 := fun h5 =>
              hT5 (Finset.mem_powersetCard.mpr ⟨hsub, h5⟩)
            have hne6 : T.card ≠ 6 := fun h6 =>
              hT6 (Finset.eq_of_subset_of_card_le hsub
                (by rw [hC]; omega))
            omega
          rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3
            hρcont u u' T hcard]
  have hBase6 : (∑ T ∈ C.powerset, c ^ T.card * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 6 := by
    have hT0 : ∀ T ∈ C.powerset,
        c ^ T.card * (e1 ρ μG) ^ T.card
          = (c * e1 ρ μG) ^ T.card := fun T _ =>
      (mul_pow _ _ _).symm
    calc (∑ T ∈ C.powerset, c ^ T.card * (e1 ρ μG) ^ T.card)
        = ∑ T ∈ C.powerset, (c * e1 ρ μG) ^ T.card :=
          Finset.sum_congr rfl hT0
      _ = ∑ T ∈ C.powerset,
            (∏ Q ∈ T, (c * e1 ρ μG))
              * ∏ Q ∈ C \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const, Finset.prod_const_one, mul_one]
      _ = ∏ Q ∈ C, (c * e1 ρ μG + 1) :=
          (Finset.prod_add _ _ _).symm
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 6 := by
          rw [Finset.prod_const, hC]
          congr 1
          rw [div_eq_inv_mul]
          ring
  have hMid4 : (∑ T ∈ C.powerset,
        (if T ∈ Finset.powersetCard 4 C then
          c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
         else 0))
      = c ^ 4 * ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have hsubpc : Finset.powersetCard 4 C ⊆ C.powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ C.powerset,
          (if T ∈ Finset.powersetCard 4 C then
            c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
           else 0))
        = ∑ T ∈ Finset.powersetCard 4 C,
            c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
      (Finset.sum_subset hsubpc (fun T _ hT => if_neg hT)).symm.trans
        (Finset.sum_congr rfl fun T hT => if_pos hT)
    rw [step1, ← Finset.mul_sum]
  have hMid5 : (∑ T ∈ C.powerset,
        (if T ∈ Finset.powersetCard 5 C then
          c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
         else 0))
      = c ^ 5 * ∑ T ∈ Finset.powersetCard 5 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5) := by
    have hsubpc : Finset.powersetCard 5 C ⊆ C.powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ C.powerset,
          (if T ∈ Finset.powersetCard 5 C then
            c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
           else 0))
        = ∑ T ∈ Finset.powersetCard 5 C,
            c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5) :=
      (Finset.sum_subset hsubpc (fun T _ hT => if_neg hT)).symm.trans
        (Finset.sum_congr rfl fun T hT => if_pos hT)
    rw [step1, ← Finset.mul_sum]
  have hTop6 : (∑ T ∈ C.powerset,
        (if T = C then
          c ^ 6 * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
         else 0))
      = c ^ 6 * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    rw [Finset.sum_ite_eq' C.powerset C
      (fun _ => c ^ 6
        * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun T _ =>
      Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl
              fun Q _ => pow_one (colRe ρ u u' Q α))) _),
    Finset.sum_congr rfl hval, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hBase6,
    hMid4, hMid5, hTop6, hc4, hc5, hc6]
  ring

/-- **The card-6 fiber.** Over a 6-support `C`, the
fiber of the expansion is the single all-ones pattern:
every exponent on the support is `1` (B6-0's
`eq_one_of_card_six`, since the exponents sum to `6`
over a 6-element support of exponents at least `1`),
its multinomial coefficient is `720`, and its value
is the sextuple pattern value. -/
theorem fiber_card_six (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 720 * ((1 - e1 ρ μG / (d : ℝ)) ^ 6
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)) := by
  classical
  have hfib : (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C)
      = {fun P => if P ∈ C then 1 else 0} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ?_
    constructor
    · refine ⟨fun P => if P ∈ C then 1 else 0, ?_⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_piAntidiag]
        constructor
        · have h1 : ∀ P ∈ Finset.univ,
              (if P ∈ C then (1 : ℕ) else 0)
                = if P ∈ C then 1 else 0 := fun P _ => rfl
          rw [Finset.sum_congr rfl h1, Finset.sum_boole]
          simp [hC]
        · intro P _
          exact Finset.mem_univ P
      · have hsupp : multSupport (fun P => if P ∈ C then 1 else 0)
            = C := by
          refine Finset.ext fun P => ?_
          simp only [multSupport, Finset.mem_filter,
            Finset.mem_univ, true_and]
          by_cases hP : P ∈ C <;> simp [hP]
        exact hsupp
    · intro k hk
      have hk6 : ∑ P ∈ Finset.univ, k P = 6 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hcard : (multSupport k).card = 6 := by rw [hsupp]; exact hC
      funext P
      by_cases hP : P ∈ C
      · have hPs : P ∈ multSupport k := hsupp ▸ hP
        rw [eq_one_of_card_six k hk6 hcard P hPs, if_pos hP]
      · have hPs : P ∉ multSupport k := hsupp ▸ hP
        have hk0 : k P = 0 := by
          by_contra hne
          exact hPs (Finset.mem_filter.mpr
            ⟨Finset.mem_univ P, hne⟩)
        rw [hk0, if_neg hP]
  rw [hfib, Finset.sum_singleton]
  have hmult : (Nat.multinomial Finset.univ
        (fun P => if P ∈ C then 1 else 0) : ℝ) = 720 := by
    have hp : ∏ P ∈ Finset.univ,
        Nat.factorial ((fun P => if P ∈ C then 1 else 0) P)
          = 1 := by
      exact (Finset.prod_subset (Finset.subset_univ C)
        (fun P _ hP => by simp [hP])).symm.trans
        (Finset.prod_eq_one fun P _ => by
          by_cases hP : P ∈ C <;> simp [hP])
    have hk6 : ∑ P ∈ Finset.univ,
        (fun P => if P ∈ C then 1 else 0) P = 6 := by
      have h1 : ∀ P ∈ Finset.univ,
          (fun P => if P ∈ C then (1 : ℕ) else 0) P
            = if P ∈ C then 1 else 0 := fun P _ => rfl
      rw [Finset.sum_congr rfl h1, Finset.sum_boole]
      simp [hC]
    have := multinomial6_univ_eq (fun P => if P ∈ C then 1 else 0)
      hk6 1 hp one_ne_zero
    rw [this]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ,
          (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 6
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + ((d : ℝ)⁻¹) ^ 6
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    have hsupp : multSupport (fun P => if P ∈ C then 1 else 0)
        = C := by
      refine Finset.ext fun P => ?_
      simp only [multSupport, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases hP : P ∈ C <;> simp [hP]
    rw [integral_colDens_prod_pow_univ_six ρ μG hρcont u u'
      (fun P => if P ∈ C then 1 else 0), hsupp]
    have hprod : ∀ α : LayerSite N → G,
        ∏ P ∈ C, (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
          = ∏ P ∈ C, colDensC ρ u u' P α :=
      fun α => Finset.prod_congr rfl fun P hP => by
        simp [hP]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_sextuple ρ μG hN hN3 hρcont
      u u' C hC
  rw [hmult, hval]

/-- **Erasure double sum.** Summing a column function
over the erasures of a support counts each column
`C.card − 1` times: the pairs `(P, x)` with
`x ∈ C.erase P` are the ordered pairs of distinct
columns of `C`. -/
theorem sum_sum_erase_eq (C : Finset (LayerColumn N))
    (f : LayerColumn N → ℝ) :
    ∑ P ∈ C, ∑ x ∈ C.erase P, f x
      = ((C.card : ℝ) - 1) * ∑ x ∈ C, f x := by
  classical
  have herase : ∀ P : LayerColumn N,
      C.erase P = C.filter (fun x => x ≠ P) := by
    intro P
    refine Finset.ext fun x => ?_
    simp only [Finset.mem_erase, Finset.mem_filter, and_comm]
  have hinner : ∀ x ∈ C,
      ∑ P ∈ C, (if x ≠ P then f x else 0)
        = ((C.card : ℝ) - 1) * f x := by
    intro x hx
    have h1 : (∑ P ∈ C, (if x ≠ P then f x else 0))
        = ∑ P ∈ C.filter (fun P => x ≠ P), f x :=
      (Finset.sum_filter (fun P => x ≠ P) (fun _ => f x)).symm
    have hfilteq : C.filter (fun P => x ≠ P) = C.erase x := by
      refine Finset.ext fun P => ?_
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨fun h => ⟨Ne.symm h.2, h.1⟩,
        fun h => ⟨h.2, Ne.symm h.1⟩⟩
    have hcardf : (C.filter (fun P => x ≠ P)).card = C.card - 1 := by
      rw [hfilteq, Finset.card_erase_of_mem hx]
    have h1le : 1 ≤ C.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_pos.mpr ⟨x, hx⟩).ne'
    rw [h1, Finset.sum_const, hcardf, nsmul_eq_mul,
      Nat.cast_sub h1le, Nat.cast_one]
  calc ∑ P ∈ C, ∑ x ∈ C.erase P, f x
      = ∑ P ∈ C, ∑ x ∈ C, (if x ≠ P then f x else 0) :=
        Finset.sum_congr rfl fun P _ => by
          rw [herase P, Finset.sum_filter]
    _ = ∑ x ∈ C, ∑ P ∈ C, (if x ≠ P then f x else 0) :=
        Finset.sum_comm
    _ = ∑ x ∈ C, ((C.card : ℝ) - 1) * f x :=
        Finset.sum_congr rfl hinner
    _ = ((C.card : ℝ) - 1) * ∑ x ∈ C, f x := by
        rw [Finset.mul_sum]

/-- **The fivefold excess factors through order 4.**
For a 5-support `C`, the private column `X` of the
order-5 selection rule splits the fivefold moment, and
every other erasure `C.erase x` is non-primitive, so
its order-4 excess vanishes and the sum of erasure
excesses is the single term at `X`. (The order-6
section's copy of the order-5 assembly's lemma of the
same shape, reproved here from the order-5 selection
and order-4 excess inputs this module imports.) -/
theorem pentaExcess_eq_e1_sum_erase (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5
      = (e1 ρ μG) * ∑ x ∈ C,
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
  classical
  obtain ⟨X, hXC, s, hsX, hpriv⟩ :=
    exists_private_column_of_card_five (N := N) hN hN3 hC
  have hXF : X ∉ C.erase X :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ P ∈ C.erase X, s ∉ colSites P :=
    fun P hP => hpriv P (Finset.mem_erase.mp hP).2
      (Finset.mem_erase.mp hP).1
  have hfact : quadReMoment ρ μG C u u'
      = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u' := by
    have hsplit : quadReMoment ρ μG C u u'
        = ∫ α : LayerSite N → G,
            (∏ P ∈ C.erase X,
              (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
              * (colRe ρ u u' X α) ^ (1 : ℕ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      show (∏ P ∈ C, colRe ρ u u' P α) = _
      rw [← Finset.mul_prod_erase C
        (fun P => colRe ρ u u' P α) hXC]
      simp only [pow_one]
      ring
    calc quadReMoment ρ μG C u u'
        = ∫ α : LayerSite N → G,
            (∏ P ∈ C.erase X,
              (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
              * (colRe ρ u u' X α) ^ (1 : ℕ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := hsplit
      _ = realMoment ρ μG 1
            * ∫ α : LayerSite N → G, ∏ P ∈ C.erase X,
                (colRe ρ u u' P α)
                  ^ ((fun _ : LayerColumn N => 1) P)
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_colRe_pow_split_finset ρ μG hN hN3 hρcont
            u u' (C.erase X) (fun _ => 1) X hXF s hsX hsF 1
      _ = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u' := by
          rw [realMoment_one]
          refine congrArg _ ?_
          refine integral_congr_ae
            (Filter.Eventually.of_forall fun α => ?_)
          exact Finset.prod_congr rfl fun P _ => pow_one _
  have hvan : ∀ x ∈ C, x ≠ X →
      quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4
        = 0 := by
    intro x hx hxX
    have hcard : (C.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hC]
    refine excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont
      u u' hcard (fun hprim => ?_)
    have hXCx : X ∈ C.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxX, hXC⟩
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXCx s hsX
    exact hpriv Q (Finset.mem_erase.mp hQ).2 hQX hsQ
  have hsum : ∑ x ∈ C,
        (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
      = quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 4 :=
    Finset.sum_eq_single X (fun x hx hxX => hvan x hx hxX)
      (fun h => absurd hXC h)
  rw [hsum, hfact]
  ring

/-- **The sixfold excess at a private column factors
through order 4.** If the 6-support `C` has a column
`X` with a site `s` of distinct degree `1` in `C`,
stripping `X` splits off `e₁` and leaves a 5-support,
whose fivefold excess is `e₁` times the sum of the
order-4 excesses of its erasures, by
`pentaExcess_eq_e1_sum_erase`. -/
theorem hexaExcess_eq_of_private (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) (X : LayerColumn N) (hX : X ∈ C)
    (s : LayerSite N) (hsX : s ∈ colSites X)
    (hdeg : siteDegree C s = 1) :
    hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6
      = (e1 ρ μG) ^ 2 * ∑ y ∈ C.erase X,
          (quadReMoment ρ μG ((C.erase X).erase y) u u'
            - (e1 ρ μG) ^ 4) := by
  classical
  have hsF : ∀ P ∈ C.erase X, s ∉ colSites P := by
    intro P hP hsP
    have hPC : P ∈ C := (Finset.mem_erase.mp hP).2
    have hPX : P ≠ X := (Finset.mem_erase.mp hP).1
    have hdeg' : (C.filter (fun Q => s ∈ colSites Q)).card = 1 :=
      hdeg
    have hlt : 1 < (C.filter (fun Q => s ∈ colSites Q)).card :=
      Finset.one_lt_card.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hX, hsX⟩,
          P, Finset.mem_filter.mpr ⟨hPC, hsP⟩, Ne.symm hPX⟩
    omega
  have hXF : X ∉ C.erase X :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hfact : quadReMoment ρ μG C u u'
      = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u' := by
    have hsplit : quadReMoment ρ μG C u u'
        = ∫ α : LayerSite N → G,
            (∏ P ∈ C.erase X,
              (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
              * (colRe ρ u u' X α) ^ (1 : ℕ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      show (∏ P ∈ C, colRe ρ u u' P α) = _
      rw [← Finset.mul_prod_erase C
        (fun P => colRe ρ u u' P α) hX]
      simp only [pow_one]
      ring
    calc quadReMoment ρ μG C u u'
        = ∫ α : LayerSite N → G,
            (∏ P ∈ C.erase X,
              (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
              * (colRe ρ u u' X α) ^ (1 : ℕ)
            ∂(Measure.pi fun _ : LayerSite N => μG) := hsplit
      _ = realMoment ρ μG 1
            * ∫ α : LayerSite N → G, ∏ P ∈ C.erase X,
                (colRe ρ u u' P α)
                  ^ ((fun _ : LayerColumn N => 1) P)
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_colRe_pow_split_finset ρ μG hN hN3 hρcont
            u u' (C.erase X) (fun _ => 1) X hXF s hsX hsF 1
      _ = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u' := by
          rw [realMoment_one]
          refine congrArg _ ?_
          refine integral_congr_ae
            (Filter.Eventually.of_forall fun α => ?_)
          exact Finset.prod_congr rfl fun P _ => pow_one _
  have hDcard : (C.erase X).card = 5 := by
    rw [Finset.card_erase_of_mem hX, hC]
  have hstep2 : quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 5
      = (e1 ρ μG) * ∑ y ∈ C.erase X,
          (quadReMoment ρ μG ((C.erase X).erase y) u u'
            - (e1 ρ μG) ^ 4) :=
    pentaExcess_eq_e1_sum_erase ρ μG hN hN3 hρcont u u'
      (C.erase X) hDcard
  calc hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6
      = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u'
          - (e1 ρ μG) ^ 6 := by
        rw [hexaReMoment_eq_quadReMoment, hfact]
    _ = (e1 ρ μG)
          * (quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 5) := by
        ring
    _ = (e1 ρ μG) ^ 2 * ∑ y ∈ C.erase X,
          (quadReMoment ρ μG ((C.erase X).erase y) u u'
            - (e1 ρ μG) ^ 4) := by
        rw [hstep2]
        ring

/-- **Every 6-support is a channel support or has a
private column.** If no site of the support has
distinct degree `1`, every support site has distinct
degree at least `2`; the indicator multiplicity
function is then weighted fully shared, and B6-0's
`card_six_classification` puts the support in the
`C₆` or the `Θ` family. -/
theorem mem_c6_or_theta_or_private_of_card_six (hN : Even N)
    (hN3 : 3 ≤ N) (C : Finset (LayerColumn N)) (hC : C.card = 6) :
    C ∈ c6Supports ∨ C ∈ thetaSupports ∨ HasPrivateColumn C := by
  classical
  by_cases hDS : ∀ s ∈ quadSupport C, 2 ≤ siteDegree C s
  · set m : LayerColumn N → ℕ := fun P => if P ∈ C then 1 else 0
      with hm
    have hsupp : multSupport m = C := by
      refine Finset.ext fun P => ?_
      simp only [multSupport, Finset.mem_filter, Finset.mem_univ,
        true_and, hm]
      by_cases hP : P ∈ C <;> simp [hP]
    have hm6 : ∑ P, m P = 6 := by
      have h1 : ∑ P, m P = C.card := by
        rw [Finset.sum_boole]
        simp [hC]
      rw [h1, hC]
    have hW : WFullyShared m := by
      refine fun s hs => ?_
      have hsC : s ∈ quadSupport C := hsupp ▸ hs
      have hcard : (multSupport m).card = 6 := by
        rw [hsupp]; exact hC
      rw [wSiteDegree_eq_siteDegree_of_card_six m hm6 hcard s,
        hsupp]
      exact hDS s hsC
    have hcard : (multSupport m).card = 6 := by
      rw [hsupp]; exact hC
    rcases card_six_classification hN hN3 m hm6 hW hcard with h | h
    · refine Or.inl ?_
      rw [c6Supports, Finset.mem_filter]
      exact ⟨Finset.mem_univ C, hC, hsupp ▸ h⟩
    · refine Or.inr (Or.inl ?_)
      rw [thetaSupports, Finset.mem_filter]
      exact ⟨Finset.mem_univ C, hC, hsupp ▸ h⟩
  · refine Or.inr (Or.inr ?_)
    push_neg at hDS
    obtain ⟨s, hs, hlt⟩ := hDS
    have h1 : 1 ≤ siteDegree C s :=
      one_le_siteDegree_of_mem_quadSupport hs
    have heq : siteDegree C s = 1 := by omega
    obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs
    exact ⟨P, hP, s, hsP, heq⟩

/-- **The six-support split of the sixfold excess
sum.** The sum of `hexaReMoment C − e₁⁶` over all
6-supports separates into the `C₆` family, the `Θ`
family, and the remaining 6-supports; by
`mem_c6_or_theta_or_private_of_card_six` every support
in the remaining family has a private column, and by
`hexaExcess_eq_of_private` its sixfold excess factors
through order-4 erasure excesses. The first two sums
are exactly `kappa6chanC6Excess` and
`kappa6chanThetaExcess`. -/
theorem sum_powersetCard_six_hexaExcess_split (hN : Even N)
    (hN3 : 3 ≤ N) (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6,
        (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
      = ∑ C ∈ c6Supports,
          (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
        + ∑ C ∈ thetaSupports,
          (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
        + ∑ C ∈ (Finset.univ.powersetCard 6).filter
            (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
          (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
  classical
  have hc6sub : c6Supports (N := N)
      ⊆ Finset.univ.powersetCard 6 :=
    fun C hC => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, card_eq_six_of_mem_c6Supports hC⟩
  have hthsub : thetaSupports (N := N)
      ⊆ Finset.univ.powersetCard 6 :=
    fun C hC => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, card_eq_six_of_mem_thetaSupports hC⟩
  have hdisj : Disjoint (c6Supports (N := N)) (thetaSupports (N := N)) := by
    refine Finset.disjoint_left.mpr fun C h1 h2 => ?_
    have h6 : (quadSupport C).card = 6 :=
      (hasSixPatternC6_of_mem_c6Supports h1).1
    have h5 : (quadSupport C).card = 5 :=
      (hasSixPatternTheta_of_mem_thetaSupports h2).1
    omega
  have hUsub : (c6Supports (N := N)) ∪ (thetaSupports (N := N))
      ⊆ Finset.univ.powersetCard 6 :=
    Finset.union_subset hc6sub hthsub
  have hrest : (Finset.univ.powersetCard 6)
        \ ((c6Supports (N := N)) ∪ (thetaSupports (N := N)))
      = (Finset.univ.powersetCard 6).filter
          (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports) := by
    refine Finset.ext fun C => ?_
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, fun h1 => h.2 (Or.inl h1), fun h2 => h.2 (Or.inr h2)⟩
    · intro h
      refine ⟨h.1, ?_⟩
      rintro (h1 | h2)
      · exact h.2.1 h1
      · exact h.2.2 h2
  have hsplit := (Finset.sum_sdiff hUsub (f :=
    fun C => hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)).symm
  rw [hrest, Finset.sum_union hdisj] at hsplit
  rw [hsplit]
  ring

/-- **The remaining six-supports have a private
column**, and their sixfold excess factors through
order-4 erasure excesses at the private column, by
`hexaExcess_eq_of_private`. -/
theorem hexaExcess_factor_of_mem_six_rest (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C ∈ (Finset.univ.powersetCard 6).filter
      (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports)) :
    ∃ X ∈ C, hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6
      = (e1 ρ μG) ^ 2 * ∑ y ∈ C.erase X,
          (quadReMoment ρ μG ((C.erase X).erase y) u u'
            - (e1 ρ μG) ^ 4) := by
  classical
  have hC6 : C.card = 6 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).2
  have hnot : C ∉ c6Supports ∧ C ∉ thetaSupports :=
    (Finset.mem_filter.mp hC).2
  have hpriv : HasPrivateColumn C := by
    rcases mem_c6_or_theta_or_private_of_card_six hN hN3 C hC6
      with h | h | h
    · exact absurd h hnot.1
    · exact absurd h hnot.2
    · exact h
  obtain ⟨X, hX, s, hsX, hdeg⟩ := hpriv
  exact ⟨X, hX, hexaExcess_eq_of_private ρ μG hN hN3 hρcont u u'
    C hC6 X hX s hsX hdeg⟩

end Fiber6c

section Assembly6Total

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **Factorial times choose is the falling product**
(the order-6 section's copy of the order-5 assembly's
lemma, reproved here from `Nat.descFactorial`). -/
theorem cast_factorial_mul_choose6 (j : ℕ) :
    ((Nat.factorial j : ℝ)) * ((Nat.choose (Fintype.card (LayerColumn N)) j : ℝ))
      = ∏ i ∈ Finset.range j, (colCount N - (i : ℝ)) := by
  classical
  have hdesc : ((Fintype.card (LayerColumn N)).descFactorial j : ℝ)
      = ∏ i ∈ Finset.range j, (colCount N - (i : ℝ)) := by
    by_cases hjM : j ≤ Fintype.card (LayerColumn N)
    · induction j with
      | zero => simp
      | succ j ih =>
        have hjM' : j ≤ Fintype.card (LayerColumn N) :=
          le_trans (Nat.le_succ j) hjM
        rw [Nat.descFactorial_succ, Nat.cast_mul, ih hjM',
          Finset.prod_range_succ]
        have hcast : (((Fintype.card (LayerColumn N) - j : ℕ)) : ℝ)
            = colCount N - (j : ℝ) :=
          Nat.cast_sub hjM'
        rw [hcast, mul_comm]
    · have hMj : Fintype.card (LayerColumn N) < j :=
        Nat.lt_of_not_le hjM
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hMj, Nat.cast_zero]
      refine (Finset.prod_eq_zero (Finset.mem_range.mpr hMj) ?_).symm
      simp [colCount]
  rw [← hdesc, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- **Powerset sums split by card.** A sum over the
powerset whose terms vanish at cards `0` and `≥ 7`
is the sum over cards `0..6`. -/
theorem sum_powerset_eq_sum_cards6 (F : Finset (LayerColumn N) → ℝ)
    (hF : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 7 ≤ C.card → F C = 0) :
    ∑ C ∈ Finset.univ.powerset, F C
      = ∑ j ∈ Finset.range 7,
          ∑ C ∈ Finset.univ.powersetCard j, F C := by
  classical
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.range
        ((Finset.univ : Finset (LayerColumn N)).card + 1)) : Set ℕ)
      (fun i => (Finset.univ : Finset (LayerColumn N)).powersetCard
        i) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro C hCi hCj
    exact hij (by
      have h1 := (Finset.mem_powersetCard.mp hCi).2
      have h2 := (Finset.mem_powersetCard.mp hCj).2
      omega)
  have h1 : ∑ C ∈ Finset.univ.powerset, F C
      = ∑ j ∈ Finset.range (Fintype.card (LayerColumn N) + 1),
          ∑ C ∈ Finset.univ.powersetCard j, F C := by
    rw [Finset.powerset_card_biUnion, Finset.sum_biUnion hdisj,
      Finset.card_univ]
  rw [h1]
  by_cases hM : Fintype.card (LayerColumn N) + 1 ≤ 7
  · refine Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by
        have hlt := Finset.mem_range.mp hj
        omega))
      (fun j _ hj => ?_)
    have hjM : Fintype.card (LayerColumn N) < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    have hempty : (Finset.univ : Finset (LayerColumn N)).powersetCard
        j = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun C hC => ?_
      have hCle : C.card ≤ Fintype.card (LayerColumn N) := by
        have hsub : C ⊆ Finset.univ := Finset.subset_univ C
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_univ] at hle
      have hCj : C.card = j := (Finset.mem_powersetCard.mp hC).2
      omega
    rw [hempty, Finset.sum_empty]
  · refine (Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by
        have hlt := Finset.mem_range.mp hj
        omega))
      (fun j _ hj7 => ?_)).symm
    simp only [Finset.mem_range, not_lt] at hj7
    refine Finset.sum_eq_zero fun C hC => ?_
    exact hF C (Or.inr (by
      have hCj := (Finset.mem_powersetCard.mp hC).2
      omega))

/-- **Sum distribution, `a + b − c + d` shape.** The
summand functions are opaque, so distribution cannot
reach inside them. -/
theorem sum_mul_add_sub_add (s : Finset (LayerColumn N))
    (K a b : ℝ) (c d : LayerColumn N → ℝ) :
    ∑ X ∈ s, K * (a + b - c X + d X)
      = K * ((s.card : ℝ) * a + (s.card : ℝ) * b
          - ∑ X ∈ s, c X + ∑ X ∈ s, d X) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul]

/-- **Sum distribution, `a + b − c − d + e` shape with
`c` constant.** -/
theorem sum_mul_add_sub_sub_add (s : Finset (LayerColumn N))
    (K a b c : ℝ) (d e : LayerColumn N → ℝ) :
    ∑ Y ∈ s, K * (a + b - c - d Y + e Y)
      = K * ((s.card : ℝ) * a + (s.card : ℝ) * b
          - (s.card : ℝ) * c - ∑ Y ∈ s, d Y
          + ∑ Y ∈ s, e Y) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul]

/-- **Sum distribution, `a + b − c − d + e` shape with
all three variable terms functional.** -/
theorem sum_mul_add_sub_sub_add_fn (s : Finset (LayerColumn N))
    (K a b : ℝ) (c d e : LayerColumn N → ℝ) :
    ∑ X ∈ s, K * (a + b - c X - d X + e X)
      = K * ((s.card : ℝ) * a + (s.card : ℝ) * b
          - ∑ X ∈ s, c X - ∑ X ∈ s, d X
          + ∑ X ∈ s, e X) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

/-- **Sum distribution, `a + c + d − e − b + f`
shape.** -/
theorem sum_mul_add_add_sub_sub_add (s : Finset (LayerColumn N))
    (K a b : ℝ) (c d e f : LayerColumn N → ℝ) :
    ∑ P ∈ s, K * (a + c P + d P - e P - b + f P)
      = K * ((s.card : ℝ) * a + ∑ P ∈ s, c P
          + ∑ P ∈ s, d P - ∑ P ∈ s, e P
          - (s.card : ℝ) * b + ∑ P ∈ s, f P) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul]

/-- **The card-4 fiber, aggregated.** The two pattern
sums of `fiber_card_four6` collected: the baselines
`480·A₃B³` and `1080·A₂²B²` (which enter
`kappa6Const` at the card-4 count), the order-4
excess dressed at `5760·d⁻⁴` (`1440` from the tripled
patterns, `4320` from the doubled-doubled patterns),
the doubled excess at `−1440·d⁻⁵` (`−360` and `−1080`:
in the doubled-doubled patterns each doubled column
appears in six ordered pairs), the tripled excess at
`120·d⁻⁶`, and the doubled-doubled excess at
`90·d⁻⁶`. -/
theorem fiber_card_four_agg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 480 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        + 1080 * ((densMomentValue ρ μG 2) ^ 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
        + 5760 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 1440 * ((d : ℝ)⁻¹) ^ 5
          * ∑ X ∈ C, (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 120 * ((d : ℝ)⁻¹) ^ 6
          * ∑ X ∈ C, (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 90 * ((d : ℝ)⁻¹) ^ 6
          * ∑ X ∈ C, ∑ Y ∈ C.erase X,
            (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
  classical
  have herase3 : ∀ X ∈ C, (C.erase X).card = 3 := by
    intro X hX
    rw [Finset.card_erase_of_mem hX, hC]
  have hfD : ∑ X ∈ C, (3 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (3 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ X ∈ C, (doubledQuadReMoment ρ μG C X u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [← Finset.mul_sum]
  have hfT : ∑ X ∈ C, (((d : ℝ)⁻¹) ^ 6)
        * (tripledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      = (((d : ℝ)⁻¹) ^ 6)
        * ∑ X ∈ C, (tripledQuadReMoment ρ μG C X u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    rw [← Finset.mul_sum]
  have hS1 : ∑ X ∈ C, (120 : ℝ)
        * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = 480 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        + 1440 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 360 * ((d : ℝ)⁻¹) ^ 5
          * ∑ X ∈ C, (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 120 * ((d : ℝ)⁻¹) ^ 6
          * ∑ X ∈ C, (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have h := sum_mul_add_sub_add C (120 : ℝ)
      (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
      (3 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      (fun X => 3 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      (fun X => ((d : ℝ)⁻¹) ^ 6
        * (tripledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
    rw [hfD, hfT, hC, Nat.cast_ofNat] at h
    exact h.trans (by ring)
  have hfDi : ∀ X ∈ C, ∑ Y ∈ C.erase X, (2 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C Y u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (2 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ Y ∈ C.erase X, (doubledQuadReMoment ρ μG C Y u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    intro X _
    rw [← Finset.mul_sum]
  have hfEi : ∀ X ∈ C, ∑ Y ∈ C.erase X, (((d : ℝ)⁻¹) ^ 6)
        * (doubledDoubledQuadReMoment ρ μG C X Y u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
      = (((d : ℝ)⁻¹) ^ 6)
        * ∑ Y ∈ C.erase X,
          (doubledDoubledQuadReMoment ρ μG C X Y u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    intro X _
    rw [← Finset.mul_sum]
  have hS2inner : ∀ X ∈ C, ∑ Y ∈ C.erase X, (90 : ℝ)
        * ((densMomentValue ρ μG 2) ^ 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Y u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 90 * (3 * ((densMomentValue ρ μG 2) ^ 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
          + 3 * (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
          - 3 * (2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C X u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
          - (2 * ((d : ℝ)⁻¹) ^ 5)
            * ∑ Y ∈ C.erase X, (doubledQuadReMoment ρ μG C Y u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ Y ∈ C.erase X,
              (doubledDoubledQuadReMoment ρ μG C X Y u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    intro X hX
    have h := sum_mul_add_sub_sub_add (C.erase X) (90 : ℝ)
      ((densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
      (4 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      (2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      (fun Y => 2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C Y u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      (fun Y => ((d : ℝ)⁻¹) ^ 6
        * (doubledDoubledQuadReMoment ρ μG C X Y u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
    rw [hfDi X hX, hfEi X hX, herase3 X hX, Nat.cast_ofNat] at h
    exact h
  have hfc : ∑ X ∈ C, 3 * (2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = (3 * (2 * ((d : ℝ)⁻¹) ^ 5))
        * ∑ X ∈ C, (doubledQuadReMoment ρ μG C X u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hfd : ∑ X ∈ C, (2 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ Y ∈ C.erase X, (doubledQuadReMoment ρ μG C Y u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (2 * ((d : ℝ)⁻¹) ^ 5)
        * (3 * ∑ Y ∈ C, (doubledQuadReMoment ρ μG C Y u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    rw [← Finset.mul_sum, sum_sum_erase_eq]
    simp only [hC, Nat.cast_ofNat]
    ring
  have hfe : ∑ X ∈ C, (((d : ℝ)⁻¹) ^ 6)
        * ∑ Y ∈ C.erase X,
          (doubledDoubledQuadReMoment ρ μG C X Y u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
      = (((d : ℝ)⁻¹) ^ 6)
        * ∑ X ∈ C, ∑ Y ∈ C.erase X,
          (doubledDoubledQuadReMoment ρ μG C X Y u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    rw [← Finset.mul_sum]
  have hS2 : ∑ X ∈ C, ∑ Y ∈ C.erase X, (90 : ℝ)
        * ((densMomentValue ρ μG 2) ^ 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + 4 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C Y u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 1080 * ((densMomentValue ρ μG 2) ^ 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
        + 4320 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 1080 * ((d : ℝ)⁻¹) ^ 5
          * ∑ X ∈ C, (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 90 * ((d : ℝ)⁻¹) ^ 6
          * ∑ X ∈ C, ∑ Y ∈ C.erase X,
            (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    have h := sum_mul_add_sub_sub_add_fn C (90 : ℝ)
      (3 * ((densMomentValue ρ μG 2) ^ 2
        * (1 - e1 ρ μG / (d : ℝ)) ^ 2))
      (3 * (4 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)))
      (fun X => 3 * (2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)))
      (fun X => (2 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ Y ∈ C.erase X, (doubledQuadReMoment ρ μG C Y u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      (fun X => ((d : ℝ)⁻¹) ^ 6
        * ∑ Y ∈ C.erase X,
          (doubledDoubledQuadReMoment ρ μG C X Y u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
    rw [hfc, hfd, hfe, hC, Nat.cast_ofNat] at h
    have hpre : ∑ X ∈ C, ∑ Y ∈ C.erase X, (90 : ℝ)
          * ((densMomentValue ρ μG 2) ^ 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + 4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C X u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C Y u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG C X Y u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
        = ∑ X ∈ C, 90 * (3 * ((densMomentValue ρ μG 2) ^ 2
                * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
            + 3 * (4 * ((d : ℝ)⁻¹) ^ 4
                * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
            - 3 * (2 * ((d : ℝ)⁻¹) ^ 5
                * (doubledQuadReMoment ρ μG C X u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
            - (2 * ((d : ℝ)⁻¹) ^ 5)
              * ∑ Y ∈ C.erase X, (doubledQuadReMoment ρ μG C Y u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ Y ∈ C.erase X,
                (doubledDoubledQuadReMoment ρ μG C X Y u u'
                  - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) :=
      Finset.sum_congr rfl hS2inner
    rw [hpre]
    exact h.trans (by ring)
  rw [fiber_card_four6 ρ μG hN hN3 hρcont u u' C hC, hS1, hS2]
  ring

/-- **The card-5 fiber, aggregated.** The five doubled
patterns of `fiber_card_five6` collected: the baseline
`1800·A₂B⁴` (which enters `kappa6Const` at the
card-5 count), the order-4 erasure excess dressed at
`3240·d⁻⁴` (`360` from the erased support itself,
`2880 = 360·2·(5−1)` from the erasure double sum over
the other four erasures), the doubled erasure excess
at `−360·d⁻⁵`, the fivefold excess at `−3600·d⁻⁵`,
and the doubled fivefold excess at `360·d⁻⁶`. -/
theorem fiber_card_five_agg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1800 * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4)
        + 3240 * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C, (quadReMoment ρ μG (C.erase x) u u'
              - (e1 ρ μG) ^ 4)
        - 360 * ((d : ℝ)⁻¹) ^ 5
          * ∑ P ∈ C, ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3600 * ((d : ℝ)⁻¹) ^ 5
          * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 360 * ((d : ℝ)⁻¹) ^ 6
          * ∑ P ∈ C, (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
  classical
  have hc : ∑ P ∈ C, (((d : ℝ)⁻¹) ^ 4)
        * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
      = (((d : ℝ)⁻¹) ^ 4)
        * ∑ P ∈ C, (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4) := by
    rw [← Finset.mul_sum]
  have hd : ∑ P ∈ C, (2 * ((d : ℝ)⁻¹) ^ 4)
        * ∑ x ∈ C.erase P, (quadReMoment ρ μG (C.erase x) u u'
          - (e1 ρ μG) ^ 4)
      = (2 * ((d : ℝ)⁻¹) ^ 4)
        * (4 * ∑ x ∈ C, (quadReMoment ρ μG (C.erase x) u u'
            - (e1 ρ μG) ^ 4)) := by
    rw [← Finset.mul_sum, sum_sum_erase_eq]
    simp only [hC, Nat.cast_ofNat]
    ring
  have he : ∑ P ∈ C, (((d : ℝ)⁻¹) ^ 5)
        * ∑ x ∈ C.erase P,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (((d : ℝ)⁻¹) ^ 5)
        * ∑ P ∈ C, ∑ x ∈ C.erase P,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [← Finset.mul_sum]
  have hf : ∑ P ∈ C, (((d : ℝ)⁻¹) ^ 6)
        * (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = (((d : ℝ)⁻¹) ^ 6)
        * ∑ P ∈ C, (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    rw [← Finset.mul_sum]
  have h := sum_mul_add_add_sub_sub_add C (360 : ℝ)
    (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4)
    (2 * ((d : ℝ)⁻¹) ^ 5 * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))
    (fun P => ((d : ℝ)⁻¹) ^ 4
      * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4))
    (fun P => 2 * ((d : ℝ)⁻¹) ^ 4
      * ∑ x ∈ C.erase P, (quadReMoment ρ μG (C.erase x) u u'
        - (e1 ρ μG) ^ 4))
    (fun P => ((d : ℝ)⁻¹) ^ 5
      * ∑ x ∈ C.erase P,
        (doubledQuadReMoment ρ μG (C.erase x) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
    (fun P => ((d : ℝ)⁻¹) ^ 6
      * (doubledPentaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
  rw [hc, hd, he, hf, hC, Nat.cast_ofNat] at h
  have hpre : ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
        (fun k => multSupport k = C),
      ((Nat.multinomial Finset.univ k : ℝ))
        * ∫ α : LayerSite N → G,
            ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
            ∂(Measure.pi fun _ : LayerSite N => μG)
    = ∑ P ∈ C, (360 : ℝ)
        * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
          + ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * ∑ x ∈ C.erase P,
              (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ x ∈ C.erase P,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) :=
    fiber_card_five6 ρ μG hN hN3 hρcont u u' C hC
  rw [hpre]
  exact h.trans (by ring)

/-- **The total sixth moment, assembled.** The
integrated multinomial expansion, grouped by support
card, in fiber language: cards `1, 2, 3` give exactly
`kappa6Const`'s constant patterns (through the
falling-factorial choose identities); card `4` gives
its two baselines into `kappa6Const` (the `(3,1,1,1)`
baseline `20·M(M−1)(M−2)(M−3)·A₃B³` and the
`(2,2,1,1)` baseline `45·M(M−1)(M−2)(M−3)·A₂²B²`)
plus the aggregated excesses of `fiber_card_four_agg`;
card `5` gives its baseline
`15·M(M−1)(M−2)(M−3)(M−4)·A₂B⁴` into `kappa6Const`
plus the aggregated excesses of `fiber_card_five_agg`;
card `6` gives its baseline `M(M−1)⋯(M−5)·B⁶` into
`kappa6Const` plus `720` times the sextuple excess
levels: the order-4 subset excesses at `d⁻⁴`, the
order-5 subset excesses at `−d⁻⁵`, and the sixfold
excess at `d⁻⁶` (whose own sum splits by the
classification, `sum_powersetCard_six_hexaExcess_split`).
Every coefficient is as it emerges from the fiber
lemmas. No `kappa6dep` identity and no sign is
asserted. -/
theorem betaCoeff6_total (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 6
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = kappa6Const (N := N) ρ μG
        + 5760 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 1440 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 120 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 90 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            ∑ Y ∈ C.erase X,
            (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 3240 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        - 360 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
            ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3600 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 5,
            (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 360 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
            (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 720 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - 720 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + 720 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 6,
            (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
  classical
  have hch2 : ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ))
      = colCount N * (colCount N - 1) / 2 := by
    have h := cast_factorial_mul_choose6 (N := N) 2
    have hprod : (∏ i ∈ Finset.range 2, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) := by
      have e0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have e1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_zero, e0, e1]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch3 : ((Nat.choose (Fintype.card (LayerColumn N)) 3 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2) / 6 := by
    have h := cast_factorial_mul_choose6 (N := N) 3
    have hprod : (∏ i ∈ Finset.range 3, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2) := by
      have e0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have e1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_zero, e0, e1, e2]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch4 : ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2)
        * (colCount N - 3) / 24 := by
    have h := cast_factorial_mul_choose6 (N := N) 4
    have hprod : (∏ i ∈ Finset.range 4, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2)
          * (colCount N - 3) := by
      have e0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have e1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      have e3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_zero, e0, e1, e2, e3]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (24 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch5 : ((Nat.choose (Fintype.card (LayerColumn N)) 5 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2)
        * (colCount N - 3) * (colCount N - 4) / 120 := by
    have h := cast_factorial_mul_choose6 (N := N) 5
    have hprod : (∏ i ∈ Finset.range 5, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2)
          * (colCount N - 3) * (colCount N - 4) := by
      have e0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have e1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      have e3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_zero, e0, e1,
        e2, e3, e4]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (120 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch6 : ((Nat.choose (Fintype.card (LayerColumn N)) 6 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2)
        * (colCount N - 3) * (colCount N - 4) * (colCount N - 5)
        / 720 := by
    have h := cast_factorial_mul_choose6 (N := N) 6
    have hprod : (∏ i ∈ Finset.range 6, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2)
          * (colCount N - 3) * (colCount N - 4) * (colCount N - 5) := by
      have e0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have e1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      have e3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      have e5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_zero, e0, e1, e2, e3, e4, e5]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (720 : ℝ) ≠ 0), mul_comm]
    exact h
  have hG0 : ∑ C ∈ Finset.univ.powersetCard 0,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = 0 := by
    rw [Finset.powersetCard_zero, Finset.sum_singleton,
      fiber6_eq_empty_of_card_ne ∅ (Or.inl Finset.card_empty),
      Finset.sum_empty]
  have hG1 : ∑ C ∈ Finset.univ.powersetCard 1,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = colCount N * densMomentValue ρ μG 6 := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_one6 ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Nat.choose_one_right, nsmul_eq_mul]
    rfl
  have hG2 : ∑ C ∈ Finset.univ.powersetCard 2,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ))
        * (6 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 5)
          + 15 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 4)
          + 20 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 3)
          + 15 * (densMomentValue ρ μG 4 * densMomentValue ρ μG 2)
          + 6 * (densMomentValue ρ μG 5 * densMomentValue ρ μG 1)) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_two6 ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hG3 : ∑ C ∈ Finset.univ.powersetCard 3,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 3 : ℝ))
        * (30 * (densMomentValue ρ μG 4
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
          + 30 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 4 * densMomentValue ρ μG 1))
          + 30 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4))
          + 60 * (densMomentValue ρ μG 3
            * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
          + 60 * (densMomentValue ρ μG 3
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
          + 60 * (densMomentValue ρ μG 2
            * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
          + 60 * (densMomentValue ρ μG 2
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
          + 60 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2))
          + 60 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3))
          + 90 * (densMomentValue ρ μG 2
            * (densMomentValue ρ μG 2 * densMomentValue ρ μG 2))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_three6 ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hG4 : ∑ C ∈ Finset.univ.powersetCard 4,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
          * (480 * (densMomentValue ρ μG 3
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
        + ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
          * (1080 * ((densMomentValue ρ μG 2) ^ 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2))
        + 5760 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 1440 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            (doubledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 120 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            (tripledQuadReMoment ρ μG C X u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 90 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 4, ∑ X ∈ C,
            ∑ Y ∈ C.erase X,
            (doubledDoubledQuadReMoment ρ μG C X Y u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_four_agg ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hG5 : ∑ C ∈ Finset.univ.powersetCard 5,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 5 : ℝ))
          * (1800 * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 4))
        + 3240 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        - 360 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
            ∑ x ∈ C.erase P,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3600 * ((d : ℝ)⁻¹) ^ 5
          * ∑ C ∈ Finset.univ.powersetCard 5,
            (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 360 * ((d : ℝ)⁻¹) ^ 6
          * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
            (doubledPentaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_five_agg ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const]
    simp only [Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hC6 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG))
      = 720 * (1 - e1 ρ μG / (d : ℝ)) ^ 6
        + (720 * ((d : ℝ)⁻¹) ^ 4)
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - (720 * ((d : ℝ)⁻¹) ^ 5)
          * ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + (720 * ((d : ℝ)⁻¹) ^ 6)
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    intro C hC
    rw [fiber_card_six ρ μG hN hN3 hρcont u u' C
      (Finset.mem_powersetCard.mp hC).2]
    ring
  have hG6 : ∑ C ∈ Finset.univ.powersetCard 6,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
            (fun k => multSupport k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 6 : ℝ))
          * (720 * (1 - e1 ρ μG / (d : ℝ)) ^ 6)
        + (720 * ((d : ℝ)⁻¹) ^ 4)
          * ∑ C ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - (720 * ((d : ℝ)⁻¹) ^ 5)
          * ∑ C ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + (720 * ((d : ℝ)⁻¹) ^ 6)
          * ∑ C ∈ Finset.univ.powersetCard 6,
            (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    rw [Finset.sum_congr rfl hC6, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const]
    simp only [Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hFibVanish : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 7 ≤ C.card →
      (∑ k ∈ (Finset.piAntidiag Finset.univ 6).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)) = 0 := by
    intro C hC
    rw [fiber6_eq_empty_of_card_ne C hC, Finset.sum_empty]
  rw [integral_layerDensSum_pow_six ρ μG hN hρcont u u',
    sum_piAntidiag6_fiberwise,
    sum_powerset_eq_sum_cards6 _ hFibVanish]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hG0, hG1, hG2, hG3, hG4, hG5, hG6]
  unfold kappa6Const
  rw [hch2, hch3, hch4, hch5, hch6, densMomentValue_one]
  ring
end Assembly6Total

/-! ## B6-2c: the assembly identity for `κ₆^dep`

The fiber sums of `betaCoeff6_total` converted through
the dictionaries: `kappa4dep_eq` (order 4),
`kappa5dep_eq` + `kappa5chanExcess_eq` (order 5), the
four channel excesses of B6-2a, the fivefold excess
factorization, and the sixfold split of B6-2b-iii.
**An identity, not a sign: NO sign is asserted for
`kappa6dep` or for any channel; the β⁶ general sign
stays FRONTIER. NO CLAIM; dials 0/4.**

**Named differences from the predicted shape**
(`A₅·κ₅^dep + A₄·κ₄^dep + Σ_ch c_ch·Excess_ch` with
`A₅, A₄` polynomials in `M = colCount N` and
`B = 1 − e₁/d` only), recorded at full rank:
(i) `A₅` is exactly the order-5 dressing factor
`4 + (M−4)·B` — no difference there — but `A₄`
carries one piece that is **not** a polynomial in
`M, B`: the term `½·(M−4)·μ₂/d²`, produced by the
doubled-penta fiber: at a 5-support the private
column, when it is the doubled one, strips off
`realMoment 2` (not a power of `B`), and its
erasure excess sums to `(M−4)·Φ₄`.
(ii) There is an **extra term** beyond the four
channel excesses: `−d⁻⁶·e₁²` times the sum, over
`Θ(2,2,2)` supports `C`, of the order-4 excesses of
`C`'s 4-subsets. It comes from the private-column
(rest) part of the sixfold split: at a rest support
the sixfold excess is `e₁²` times the sum of its
4-subset excesses, and summing that over the rest
family leaves the `Θ` family's 4-subset excess sum
unabsorbed — a `Θ` support's rectangle 4-subsets
are primitive quads, so this sum does not reduce
to a multiple of `κ₄^dep` by any counting the
corpus owns (a `C₆` support, by contrast, has no
primitive 4-subset at all: its 4-subset excess sum
vanishes, proved below). The `C₆` and `Θ` channel
excesses themselves enter at the clean weight
`d⁻⁶`, the `(3,1,1,1)` excess at `d⁻⁶/6`, and the
`(2,2,1,1)` excess at `d⁻⁶/8`. -/

section Assembly6Close

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **Distinct-pair double sums swap.** Summing over
ordered pairs of distinct columns in either order
gives the same total. -/
theorem sum_sum_erase_swap (C : Finset (LayerColumn N))
    (g : LayerColumn N → LayerColumn N → ℝ) :
    ∑ x ∈ C, ∑ y ∈ C.erase x, g x y
      = ∑ y ∈ C, ∑ x ∈ C.erase y, g x y := by
  classical
  have h : ∀ x ∈ C, ∑ y ∈ C.erase x, g x y
      = ∑ y ∈ C, (if y ≠ x then g x y else 0) := by
    intro x _
    rw [← Finset.filter_ne', Finset.sum_filter]
  have h' : ∀ y ∈ C, ∑ x ∈ C.erase y, g x y
      = ∑ x ∈ C, (if x ≠ y then g x y else 0) := by
    intro y _
    rw [← Finset.filter_ne', Finset.sum_filter]
  rw [Finset.sum_congr rfl h, Finset.sum_congr rfl h',
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_pos (Ne.symm hxy), if_pos hxy]

/-- **Erasure counting, 5 → 4 (generic).** Summing a
support function over the erasures of all 5-supports
counts each 4-support `colCount N − 4` times: the
complements of a fixed 4-support. (The generic form
of `sum_powersetCard_five_erase_excess`.) -/
theorem sum_powersetCard_five_erase_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C, g (C.erase x)
      = (colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4, g T := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 5,
      ∑ x ∈ C, g (C.erase x)
        = ∑ x ∈ Finset.univ, (if x ∈ C then g (C.erase x)
            else 0) := fun C _ =>
    (Finset.sum_congr rfl (fun x hx => (if_pos hx).symm)).trans
      (Finset.sum_subset (Finset.subset_univ C)
        (fun x _ hx => if_neg hx))
  have step2 : ∀ x : LayerColumn N,
      ∑ C ∈ Finset.univ.powersetCard 5, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ T ∈ Finset.univ.powersetCard 4, (if x ∈ T then 0
          else g T) := by
    intro x
    have hA : ∑ C ∈ Finset.univ.powersetCard 5, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ C ∈ (Finset.univ.powersetCard 5).filter
          (fun C => x ∈ C), g (C.erase x) :=
      (Finset.sum_filter _ _).symm
    have hB : ∑ T ∈ Finset.univ.powersetCard 4, (if x ∈ T then 0
          else g T)
      = ∑ T ∈ (Finset.univ.powersetCard 4).filter
          (fun T => x ∉ T), g T := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hxT : x ∈ T <;> simp [hxT]
    rw [hA, hB]
    refine Finset.sum_bij (fun C _ => C.erase x) ?_ ?_ ?_ ?_
    · intro C hC
      have hC5 : C ∈ Finset.univ.powersetCard 5 :=
        (Finset.mem_filter.mp hC).1
      have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powersetCard.mpr
        ⟨(Finset.erase_subset x C).trans (Finset.subset_univ C),
          by
          rw [Finset.card_erase_of_mem hxC,
            (Finset.mem_powersetCard.mp hC5).2]⟩, ?_⟩
      exact fun h => (Finset.mem_erase.mp h).1 rfl
    · intro C hC C' hC' h
      have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
      have hxC' : x ∈ C' := (Finset.mem_filter.mp hC').2
      have h1 : insert x (C.erase x) = C :=
        Finset.insert_erase hxC
      have h2 : insert x (C'.erase x) = C' :=
        Finset.insert_erase hxC'
      rw [← h1, ← h2, h]
    · intro T hT
      have hT4 : T ∈ Finset.univ.powersetCard 4 :=
        (Finset.mem_filter.mp hT).1
      have hxT : x ∉ T := (Finset.mem_filter.mp hT).2
      refine ⟨insert x T, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset (Finset.mem_univ x)
            (Finset.mem_powersetCard.mp hT4).1, by
            rw [Finset.card_insert_of_notMem hxT,
              (Finset.mem_powersetCard.mp hT4).2]⟩,
          Finset.mem_insert_self x T⟩
      · exact Finset.erase_insert hxT
    · intro C _
      rfl
  have step3 : ∀ T ∈ Finset.univ.powersetCard 4,
      ∑ x ∈ Finset.univ, (if x ∈ T then (0 : ℝ) else g T)
        = (colCount N - 4) * g T := by
    intro T hT
    have hT4 : T.card = 4 := (Finset.mem_powersetCard.mp hT).2
    have h4M : 4 ≤ Fintype.card (LayerColumn N) := by
      have hle := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, hT4] at hle
    have hform : ∀ x : LayerColumn N,
        (if x ∈ T then (0 : ℝ) else g T)
        = (if x ∉ T then g T else 0) := fun x => (ite_not _ _ _).symm
    rw [Finset.sum_congr rfl (fun x _ => hform x),
      ← Finset.sum_filter, Finset.sum_const]
    have hcard : (Finset.univ.filter (fun x => x ∉ T)).card
        = Fintype.card (LayerColumn N) - 4 := by
      have hset : Finset.univ.filter (fun x => x ∉ T)
          = Finset.univ \ T := by
        refine Finset.ext fun x => ?_
        simp [Finset.mem_sdiff]
      rw [hset, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hT4]
    rw [hcard, nsmul_eq_mul, Nat.cast_sub h4M, Nat.cast_ofNat]
    rfl
  rw [Finset.sum_congr rfl step1, Finset.sum_comm,
    Finset.sum_congr rfl (fun x _ => step2 x), Finset.sum_comm,
    Finset.sum_congr rfl step3, ← Finset.mul_sum]

/-- **Erasure counting, 6 → 5 (generic).** Summing a
support function over the erasures of all 6-supports
counts each 5-support `colCount N − 5` times. -/
theorem sum_powersetCard_six_erase_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ x ∈ C, g (C.erase x)
      = (colCount N - 5) * ∑ T ∈ Finset.univ.powersetCard 5, g T := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 6,
      ∑ x ∈ C, g (C.erase x)
        = ∑ x ∈ Finset.univ, (if x ∈ C then g (C.erase x)
            else 0) := fun C _ =>
    (Finset.sum_congr rfl (fun x hx => (if_pos hx).symm)).trans
      (Finset.sum_subset (Finset.subset_univ C)
        (fun x _ hx => if_neg hx))
  have step2 : ∀ x : LayerColumn N,
      ∑ C ∈ Finset.univ.powersetCard 6, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ T ∈ Finset.univ.powersetCard 5, (if x ∈ T then 0
          else g T) := by
    intro x
    have hA : ∑ C ∈ Finset.univ.powersetCard 6, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ C ∈ (Finset.univ.powersetCard 6).filter
          (fun C => x ∈ C), g (C.erase x) :=
      (Finset.sum_filter _ _).symm
    have hB : ∑ T ∈ Finset.univ.powersetCard 5, (if x ∈ T then 0
          else g T)
      = ∑ T ∈ (Finset.univ.powersetCard 5).filter
          (fun T => x ∉ T), g T := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hxT : x ∈ T <;> simp [hxT]
    rw [hA, hB]
    refine Finset.sum_bij (fun C _ => C.erase x) ?_ ?_ ?_ ?_
    · intro C hC
      have hC6 : C ∈ Finset.univ.powersetCard 6 :=
        (Finset.mem_filter.mp hC).1
      have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powersetCard.mpr
        ⟨(Finset.erase_subset x C).trans (Finset.subset_univ C),
          by
          rw [Finset.card_erase_of_mem hxC,
            (Finset.mem_powersetCard.mp hC6).2]⟩, ?_⟩
      exact fun h => (Finset.mem_erase.mp h).1 rfl
    · intro C hC C' hC' h
      have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
      have hxC' : x ∈ C' := (Finset.mem_filter.mp hC').2
      have h1 : insert x (C.erase x) = C :=
        Finset.insert_erase hxC
      have h2 : insert x (C'.erase x) = C' :=
        Finset.insert_erase hxC'
      rw [← h1, ← h2, h]
    · intro T hT
      have hT5 : T ∈ Finset.univ.powersetCard 5 :=
        (Finset.mem_filter.mp hT).1
      have hxT : x ∉ T := (Finset.mem_filter.mp hT).2
      refine ⟨insert x T, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset (Finset.mem_univ x)
            (Finset.mem_powersetCard.mp hT5).1, by
            rw [Finset.card_insert_of_notMem hxT,
              (Finset.mem_powersetCard.mp hT5).2]⟩,
          Finset.mem_insert_self x T⟩
      · exact Finset.erase_insert hxT
    · intro C _
      rfl
  have step3 : ∀ T ∈ Finset.univ.powersetCard 5,
      ∑ x ∈ Finset.univ, (if x ∈ T then (0 : ℝ) else g T)
        = (colCount N - 5) * g T := by
    intro T hT
    have hT5 : T.card = 5 := (Finset.mem_powersetCard.mp hT).2
    have h5M : 5 ≤ Fintype.card (LayerColumn N) := by
      have hle := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, hT5] at hle
    have hform : ∀ x : LayerColumn N,
        (if x ∈ T then (0 : ℝ) else g T)
        = (if x ∉ T then g T else 0) := fun x => (ite_not _ _ _).symm
    rw [Finset.sum_congr rfl (fun x _ => hform x),
      ← Finset.sum_filter, Finset.sum_const]
    have hcard : (Finset.univ.filter (fun x => x ∉ T)).card
        = Fintype.card (LayerColumn N) - 5 := by
      have hset : Finset.univ.filter (fun x => x ∉ T)
          = Finset.univ \ T := by
        refine Finset.ext fun x => ?_
        simp [Finset.mem_sdiff]
      rw [hset, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hT5]
    rw [hcard, nsmul_eq_mul, Nat.cast_sub h5M, Nat.cast_ofNat]
    rfl
  rw [Finset.sum_congr rfl step1, Finset.sum_comm,
    Finset.sum_congr rfl (fun x _ => step2 x), Finset.sum_comm,
    Finset.sum_congr rfl step3, ← Finset.mul_sum]

/-- **5-subsets of a 6-support are its erasures.**
Summing over the 5-subsets of a 6-support is summing
over the erased column. -/
theorem sum_powersetCard_five_subset_eq_sum_erase
    (C : Finset (LayerColumn N)) (hC : C.card = 6)
    (f : Finset (LayerColumn N) → ℝ) :
    ∑ D ∈ Finset.powersetCard 5 C, f D
      = ∑ x ∈ C, f (C.erase x) := by
  classical
  refine (Finset.sum_bij (fun x _ => C.erase x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.erase_subset x C, by
        rw [Finset.card_erase_of_mem hx, hC]⟩
  · intro x _ x' hx' h
    by_contra hne
    have hmem : x' ∈ C.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, hx'⟩
    rw [h] at hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  · intro D hD
    have hsub : D ⊆ C := (Finset.mem_powersetCard.mp hD).1
    have hcard : D.card = 5 := (Finset.mem_powersetCard.mp hD).2
    have hsdcard : (C \ D).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hC, hcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsdcard
    have hxCD : x ∈ C \ D := by
      rw [hx]; exact Finset.mem_singleton_self x
    have hxC : x ∈ C := (Finset.mem_sdiff.mp hxCD).1
    have hxD : x ∉ D := (Finset.mem_sdiff.mp hxCD).2
    refine ⟨x, hxC, ?_⟩
    refine Finset.ext fun z => ?_
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hzx, hzC⟩
      by_contra hzD
      have hz : z ∈ C \ D := Finset.mem_sdiff.mpr ⟨hzC, hzD⟩
      rw [hx, Finset.mem_singleton] at hz
      exact hzx hz
    · intro hzD
      exact ⟨fun h => hxD (h ▸ hzD), hsub hzD⟩
  · intro x _
    rfl

/-- **4-subsets of a 5-support are its erasures.** -/
theorem sum_powersetCard_four_subset_eq_sum_erase
    (C : Finset (LayerColumn N)) (hC : C.card = 5)
    (f : Finset (LayerColumn N) → ℝ) :
    ∑ D ∈ Finset.powersetCard 4 C, f D
      = ∑ x ∈ C, f (C.erase x) := by
  classical
  refine (Finset.sum_bij (fun x _ => C.erase x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.erase_subset x C, by
        rw [Finset.card_erase_of_mem hx, hC]⟩
  · intro x _ x' hx' h
    by_contra hne
    have hmem : x' ∈ C.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, hx'⟩
    rw [h] at hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  · intro D hD
    have hsub : D ⊆ C := (Finset.mem_powersetCard.mp hD).1
    have hcard : D.card = 4 := (Finset.mem_powersetCard.mp hD).2
    have hsdcard : (C \ D).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hC, hcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsdcard
    have hxCD : x ∈ C \ D := by
      rw [hx]; exact Finset.mem_singleton_self x
    have hxC : x ∈ C := (Finset.mem_sdiff.mp hxCD).1
    have hxD : x ∉ D := (Finset.mem_sdiff.mp hxCD).2
    refine ⟨x, hxC, ?_⟩
    refine Finset.ext fun z => ?_
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hzx, hzC⟩
      by_contra hzD
      have hz : z ∈ C \ D := Finset.mem_sdiff.mpr ⟨hzC, hzD⟩
      rw [hx, Finset.mem_singleton] at hz
      exact hzx hz
    · intro hzD
      exact ⟨fun h => hxD (h ▸ hzD), hsub hzD⟩
  · intro x _
    rfl

/-- **Tripled excess vanishes off primitive quads.**
At a non-primitive 4-support `C` and `P ∈ C`,
`tripledQuadReMoment C P = μ₃e₁³`: take a private
column `X` of `C`. At `X = P` the tripled strip
leaves `μ₃` times a triple moment, which factors;
at `X ≠ P` the single strip leaves `e₁` times the
tripled moment of a triple, which factors by the
cardinality-≤-3 power factorization. (The mirror of
`doubledQuadReMoment_sub_eq_zero_of_not_primitive`.) -/
theorem tripledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P : LayerColumn N} (hP : P ∈ C) :
    tripledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 3 * (e1 ρ μG) ^ 3 = 0 := by
  classical
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  by_cases hXP : X = P
  · subst hXP
    rw [tripledQuadReMoment_strip_tripled ρ μG hN hN3 hρcont
      u u' hsX hpriv]
    have hcard3 : (C.erase X).card = 3 := by
      rw [Finset.card_erase_of_mem hXC, hC]
    show realMoment ρ μG 3 * (∫ α : LayerSite N → G,
        ∏ Q ∈ C.erase X, colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG))
      - realMoment ρ μG 3 * (e1 ρ μG) ^ 3 = 0
    rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
      u u' (C.erase X) (le_of_eq hcard3), hcard3]
    exact sub_self _
  · have hPX : P ∈ C.erase X :=
      Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
    rw [tripledQuadReMoment_strip_single ρ μG hN hN3 hρcont
      u u' hP hXC hXP hsX hpriv]
    have hcard3 : (C.erase X).card = 3 := by
      rw [Finset.card_erase_of_mem hXC, hC]
    have hfact : tripledQuadReMoment ρ μG (C.erase X) P u u'
        = realMoment ρ μG 3 * (e1 ρ μG) ^ 2 := by
      have hcong : ∀ α : LayerSite N → G,
          (colRe ρ u u' P α) ^ 3
              * ∏ Q ∈ (C.erase X).erase P, colRe ρ u u' Q α
            = ∏ Q ∈ C.erase X,
                (colRe ρ u u' Q α) ^ (if Q = P then 3 else 1) := by
        intro α
        rw [← Finset.mul_prod_erase (C.erase X)
          (fun Q => (colRe ρ u u' Q α) ^ (if Q = P then 3 else 1))
          hPX, if_pos rfl]
        refine congrArg _ ?_
        exact Finset.prod_congr rfl fun Q hQ => by
          rw [if_neg (Finset.mem_erase.mp hQ).1, pow_one]
      calc tripledQuadReMoment ρ μG (C.erase X) P u u'
          = ∫ α : LayerSite N → G,
              ∏ Q ∈ C.erase X,
                (colRe ρ u u' Q α) ^ (if Q = P then 3 else 1)
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
            integral_congr_ae (Filter.Eventually.of_forall hcong)
        _ = ∏ Q ∈ C.erase X,
              realMoment ρ μG (if Q = P then 3 else 1) :=
            integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
              hρcont u u' (C.erase X) (le_of_eq hcard3)
              (fun Q => if Q = P then 3 else 1)
        _ = realMoment ρ μG 3 * (e1 ρ μG) ^ 2 := by
            rw [← Finset.mul_prod_erase (C.erase X)
              (fun Q => realMoment ρ μG (if Q = P then 3 else 1))
              hPX, if_pos rfl]
            have h2 : ∀ Q ∈ (C.erase X).erase P,
                realMoment ρ μG (if Q = P then 3 else 1)
                  = e1 ρ μG := by
              intro Q hQ
              rw [if_neg (Finset.mem_erase.mp hQ).1,
                realMoment_one]
            rw [Finset.prod_congr rfl h2, Finset.prod_const]
            have h3 : ((C.erase X).erase P).card = 2 := by
              rw [Finset.card_erase_of_mem hPX,
                Finset.card_erase_of_mem hXC, hC]
            rw [h3]
    rw [hfact]
    ring

/-- **The powerset tripled-excess sum is the
`(3,1,1,1)` channel excess.** Over the full
`powersetCard 4`, the tripled-excess sum equals
`kappa6chan3111Excess`: off `primitiveQuads` every
term vanishes by the previous lemma. -/
theorem sum_powersetCard_four_tripled_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      = kappa6chan3111Excess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (tripledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro C hC
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, (Finset.mem_filter.mp hC).2.1⟩
  · intro C hCunivers hCnotprim
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hCunivers).2
    have hnp : ¬ IsPrimitiveQuad C := fun hp =>
      hCnotprim (Finset.mem_filter.mpr ⟨Finset.mem_univ C, hp⟩)
    rw [Finset.sum_eq_zero]
    intro P hP
    exact tripledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG
      hN hN3 hρcont u u' hcard hnp hP

/-- **Doubled-doubled excess vanishes off primitive
quads.** At a non-primitive 4-support `C` and
distinct `P, Q ∈ C`,
`doubledDoubledQuadReMoment C P Q = μ₂²e₁²`: take a
private column `X` of `C`. At `X = P` or `X = Q` a
doubled strip leaves `μ₂` times a doubled moment of
a triple, which factors; at `X` distinct from both,
the single strip leaves `e₁` times the
doubled-doubled moment of a triple, which factors
by the cardinality-≤-3 power factorization. -/
theorem doubledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P Q : LayerColumn N} (hP : P ∈ C) (hQ : Q ∈ C.erase P) :
    doubledDoubledQuadReMoment ρ μG C P Q u u'
      - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2 = 0 := by
  classical
  have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  have hfact : ∀ (D : Finset (LayerColumn N)) (hD : D.card = 3)
      (R : LayerColumn N) (hR : R ∈ D),
      doubledQuadReMoment ρ μG D R u u'
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
    intro D hD R hR
    have hcong : ∀ α : LayerSite N → G,
        (colRe ρ u u' R α) ^ 2
            * ∏ Z ∈ D.erase R, colRe ρ u u' Z α
          = ∏ Z ∈ D,
              (colRe ρ u u' Z α) ^ (if Z = R then 2 else 1) := by
      intro α
      rw [← Finset.mul_prod_erase D
        (fun Z => (colRe ρ u u' Z α) ^ (if Z = R then 2 else 1))
        hR, if_pos rfl]
      refine congrArg _ ?_
      exact Finset.prod_congr rfl fun Z hZ => by
        rw [if_neg (Finset.mem_erase.mp hZ).1, pow_one]
    calc doubledQuadReMoment ρ μG D R u u'
        = ∫ α : LayerSite N → G,
            ∏ Z ∈ D,
              (colRe ρ u u' Z α) ^ (if Z = R then 2 else 1)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_congr_ae (Filter.Eventually.of_forall hcong)
      _ = ∏ Z ∈ D, realMoment ρ μG (if Z = R then 2 else 1) :=
          integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
            hρcont u u' D (le_of_eq hD)
            (fun Z => if Z = R then 2 else 1)
      _ = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
          rw [← Finset.mul_prod_erase D
            (fun Z => realMoment ρ μG (if Z = R then 2 else 1))
            hR, if_pos rfl]
          have h2 : ∀ Z ∈ D.erase R,
              realMoment ρ μG (if Z = R then 2 else 1)
                = e1 ρ μG := by
            intro Z hZ
            rw [if_neg (Finset.mem_erase.mp hZ).1, realMoment_one]
          rw [Finset.prod_congr rfl h2, Finset.prod_const]
          have h3 : (D.erase R).card = 2 := by
            rw [Finset.card_erase_of_mem hR, hD]
          rw [h3]
  by_cases hXP : X = P
  · subst hXP
    rw [doubledDoubledQuadReMoment_strip_first ρ μG hN hN3
      hρcont u u' hQC hQP hsX hpriv,
      hfact (C.erase X) (by
        rw [Finset.card_erase_of_mem hXC, hC]) Q hQ]
    ring
  · by_cases hXQ : X = Q
    · subst hXQ
      rw [doubledDoubledQuadReMoment_strip_second ρ μG hN hN3
        hρcont u u' hP hQP hsX hpriv,
        hfact (C.erase X) (by
          rw [Finset.card_erase_of_mem hXC, hC]) P
          (Finset.mem_erase.mpr ⟨fun h => hQP h.symm, hP⟩)]
      ring
    · have hQD : Q ∈ (C.erase X).erase P :=
        Finset.mem_erase.mpr ⟨hQP, Finset.mem_erase.mpr
          ⟨Ne.symm hXQ, hQC⟩⟩
      have hPD : P ∈ C.erase X :=
        Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
      rw [doubledDoubledQuadReMoment_strip_single ρ μG hN hN3
        hρcont u u' hP hQC hXC hXP hXQ hQP hsX hpriv]
      have hcard3 : (C.erase X).card = 3 := by
        rw [Finset.card_erase_of_mem hXC, hC]
      have hfact2 : doubledDoubledQuadReMoment ρ μG
            (C.erase X) P Q u u'
          = (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) := by
        have hcong : ∀ α : LayerSite N → G,
            (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
                * ∏ R ∈ ((C.erase X).erase P).erase Q,
                  colRe ρ u u' R α
              = ∏ R ∈ C.erase X, (colRe ρ u u' R α)
                  ^ (if R = P then 2 else if R = Q then 2 else 1) := by
          intro α
          have hrest : ∏ R ∈ ((C.erase X).erase P).erase Q,
                colRe ρ u u' R α
              = ∏ R ∈ ((C.erase X).erase P).erase Q,
                (colRe ρ u u' R α)
                  ^ (if R = P then 2 else if R = Q then 2 else 1) :=
            Finset.prod_congr rfl fun R hR => by
              have hRP : R ≠ P :=
                (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
              have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
              rw [if_neg hRP, if_neg hRQ, pow_one]
          rw [hrest,
            ← Finset.mul_prod_erase (C.erase X)
            (fun R => (colRe ρ u u' R α)
              ^ (if R = P then 2 else if R = Q then 2 else 1)) hPD,
            ← Finset.mul_prod_erase ((C.erase X).erase P)
            (fun R => (colRe ρ u u' R α)
              ^ (if R = P then 2 else if R = Q then 2 else 1)) hQD,
            if_pos rfl, if_neg hQP, if_pos rfl]
          ring
        calc doubledDoubledQuadReMoment ρ μG (C.erase X) P Q u u'
            = ∫ α : LayerSite N → G,
                ∏ R ∈ C.erase X, (colRe ρ u u' R α)
                    ^ (if R = P then 2 else if R = Q then 2 else 1)
                ∂(Measure.pi fun _ : LayerSite N => μG) :=
              integral_congr_ae (Filter.Eventually.of_forall hcong)
          _ = ∏ R ∈ C.erase X, realMoment ρ μG
                (if R = P then 2 else if R = Q then 2 else 1) :=
              integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
                hρcont u u' (C.erase X) (le_of_eq hcard3)
                (fun R => if R = P then 2 else if R = Q then 2
                  else 1)
          _ = (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) := by
              have haP : (if P = P then 2 else if P = Q then 2
                  else 1) = 2 := if_pos rfl
              have haQ : (if Q = P then 2 else if Q = Q then 2
                  else 1) = 2 := (if_neg hQP).trans (if_pos rfl)
              rw [← Finset.mul_prod_erase (C.erase X)
                (fun R => realMoment ρ μG
                  (if R = P then 2 else if R = Q then 2 else 1))
                hPD, haP,
                ← Finset.mul_prod_erase ((C.erase X).erase P)
                (fun R => realMoment ρ μG
                  (if R = P then 2 else if R = Q then 2 else 1))
                hQD, haQ]
              have h1 : ∀ R ∈ ((C.erase X).erase P).erase Q,
                  realMoment ρ μG
                      (if R = P then 2 else if R = Q then 2 else 1)
                    = e1 ρ μG := by
                intro R hR
                have hRP : R ≠ P :=
                  (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
                have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
                rw [if_neg hRP, if_neg hRQ, realMoment_one]
              rw [Finset.prod_congr rfl h1, Finset.prod_const]
              have h1c : (((C.erase X).erase P).erase Q).card
                  = 1 := by
                rw [Finset.card_erase_of_mem hQD,
                  Finset.card_erase_of_mem hPD, hcard3]
              rw [h1c, pow_one]
              ring
      rw [hfact2]
      ring

/-- **The powerset doubled-doubled-excess sum is the
`(2,2,1,1)` channel excess.** Over the full
`powersetCard 4`, the doubled-doubled-excess sum
equals `kappa6chan2211Excess`: off `primitiveQuads`
every term vanishes by the previous lemma. -/
theorem sum_powersetCard_four_doubledDoubled_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, ∑ Q ∈ C.erase P,
        (doubledDoubledQuadReMoment ρ μG C P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
      = kappa6chan2211Excess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    (doubledDoubledQuadReMoment ρ μG C P Q u u'
      - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro C hC
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, (Finset.mem_filter.mp hC).2.1⟩
  · intro C hCunivers hCnotprim
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hCunivers).2
    have hnp : ¬ IsPrimitiveQuad C := fun hp =>
      hCnotprim (Finset.mem_filter.mpr ⟨Finset.mem_univ C, hp⟩)
    rw [Finset.sum_eq_zero]
    intro P hP
    rw [Finset.sum_eq_zero]
    intro Q hQ
    exact doubledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
      ρ μG hN hN3 hρcont u u' hcard hnp hP hQ

/-- **The card-5 doubled-erasure sum is the dressed
`(2,1,1,1)` channel excess.** Swap the distinct-pair
sum, erase-count 5 → 4, and apply the order-5
dictionary `sum_powersetCard_four_doubled_excess`. -/
theorem sum_powersetCard_five_doubled_erase (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        ∑ x ∈ C.erase P,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * kappa5chanExcess ρ μG u u' := by
  classical
  have hswap : ∀ C : Finset (LayerColumn N),
      (∑ P ∈ C, ∑ x ∈ C.erase P,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = ∑ x ∈ C, ∑ P ∈ C.erase x,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C => sum_sum_erase_swap C
      (fun a b => doubledQuadReMoment ρ μG (C.erase b) a u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
  rw [Finset.sum_congr rfl (fun C _ => hswap C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T,
        (doubledQuadReMoment ρ μG T P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont u u']

/-- **The fivefold excess sum is `e₁` times the
dressed order-4 excess sum**: the fivefold excess
factorization of B6-2b-iii, summed over all
5-supports and erase-counted. -/
theorem sum_powersetCard_five_penta_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5,
        (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
      = e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have h1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (pentaReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        = e1 ρ μG * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
    intro C hC
    rw [pentaReMoment_eq_quadReMoment]
    exact pentaExcess_eq_e1_sum_erase ρ μG hN hN3 hρcont u u' C
      (Finset.mem_powersetCard.mp hC).2
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u']

/-- **The doubled-penta excess at one 5-support
factors.** At a 5-support `C` with private column
`X`: the doubled term at `X` strips off `μ₂` onto
the erasure excess; the doubled terms at the other
columns strip off `e₁` onto the doubled excesses of
the erasure. Summing the erasure excesses over all
erasures of `C` leaves only the `X` terms (the other
erasures are non-primitive), giving the displayed
form with full erasure sums on the right. -/
theorem doubledPenta_excess_sum_factor (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ P ∈ C, (doubledPentaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 2 * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
  classical
  obtain ⟨X, hXC, s, hsX, hpriv⟩ :=
    exists_private_column_of_card_five (N := N) hN hN3 hC
  have hnp : ∀ x ∈ C, x ≠ X → ¬ IsPrimitiveQuad (C.erase x) := by
    intro x hx hxX hprim
    have hXCx : X ∈ C.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxX, hXC⟩
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXCx s hsX
    exact hpriv Q (Finset.mem_erase.mp hQ).2 hQX hsQ
  have hvan4 : ∀ x ∈ C, x ≠ X →
      quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4 = 0 := by
    intro x hx hxX
    have hcard : (C.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hC]
    exact excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont
      u u' hcard (hnp x hx hxX)
  have hvandbl : ∀ x ∈ C, x ≠ X →
      ∑ P ∈ C.erase x,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) = 0 := by
    intro x hx hxX
    have hcard : (C.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hC]
    refine Finset.sum_eq_zero fun P hP => ?_
    exact doubledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG
      hN hN3 hρcont u u' hcard (hnp x hx hxX) hP
  have htermX : (doubledPentaReMoment ρ μG C X u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 2
          * (quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 4) := by
    rw [doubledPentaReMoment_eq_doubledQuadReMoment,
      doubledQuadReMoment_strip_doubled ρ μG hN hN3 hρcont
        u u' hsX hpriv]
    ring
  have hterm : ∀ P ∈ C.erase X,
      (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        = e1 ρ μG * (doubledQuadReMoment ρ μG (C.erase X) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    intro P hP
    rw [doubledPentaReMoment_eq_doubledQuadReMoment,
      doubledQuadReMoment_strip_single ρ μG hN hN3 hρcont
        u u' (Finset.mem_erase.mp hP).2 hXC
        (Ne.symm (Finset.mem_erase.mp hP).1) hsX hpriv]
    ring
  calc ∑ P ∈ C, (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = (doubledPentaReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + ∑ P ∈ C.erase X, (doubledPentaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
        (Finset.add_sum_erase C _ hXC).symm
    _ = realMoment ρ μG 2
            * (quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 4)
          + ∑ P ∈ C.erase X, e1 ρ μG
              * (doubledQuadReMoment ρ μG (C.erase X) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
          rw [htermX, Finset.sum_congr rfl hterm]
    _ = realMoment ρ μG 2 * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
          rw [← Finset.mul_sum]
          congr 1
          · exact congrArg (fun t => realMoment ρ μG 2 * t)
              (Finset.sum_eq_single X
                (fun x hx hxX => hvan4 x hx hxX)
                (fun h => absurd hXC h)).symm
          · exact congrArg (fun t => e1 ρ μG * t)
              (Finset.sum_eq_single X
                (fun x hx hxX => hvandbl x hx hxX)
                (fun h => absurd hXC h)).symm

/-- **The doubled-penta excess sum, converted**: `μ₂`
times the dressed order-4 excess sum plus `e₁` times
the dressed `(2,1,1,1)` channel excess. The `μ₂`
piece is named difference (i) of the section
header. -/
theorem sum_powersetCard_five_doubledPenta_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 2 * ((colCount N - 4)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4)
            * kappa5chanExcess ρ μG u u') := by
  classical
  have hF' : (∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
        ∑ P ∈ C.erase x,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = (colCount N - 4) * kappa5chanExcess ρ μG u u' := by
    have hswap : ∀ C : Finset (LayerColumn N),
        (∑ x ∈ C, ∑ P ∈ C.erase x,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
          = ∑ P ∈ C, ∑ x ∈ C.erase P,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
      fun C => (sum_sum_erase_swap C
        (fun a b => doubledQuadReMoment ρ μG (C.erase b) a u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)).symm
    rw [Finset.sum_congr rfl (fun C _ => hswap C)]
    exact sum_powersetCard_five_doubled_erase ρ μG hN hN3 hρcont
      u u'
  rw [Finset.sum_congr rfl (fun C hC =>
      doubledPenta_excess_sum_factor ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u',
    hF']

/-- **The card-6 penta-subset sum**: each 5-subset
of a 6-support is an erasure, and erasure counting
6 → 5 dresses the fivefold sum by `colCount N − 5`. -/
theorem sum_powersetCard_six_penta_subset (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 5 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
      = (colCount N - 5)
          * ∑ D ∈ Finset.univ.powersetCard 5,
            (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 5) := by
  classical
  rw [Finset.sum_congr rfl (fun C hC =>
      sum_powersetCard_five_subset_eq_sum_erase C
        (Finset.mem_powersetCard.mp hC).2
        (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)),
    sum_powersetCard_six_erase_apply
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)]

/-- **Twice the 4-subset sum at one 6-support is its
5-subset erasure sum**: each 4-subset `T` is counted
once for each of the two columns of `C ∖ T`, through
the 5-subsets between `T` and `C`. -/
theorem two_mul_sum_powersetCard_four_subset
    (C : Finset (LayerColumn N)) (hC : C.card = 6)
    (f : Finset (LayerColumn N) → ℝ) :
    2 * ∑ T ∈ Finset.powersetCard 4 C, f T
      = ∑ D ∈ Finset.powersetCard 5 C,
          ∑ T ∈ Finset.powersetCard 4 D, f T := by
  classical
  have h1 : ∀ T ∈ Finset.powersetCard 4 C,
      ∑ z ∈ C \ T, f T = 2 * f T := by
    intro T hT
    have hsub : T ⊆ C := (Finset.mem_powersetCard.mp hT).1
    have hcard : T.card = 4 := (Finset.mem_powersetCard.mp hT).2
    rw [Finset.sum_const, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hsub, hC, hcard, nsmul_eq_mul]
    norm_num
  have hset : ∀ T : Finset (LayerColumn N),
      C.filter (fun z => z ∉ T) = C \ T := fun T =>
    Finset.ext fun z => by simp [Finset.mem_sdiff]
  have h2 : ∑ T ∈ Finset.powersetCard 4 C, ∑ z ∈ C \ T, f T
      = ∑ T ∈ Finset.powersetCard 4 C,
          ∑ z ∈ C, (if z ∉ T then f T else 0) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← hset T, Finset.sum_filter]
  have h3 : ∑ T ∈ Finset.powersetCard 4 C,
        ∑ z ∈ C, (if z ∉ T then f T else 0)
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase z), f T := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hset : (Finset.powersetCard 4 C).filter (fun T => z ∉ T)
        = Finset.powersetCard 4 (C.erase z) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hzT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hzT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset z C), hcard⟩, ?_⟩
        exact fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    rw [← Finset.sum_filter, hset]
  have h4 : ∑ D ∈ Finset.powersetCard 5 C,
        ∑ T ∈ Finset.powersetCard 4 D, f T
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase z), f T :=
    sum_powersetCard_five_subset_eq_sum_erase C hC
      (fun D => ∑ T ∈ Finset.powersetCard 4 D, f T)
  calc 2 * ∑ T ∈ Finset.powersetCard 4 C, f T
      = ∑ T ∈ Finset.powersetCard 4 C, ∑ z ∈ C \ T, f T := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T hT => (h1 T hT).symm
    _ = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase z), f T :=
        h2.trans h3
    _ = ∑ D ∈ Finset.powersetCard 5 C,
          ∑ T ∈ Finset.powersetCard 4 D, f T := h4.symm

/-- **The card-6 quad-subset sum**: each 4-support
sits in `C(colCount N − 4, 2)` six-supports, counted
through the 5-subset erasure chain. -/
theorem sum_powersetCard_six_quad_subset (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      = ((colCount N - 4) * (colCount N - 5) / 2)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
  classical
  set f : Finset (LayerColumn N) → ℝ :=
    fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4 with hf
  have h2 : 2 * (∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 4 C, f T)
      = (colCount N - 5) * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4, f T) := by
    have step1 : ∀ C ∈ Finset.univ.powersetCard 6,
        2 * ∑ T ∈ Finset.powersetCard 4 C, f T
          = ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase x), f T := by
      intro C hC
      have hC6 : C.card = 6 := (Finset.mem_powersetCard.mp hC).2
      rw [two_mul_sum_powersetCard_four_subset C hC6 f,
        sum_powersetCard_five_subset_eq_sum_erase C hC6
          (fun D => ∑ T ∈ Finset.powersetCard 4 D, f T)]
    have step2 : (∑ C ∈ Finset.univ.powersetCard 6,
          ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase x), f T)
        = (colCount N - 5) * ∑ D ∈ Finset.univ.powersetCard 5,
            ∑ T ∈ Finset.powersetCard 4 D, f T :=
      sum_powersetCard_six_erase_apply
        (fun D => ∑ T ∈ Finset.powersetCard 4 D, f T)
    have step3 : (∑ D ∈ Finset.univ.powersetCard 5,
          ∑ T ∈ Finset.powersetCard 4 D, f T)
        = (colCount N - 4)
            * ∑ T ∈ Finset.univ.powersetCard 4, f T := by
      rw [Finset.sum_congr rfl (fun D hD =>
          sum_powersetCard_four_subset_eq_sum_erase D
            (Finset.mem_powersetCard.mp hD).2 f)]
      exact sum_powersetCard_five_erase_apply f
    rw [Finset.mul_sum, Finset.sum_congr rfl step1, step2, step3]
  have hI : (∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 4 C, f T)
      = ((colCount N - 5) * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4, f T)) / 2 := by
    linarith
  rw [hI]
  ring

/-- **The six-support split, generic in the
summand**: any sum over all 6-supports separates
into the `C₆` family, the `Θ` family, and the rest.
(The generic form of
`sum_powersetCard_six_hexaExcess_split`.) -/
theorem sum_powersetCard_six_split_apply
    (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 6, f C
      = ∑ C ∈ c6Supports, f C
        + ∑ C ∈ thetaSupports, f C
        + ∑ C ∈ (Finset.univ.powersetCard 6).filter
            (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports), f C := by
  classical
  have hc6sub : c6Supports (N := N)
      ⊆ Finset.univ.powersetCard 6 :=
    fun C hC => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, card_eq_six_of_mem_c6Supports hC⟩
  have hthsub : thetaSupports (N := N)
      ⊆ Finset.univ.powersetCard 6 :=
    fun C hC => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, card_eq_six_of_mem_thetaSupports hC⟩
  have hdisj : Disjoint (c6Supports (N := N)) (thetaSupports (N := N)) := by
    refine Finset.disjoint_left.mpr fun C h1 h2 => ?_
    have h6 : (quadSupport C).card = 6 :=
      (hasSixPatternC6_of_mem_c6Supports h1).1
    have h5 : (quadSupport C).card = 5 :=
      (hasSixPatternTheta_of_mem_thetaSupports h2).1
    omega
  have hUsub : (c6Supports (N := N)) ∪ (thetaSupports (N := N))
      ⊆ Finset.univ.powersetCard 6 :=
    Finset.union_subset hc6sub hthsub
  have hrest : (Finset.univ.powersetCard 6)
        \ ((c6Supports (N := N)) ∪ (thetaSupports (N := N)))
      = (Finset.univ.powersetCard 6).filter
          (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports) := by
    refine Finset.ext fun C => ?_
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, fun h1 => h.2 (Or.inl h1), fun h2 => h.2 (Or.inr h2)⟩
    · intro h
      refine ⟨h.1, ?_⟩
      rintro (h1 | h2)
      · exact h.2.1 h1
      · exact h.2.2 h2
  have hsplit := (Finset.sum_sdiff hUsub (f := f)).symm
  rw [hrest, Finset.sum_union hdisj] at hsplit
  rw [hsplit]
  ring

/-- **A `C₆` support has no primitive 4-subset.**
If `T ⊆ C` were a primitive quad inside a `C₆`
support `C`, every site of `T` would have degree
exactly `2` in both, so `T` would read exactly four
of `C`'s six sites; the two remaining columns of
`C` would then both have to read exactly the two
remaining sites — the same site pair twice,
contradicting `colSites_eq_imp`. Hence every
4-subset excess at a `C₆` support vanishes. -/
theorem excess_eq_zero_of_subset_c6Supports (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C ∈ c6Supports) {T : Finset (LayerColumn N)}
    (hT : T ∈ Finset.powersetCard 4 C) :
    quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4 = 0 := by
  classical
  obtain ⟨hsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  refine excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont
    u u' hTcard ?_
  intro hprim
  have hCcard : C.card = 6 := card_eq_six_of_mem_c6Supports hC
  have hpat := hasSixPatternC6_of_mem_c6Supports hC
  have hsuppSub : quadSupport T ⊆ quadSupport C := by
    intro s hs
    obtain ⟨P, hPT, hsP⟩ := Finset.mem_biUnion.mp hs
    exact Finset.mem_biUnion.mpr ⟨P, hsub hPT, hsP⟩
  have hdegT : ∀ s ∈ quadSupport T, siteDegree T s = 2 := by
    intro s hs
    have hle1 : 2 ≤ siteDegree T s := two_le_siteDegree hprim hs
    have hle2 : siteDegree T s ≤ siteDegree C s :=
      Finset.card_le_card (by
        intro P hP
        rw [Finset.mem_filter] at hP ⊢
        exact ⟨hsub hP.1, hP.2⟩)
    have hC2 : siteDegree C s = 2 := hpat.2 s (hsuppSub hs)
    omega
  have hqcard : (quadSupport T).card = 4 := by
    have hsum := sum_siteDegree_eq hN hprim.1
    rw [Finset.sum_congr rfl hdegT, Finset.sum_const] at hsum
    simp only [nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  have hsdiffCard : (quadSupport C \ quadSupport T).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsuppSub,
      hpat.1, hqcard]
  have hCTcard : (C \ T).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      hCcard, hTcard]
  obtain ⟨x, y, hxy, hCT⟩ := Finset.card_eq_two.mp hCTcard
  have hxCT : x ∈ C \ T := by
    rw [hCT]; exact Finset.mem_insert_self x {y}
  have hyCT : y ∈ C \ T := by
    rw [hCT]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hcol : ∀ z ∈ C \ T,
      colSites z = quadSupport C \ quadSupport T := by
    intro z hz
    have hzC : z ∈ C := (Finset.mem_sdiff.mp hz).1
    have hzT : z ∉ T := (Finset.mem_sdiff.mp hz).2
    have hsub2 : colSites z ⊆ quadSupport C \ quadSupport T := by
      intro s hs
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_biUnion.mpr ⟨z, hzC, hs⟩, ?_⟩
      intro hsT
      have hT2 : (T.filter (fun P => s ∈ colSites P)).card = 2 :=
        hdegT s hsT
      have hC2 : (C.filter (fun P => s ∈ colSites P)).card = 2 :=
        hpat.2 s (hsuppSub hsT)
      have hsubf : insert z (T.filter (fun P => s ∈ colSites P))
          ⊆ C.filter (fun P => s ∈ colSites P) := by
        intro P hP
        rw [Finset.mem_filter]
        rcases Finset.mem_insert.mp hP with rfl | hP
        · exact ⟨hzC, hs⟩
        · exact ⟨hsub (Finset.mem_filter.mp hP).1,
            (Finset.mem_filter.mp hP).2⟩
      have hcard := Finset.card_le_card hsubf
      rw [Finset.card_insert_of_notMem (by
        rw [Finset.mem_filter]
        exact fun h => hzT h.1)] at hcard
      omega
    exact Finset.eq_of_subset_of_card_le hsub2
      (le_of_eq (by rw [hsdiffCard, card_colSites_two hN z]))
  have h1 : colSites x = colSites y := by
    rw [hcol x hxCT, hcol y hyCT]
  exact hxy (colSites_eq_imp hN hN3 h1)

/-- **The rest family's sixfold excess is `e₁²`
times its 4-subset excess sum.** At a rest support
the private column's factor identity
(`hexaExcess_eq_of_private`) has inner sum equal to
the full 4-subset excess sum: the 4-subsets through
the private column are non-primitive (the column
stays private in them), and the remaining
4-subsets are exactly the erasure 4-subsets. -/
theorem hexaExcess_eq_e1_sq_sum_fourSubsets_of_mem_rest
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C ∈ (Finset.univ.powersetCard 6).filter
      (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports)) :
    hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6
      = (e1 ρ μG) ^ 2 * ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
  classical
  have hCcard : C.card = 6 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).2
  have hnot : C ∉ c6Supports ∧ C ∉ thetaSupports :=
    (Finset.mem_filter.mp hC).2
  have hpriv : HasPrivateColumn C := by
    rcases mem_c6_or_theta_or_private_of_card_six hN hN3 C hCcard
      with h | h | h
    · exact absurd h hnot.1
    · exact absurd h hnot.2
    · exact h
  obtain ⟨X, hXC, s, hsX, hdeg⟩ := hpriv
  have hDcard : (C.erase X).card = 5 := by
    rw [Finset.card_erase_of_mem hXC, hCcard]
  have hB0 : ∑ T ∈ (Finset.powersetCard 4 C).filter
        (fun T => X ∈ T),
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    have hsub : T ⊆ C :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
    have hTcard : T.card = 4 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    have hXT : X ∈ T := (Finset.mem_filter.mp hT).2
    refine excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont
      u u' hTcard (fun hprim => ?_)
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXT s hsX
    have hsub2 : ({X, Q} : Finset (LayerColumn N))
        ⊆ C.filter (fun P => s ∈ colSites P) := by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rw [Finset.mem_filter]
      rcases hR with rfl | rfl
      · exact ⟨hXC, hsX⟩
      · exact ⟨hsub hQ, hsQ⟩
    have hle := Finset.card_le_card hsub2
    rw [Finset.card_pair (fun hh => hQX hh.symm)] at hle
    have hdeg' : (C.filter (fun P => s ∈ colSites P)).card = 1 :=
      hdeg
    omega
  have hsplit : ∑ T ∈ Finset.powersetCard 4 C,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      = ∑ T ∈ Finset.powersetCard 4 (C.erase X),
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have h := (Finset.sum_filter_add_sum_filter_not
      (Finset.powersetCard 4 C) (fun T => X ∈ T)
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)).symm
    rw [hB0, zero_add] at h
    rw [h]
    have hset : (Finset.powersetCard 4 C).filter (fun T => X ∉ T)
        = Finset.powersetCard 4 (C.erase X) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hzT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hzT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset X C), hcard⟩, ?_⟩
        exact fun hh => (Finset.mem_erase.mp (hsub hh)).1 rfl
    rw [hset]
  rw [hexaExcess_eq_of_private ρ μG hN hN3 hρcont u u' C
    hCcard X hXC s hsX hdeg,
    ← sum_powersetCard_four_subset_eq_sum_erase (C.erase X) hDcard
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4),
    hsplit]

/-- **The sixfold excess sum, converted**: the `C₆`
and `Θ` channel excesses at weight `d⁻⁶` (after the
assembly's `/720`), plus `e₁²` times the dressed
4-subset count, minus `e₁²` times the `Θ` family's
4-subset excess sum — named difference (ii) of the
section header. -/
theorem sum_powersetCard_six_hexaExcess_convert (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6,
        (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
      = kappa6chanC6Excess ρ μG u u'
        + kappa6chanThetaExcess ρ μG u u'
        + (e1 ρ μG) ^ 2
          * (((colCount N - 4) * (colCount N - 5) / 2)
              * ∑ T ∈ Finset.univ.powersetCard 4,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
                ∑ T ∈ Finset.powersetCard 4 C,
                  (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have hC6 : kappa6chanC6Excess ρ μG u u'
      = ∑ C ∈ c6Supports,
          (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := rfl
  have hTh : kappa6chanThetaExcess ρ μG u u'
      = ∑ C ∈ thetaSupports,
          (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := rfl
  have hRest : (∑ C ∈ (Finset.univ.powersetCard 6).filter
        (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
        (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))
      = (e1 ρ μG) ^ 2 * ∑ C ∈ (Finset.univ.powersetCard 6).filter
          (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
          ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun C hC =>
      hexaExcess_eq_e1_sq_sum_fourSubsets_of_mem_rest ρ μG hN
        hN3 hρcont u u' hC
  have hS4c6 : (∑ C ∈ c6Supports,
        ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) = 0 :=
    Finset.sum_eq_zero fun C hC => Finset.sum_eq_zero fun T hT =>
      excess_eq_zero_of_subset_c6Supports ρ μG hN hN3 hρcont
        u u' hC hT
  have hsplitS4 := sum_powersetCard_six_split_apply
    (fun C => ∑ T ∈ Finset.powersetCard 4 C,
      (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
  rw [hS4c6] at hsplitS4
  have hRestS4 : (∑ C ∈ (Finset.univ.powersetCard 6).filter
        (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
        ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ((colCount N - 4) * (colCount N - 5) / 2)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ∑ C ∈ thetaSupports,
            ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have hI := sum_powersetCard_six_quad_subset ρ μG hN hN3
      hρcont u u'
    linarith
  rw [sum_powersetCard_six_split_apply
      (fun C => hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6),
    hC6, hTh, hRest, hRestS4]

/-- **The order-6 assembly identity** (B6-2c):
`κ₆^dep` is the order-5 dressing of `κ₅^dep` — at
exactly the order-5 factor `4 + (M−4)·B` — plus a
`κ₄^dep` dressing, plus the four channel excesses
at their `d⁻⁶` weights (`1/6`, `1/8`, `1`, `1`),
minus the named extra term of difference (ii).
FENCES: an identity, not a sign — no sign is
asserted for `κ₆^dep` or for any channel; the
β⁶ general sign remains FRONTIER; NO CLAIM;
parts of the Clay Yang–Mills statement closed: 0;
dials 0/4. The two named differences from the
predicted shape are recorded in the
`Assembly6Close` header and on this statement's
face: the `κ₄^dep` coefficient carries
`½·(M−4)·μ₂/d²`, and the `Θ` 4-subset sum
`S4theta` appears beyond the four channels. -/
theorem kappa6dep_eq (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa6dep ρ μG u u'
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa5dep ρ μG u u'
        + (-(4 + (colCount N - 4)
              * (1 - e1 ρ μG / (d : ℝ))) ^ 2
            + 8
            + (9 / 2) * (colCount N - 4)
            - 5 * (colCount N - 4) * (e1 ρ μG / (d : ℝ))
            + (colCount N - 4) * (colCount N - 5) / 2
            - (colCount N - 4) * (colCount N - 5)
              * (e1 ρ μG / (d : ℝ))
            + (1 / 2) * (colCount N - 4)
              * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + (e1 ρ μG / (d : ℝ)) ^ 2
              * ((colCount N - 4) * (colCount N - 5) / 2))
          * kappa4dep ρ μG u u'
        + (((d : ℝ)⁻¹) ^ 6 / 6)
          * kappa6chan3111Excess ρ μG u u'
        + (((d : ℝ)⁻¹) ^ 6 / 8)
          * kappa6chan2211Excess ρ μG u u'
        + ((d : ℝ)⁻¹) ^ 6 * kappa6chanC6Excess ρ μG u u'
        + ((d : ℝ)⁻¹) ^ 6 * kappa6chanThetaExcess ρ μG u u'
        - ((d : ℝ)⁻¹) ^ 6 * (e1 ρ μG) ^ 2
          * ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
  classical
  have hβ : betaCoeff6 ρ μG u u'
      = (∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 6
          ∂(Measure.pi fun _ : LayerSite N => μG)) / 720 := by
    have hcong : (∫ α : LayerSite N → G,
          (layerDensSum ρ α u u') ^ 6 / 720
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          (720 : ℝ)⁻¹ * (layerDensSum ρ α u u') ^ 6
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with α
      rw [div_eq_inv_mul]
    show betaCoeff6 ρ μG u u' = _
    unfold betaCoeff6
    rw [hcong, integral_const_mul, div_eq_inv_mul]
  have hJ : (∑ D ∈ Finset.univ.powersetCard 5,
        (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 5))
      = e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    have hqp : (∑ D ∈ Finset.univ.powersetCard 5,
          (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 5))
        = ∑ D ∈ Finset.univ.powersetCard 5,
          (pentaReMoment ρ μG D u u' - (e1 ρ μG) ^ 5) :=
      Finset.sum_congr rfl fun C _ => by
        rw [pentaReMoment_eq_quadReMoment]
    rw [hqp, sum_powersetCard_five_penta_excess ρ μG hN hN3
      hρcont u u']
  rw [kappa6dep_def, hβ,
    betaCoeff6_total ρ μG hN hN3 hρcont u u',
    sum_powersetCard_four_eq_primitive ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_four_tripled_excess ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
      hρcont u u',
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_five_doubled_erase ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_five_penta_excess ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_five_doubledPenta_excess ρ μG hN hN3
      hρcont u u',
    sum_powersetCard_six_quad_subset ρ μG hN hN3 hρcont
      u u',
    sum_powersetCard_six_penta_subset ρ μG hN hN3 hρcont
      u u',
    hJ,
    sum_powersetCard_six_hexaExcess_convert ρ μG hN hN3
      hρcont u u',
    kappa5dep_eq ρ μG hN hN3 hρcont u u',
    kappa4dep_eq ρ μG hN hN3 hρcont u u']
  simp only [sum_powersetCard_four_eq_primitive ρ μG hN hN3
    hρcont u u']
  ring

/-- **Diagonal corollary.** On the diagonal
`u' = u`: `kappa6dep` in the closed form of
`kappa6dep_eq`. -/
theorem kappa6dep_diag (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u : LayerLink N → G) :
    kappa6dep ρ μG u u
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa5dep ρ μG u u
        + (-(4 + (colCount N - 4)
              * (1 - e1 ρ μG / (d : ℝ))) ^ 2
            + 8
            + (9 / 2) * (colCount N - 4)
            - 5 * (colCount N - 4) * (e1 ρ μG / (d : ℝ))
            + (colCount N - 4) * (colCount N - 5) / 2
            - (colCount N - 4) * (colCount N - 5)
              * (e1 ρ μG / (d : ℝ))
            + (1 / 2) * (colCount N - 4)
              * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + (e1 ρ μG / (d : ℝ)) ^ 2
              * ((colCount N - 4) * (colCount N - 5) / 2))
          * kappa4dep ρ μG u u
        + (((d : ℝ)⁻¹) ^ 6 / 6)
          * kappa6chan3111Excess ρ μG u u
        + (((d : ℝ)⁻¹) ^ 6 / 8)
          * kappa6chan2211Excess ρ μG u u
        + ((d : ℝ)⁻¹) ^ 6 * kappa6chanC6Excess ρ μG u u
        + ((d : ℝ)⁻¹) ^ 6 * kappa6chanThetaExcess ρ μG u u
        - ((d : ℝ)⁻¹) ^ 6 * (e1 ρ μG) ^ 2
          * ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u - (e1 ρ μG) ^ 4) :=
  kappa6dep_eq ρ μG hN hN3 hρcont u u

end Assembly6Close

#print axioms kappa6dep_eq

end ThetLogos
