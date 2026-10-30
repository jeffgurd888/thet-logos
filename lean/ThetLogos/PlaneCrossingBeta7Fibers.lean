/-
# ThetLogos.PlaneCrossingBeta7Fibers — B7-2b-i: the
order-7 fiber expansion machinery, the migration
lemmas, and the constant fibers (cards 1, 2, 3)

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**.
Dials 0/4. This is B7-2b-i, a sibling module to
`ThetLogos.PlaneCrossingBeta7Assembly` (B7-2a, the
seven excesses), mirroring B6-2b-i's fiber sections in
`ThetLogos.PlaneCrossingBeta6Assembly` at order 7.
Variable context, named exactly: general `(G, ρ)` in
the β-line's section context (no irreducibility); the
fiber evaluations additionally carry `Even N`,
`3 ≤ N`, and continuity of `g ↦ repMatrix ρ g`, as at
order 6. Fiber bookkeeping and constant evaluations
only: the integrated seventh-power expansion is split
fiberwise by `multSupport` (B6-0's support), fibers
over supports of card `0` or `≥ 8` are empty, and the
fibers over supports of card `1`, `2`, `3` evaluate to
the constant pattern values of `kappa7Const`: card
`1`: pattern `(7)`; card `2`: splits `(6,1)`, `(5,2)`,
`(4,3)` (with their reversals); card `3`: `(5,1,1)`,
`(4,2,1)`, `(3,3,1)`, `(3,2,2)` (with all their
permutations). **No card-by-card fiber accounting for
cards 7/6/5/4 is asserted here** (that is B7-2b-ii /
2b-iii), **no total decomposition, no `kappa7dep`
identity, and no sign is asserted anywhere**: the
assembly is an identity-in-progress and the β⁷
general sign is FRONTIER. B7-0's claims-to-check (the
card-5 and card-6 erasure claims and the card-7
enumeration remainder) stay OPEN and are not settled
by anything in this module.
-/

import Mathlib.Data.Nat.Choose.Multinomial
import ThetLogos.PlaneCrossingBeta7Assembly
import ThetLogos.PrimitiveQuadPatterns

open MeasureTheory Finset

namespace ThetLogos

section Fiber7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The seventh-power expansion, integrated.** The
multinomial expansion of `(layerDensSum)^7`, integrated
termwise: each exponent function `k` contributes its
multinomial coefficient times the integral of the
column-density monomial `∏ P, colDensC(P)^(k P)`.
Integrability of each monomial is by the uniform bound
`|colDensC| ≤ 2` (total mass `2^7 = 128`). The order-7
analogue of `integral_layerDensSum_pow_six`. -/
theorem integral_layerDensSum_pow_seven (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 7
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ k ∈ Finset.piAntidiag Finset.univ 7,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG) := by
  classical
  have hmeas : ∀ P : LayerColumn N,
      Measurable fun α : LayerSite N → G =>
        colDensC ρ u u' P α :=
    fun P => measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2
  have hInt : ∀ k ∈ Finset.piAntidiag Finset.univ 7,
      Integrable (fun α : LayerSite N → G =>
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro k hk
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound
      (Finset.measurable_prod Finset.univ fun P _ =>
        (hmeas P).pow_const (k P)).aestronglyMeasurable
      (128 : ℝ) (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    have hsum7 : ∑ P ∈ Finset.univ, k P = 7 :=
      (Finset.mem_piAntidiag.mp hk).1
    have hle : ∏ P ∈ Finset.univ, |(colDensC ρ u u' P α) ^ (k P)|
        ≤ ∏ P ∈ Finset.univ, (2 : ℝ) ^ (k P) :=
      Finset.prod_le_prod₀ (fun P _ => abs_nonneg _)
        (fun P _ => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_colDensC_le ρ u u' P α) _)
    refine le_trans hle ?_
    rw [Finset.prod_pow_eq_pow_sum, hsum7]
    norm_num
  have hpt : ∀ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 7
      = ∑ k ∈ Finset.piAntidiag Finset.univ 7,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P) := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u']
    exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ
      (fun P => colDensC ρ u u' P α) 7
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ hInt,
    Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)]

/-- **Migration lemma (support collapse of the exponent
sum).** Summation over all columns collapses to the
multiplicity support: off-support exponents are zero.
The support is B6-0's `multSupport`. (The order-6
assembly's `sum_univ_eq_sum_multSupport` is this same
statement; it is restated here under the order-7 name
so the fiber arguments below cite the local form.) -/
theorem sum_univ_eq_sum_multSupport7 (k : LayerColumn N → ℕ) :
    ∑ P ∈ Finset.univ, k P = ∑ P ∈ multSupport k, k P := by
  unfold multSupport
  exact (Finset.sum_subset (Finset.filter_subset _ _)
    (fun P _ hP => not_not.mp (fun hne =>
      hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩)))).symm

/-- **Migration lemma (support collapse of the monomial
integral).** The monomial integral collapses to the
multiplicity support: off-support factors are
`x^0 = 1`. The order-7 analogue of
`integral_colDens_prod_pow_univ_six`. -/
theorem integral_colDens_prod_pow_univ_seven
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

/-- **Migration lemma (fiberwise split by support).**
The integrated expansion, regrouped by the
multiplicity support of the exponent function. The
order-7 analogue of `sum_piAntidiag6_fiberwise`. -/
theorem sum_piAntidiag7_fiberwise (F : (LayerColumn N → ℕ) → ℝ) :
    ∑ k ∈ Finset.piAntidiag Finset.univ 7, F k
      = ∑ C ∈ Finset.univ.powerset,
          ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
              (fun k => multSupport k = C), F k := by
  have hsub : ∀ k : LayerColumn N → ℕ,
      multSupport k = Finset.univ.filter (fun P => k P ≠ 0) :=
    fun k => rfl
  exact (Finset.sum_fiberwise_of_maps_to (fun k _ => by
    rw [hsub k]
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)) F).symm

/-- **Fibers over supports of card `0` or `≥ 8` are
empty**: on its support every exponent is at least
`1`, so the support's card is at most the total
exponent sum `7`, and a card-`0` support carries sum
`0 ≠ 7`. The order-7 analogue of
`fiber6_eq_empty_of_card_ne`. -/
theorem fiber7_eq_empty_of_card_ne (C : Finset (LayerColumn N))
    (hC : C.card = 0 ∨ 8 ≤ C.card) :
    (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun k hk => ?_
  have hk7 : ∑ P ∈ Finset.univ, k P = 7 :=
    (Finset.mem_piAntidiag.mp
      (Finset.mem_filter.mp hk).1).1
  have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
  have hsumC : ∑ P ∈ C, k P = 7 := by
    rw [← hsupp, ← sum_univ_eq_sum_multSupport7]
    exact hk7
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
  rcases hC with h0 | h8
  · have : C = ∅ := Finset.card_eq_zero.mp h0
    rw [this, Finset.sum_empty] at hsumC
    exact absurd hsumC (by norm_num)
  · omega

/-- **Multinomial from the factorial product.** If
the factorials of the exponents of `k` multiply to
`p ≠ 0`, the multinomial coefficient is `5040 / p`,
by `Nat.multinomial_spec` at total exponent `7`. The
order-7 analogue of `multinomial6_univ_eq`. -/
theorem multinomial7_univ_eq (k : LayerColumn N → ℕ)
    (hk7 : ∑ P ∈ Finset.univ, k P = 7) (p : ℕ)
    (hp : ∏ P ∈ Finset.univ, Nat.factorial (k P) = p)
    (hp0 : p ≠ 0) :
    (Nat.multinomial Finset.univ k : ℝ) = 5040 / (p : ℝ) := by
  have h := Nat.multinomial_spec Finset.univ k
  rw [hp, hk7] at h
  have h5040 : Nat.factorial 7 = 5040 := by
    norm_num [Nat.factorial]
  rw [h5040] at h
  have h' : (p : ℝ) * (Nat.multinomial Finset.univ k : ℝ)
      = 5040 := by exact_mod_cast h
  rw [eq_div_iff (by exact_mod_cast hp0 : (p : ℝ) ≠ 0), mul_comm]
  exact h'

/-- The multiplicity support unfolds to its defining
filter (B6-0's `multSupport`); used as a simp normal
form in the fiber arguments below. The order-7-named
form of `multSupport_eq_filter`. -/
theorem multSupport_eq_filter7 (k : LayerColumn N → ℕ) :
    multSupport k = Finset.univ.filter (fun P => k P ≠ 0) :=
  rfl

/-- **Character power-moments factor on small supports**
(order-7 form). For `T` of card at most 3 and arbitrary
exponents, the integral of `∏ r_P^{aP}` is the product
of the Haar moments. This is exactly the statement of
the order-6 assembly's
`integral_colRe_prod_pow_card_le_three6` — the
factorization is exponent-blind and order-free — restated
under the order-7 name so the fiber arguments below cite
the local form, and proved by that theorem. -/
theorem integral_colRe_prod_pow_card_le_three7 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (T : Finset (LayerColumn N))
    (hT : T.card ≤ 3) (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, ∏ P ∈ T, (colRe ρ u u' P α) ^ (a P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∏ P ∈ T, realMoment ρ μG (a P) :=
  integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3 hρcont u u' T hT a

/-- **Density moments of a triple of distinct columns
factor** (order-7 form). Exactly the statement of the
order-6 assembly's `integral_colDens_triple_pow6`,
restated under the order-7 name and proved by it. -/
theorem integral_colDens_triple_pow7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ (a P)
          * (colDensC ρ u u' Q α) ^ (a Q)
          * (colDensC ρ u u' R α) ^ (a R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG (a P) * densMomentValue ρ μG (a Q)
        * densMomentValue ρ μG (a R) :=
  integral_colDens_triple_pow6 ρ μG hN hN3 hρcont u u' hPQ hPR hQR a

/-- **Density power-moments factor on small supports**
(order-7 form), by the card of the support. Exactly the
statement of the order-6 assembly's
`integral_colDens_prod_pow_card_le_three6`, restated
under the order-7 name and proved by it; this is the
evaluation engine for the card-2 and card-3 fibers
below. -/
theorem integral_colDens_prod_pow_card_le_three7 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (T : Finset (LayerColumn N))
    (hT : T.card ≤ 3) (a : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G, ∏ P ∈ T, (colDensC ρ u u' P α) ^ (a P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∏ P ∈ T, densMomentValue ρ μG (a P) :=
  integral_colDens_prod_pow_card_le_three6 ρ μG hN hN3 hρcont u u' T hT a


/-- **The card-1 fiber.** Over a 1-support `C`, the
fiber of the expansion is the single exponent `(7)`
on that column, its multinomial coefficient is `1`,
and its value is the pattern value `A₇` of
`kappa7Const`'s `(7)` pattern. The order-7 analogue
of `fiber_card_one6` — the first constant fiber. -/
theorem fiber_card_one7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 1) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 7 := by
  classical
  obtain ⟨P, hPeq⟩ := Finset.card_eq_one.mp hC
  have hfib : (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C)
      = {fun Q => if Q = P then 7 else 0} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ?_
    constructor
    · refine ⟨fun Q => if Q = P then 7 else 0, ?_⟩
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun Q _ => Finset.mem_univ Q⟩, ?_⟩
      · rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 7)]
        simp
      · refine Finset.ext fun Q => ?_
        simp only [show multSupport (fun Q => if Q = P then 7 else 0)
            = Finset.univ.filter
              (fun Q => (if Q = P then 7 else 0) ≠ 0) from rfl,
          Finset.mem_filter, Finset.mem_univ,
          true_and, hPeq, Finset.mem_singleton]
        by_cases hQ : Q = P <;> simp [hQ]
    · intro k hk
      have hk7 : ∑ Q ∈ Finset.univ, k Q = 7 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hkP : k P = 7 := by
        have h1 : ∑ Q ∈ multSupport k, k Q = 7 := by
          rw [← sum_univ_eq_sum_multSupport7]
          exact hk7
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
        (fun Q => if Q = P then 7 else 0) : ℝ) = 1 := by
    have hp : ∏ Q ∈ Finset.univ,
        Nat.factorial ((fun Q => if Q = P then 7 else 0) Q)
          = 5040 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial ((fun Q => if Q = P then 7 else 0) Q)
          = ∏ Q ∈ C,
            Nat.factorial ((fun Q => if Q = P then 7 else 0) Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := by
              rw [hPeq, Finset.mem_singleton] at hQ
              exact hQ
            simp [hQP])).symm
      rw [h1, hPeq, Finset.prod_singleton]
      simp
      norm_num [Nat.factorial]
    have hk7 : ∑ Q ∈ Finset.univ,
        (fun Q => if Q = P then 7 else 0) Q = 7 := by
      rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 7)]
      simp
    have h := multinomial7_univ_eq
      (fun Q => if Q = P then 7 else 0) hk7 5040 hp
      (by norm_num)
    rw [h]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ Q ∈ Finset.univ,
          (colDensC ρ u u' Q α)
            ^ ((fun Q => if Q = P then 7 else 0) Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 7 := by
    have hsupp : multSupport (fun Q => if Q = P then 7 else 0)
        = C := by
      refine Finset.ext fun Q => ?_
      simp only [show multSupport (fun Q => if Q = P then 7 else 0)
          = Finset.univ.filter
            (fun Q => (if Q = P then 7 else 0) ≠ 0) from rfl,
        Finset.mem_filter, Finset.mem_univ,
        true_and, hPeq, Finset.mem_singleton]
      by_cases hQ : Q = P <;> simp [hQ]
    rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont u u'
      (fun Q => if Q = P then 7 else 0), hsupp, hPeq]
    have hpt : ∀ α : LayerSite N → G,
        ∏ Q ∈ ({P} : Finset (LayerColumn N)),
          (colDensC ρ u u' Q α)
            ^ ((fun Q => if Q = P then 7 else 0) Q)
        = (colDensC ρ u u' P α) ^ 7 := by
      intro α
      rw [Finset.prod_singleton]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact densMomentValue_eq ρ μG hN hρcont u u' P 7
  rw [hmult, hval, one_mul]

/-- **The card-2 fiber.** Over a 2-support `{P, Q}`,
the fiber is the six exponent splits `(a, 7−a)`,
`a = 1..6` (parametrized by the ordered pair
`(k P, k Q)`); the fiber sum evaluates to
`7·A₁A₆ + 21·A₂A₅ + 35·A₃A₄ + 35·A₄A₃ + 21·A₅A₂
+ 7·A₆A₁`: the `(6,1)`, `(5,2)`, `(4,3)` patterns of
`kappa7Const` with their reversals. The order-7
analogue of `fiber_card_two6` — the second constant
fiber. -/
theorem fiber_card_two7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 2) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 7 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 6)
        + 21 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 5)
        + 35 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 4)
        + 35 * (densMomentValue ρ μG 4 * densMomentValue ρ μG 3)
        + 21 * (densMomentValue ρ μG 5 * densMomentValue ρ μG 2)
        + 7 * (densMomentValue ρ μG 6 * densMomentValue ρ μG 1) := by
  classical
  obtain ⟨P, Q, hPQ, hCeq⟩ := Finset.card_eq_two.mp hC
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 6 ×ˢ Finset.Icc 1 6).filter
      (fun t => t.1 + t.2 = 7) with hS
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (5040
            / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ) : ℝ))
          * (densMomentValue ρ μG t.1
            * densMomentValue ρ μG t.2) := by
    refine (Finset.sum_bij
      (fun t _ => fun X => if X = P then t.1
        else if X = Q then t.2 else 0) ?_ ?_ ?_ ?_).symm
    · intro t ht
      have htS : t.1 + t.2 = 7
          ∧ t.1 ∈ Finset.Icc 1 6 ∧ t.2 ∈ Finset.Icc 1 6 :=
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
        simp only [multSupport_eq_filter7, Finset.mem_filter, Finset.mem_univ,
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
      have hk7 : ∑ X ∈ Finset.univ, k X = 7 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 7 := by
        rw [← hsupp, ← sum_univ_eq_sum_multSupport7]
        exact hk7
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
      have htS : t.1 + t.2 = 7
          ∧ t.1 ∈ Finset.Icc 1 6 ∧ t.2 ∈ Finset.Icc 1 6 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2⟩
      have hsum : ∑ X ∈ Finset.univ,
          (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) X = 7 := by
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
           = 5040 / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ)
            : ℝ) :=
        multinomial7_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : multSupport (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) = C := by
        have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
        have ht2 : 1 ≤ t.2 := (Finset.mem_Icc.mp htS.2.2).1
        refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter7, Finset.mem_filter, Finset.mem_univ,
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
        rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_card_le_three7 ρ μG hN hN3
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
  have hSeq : S = {(1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} := by
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
    Finset.sum_insert (by
        simp [Prod.ext_iff]),
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring

/-- **The card-3 fiber.** Over a 3-support
`{P, Q, R}`, the fiber is the fifteen positive
exponent triples summing to `7` (parametrized by
`(k P, k Q, k R)`); the fiber sum evaluates to the
`(5,1,1)` terms at coefficient `42`, the `(4,2,1)`
terms at coefficient `105`, the `(3,3,1)` terms at
coefficient `140`, and the `(3,2,2)` terms at
coefficient `210` — the card-3 patterns of
`kappa7Const`, each with all its permutations. The
order-7 analogue of `fiber_card_three6` — the third
constant fiber. -/
theorem fiber_card_three7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 3) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 42 * (densMomentValue ρ μG 5
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
        + 42 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 5 * densMomentValue ρ μG 1))
        + 42 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 5))
        + 105 * (densMomentValue ρ μG 4
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
        + 105 * (densMomentValue ρ μG 4
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
        + 105 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 4 * densMomentValue ρ μG 1))
        + 105 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4))
        + 105 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 4 * densMomentValue ρ μG 2))
        + 105 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 4))
        + 140 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
        + 140 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
        + 140 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 3))
        + 210 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 2))
        + 210 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2))
        + 210 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3)) := by
  classical
  obtain ⟨P, Q, R, hPQ, hPR, hQR, hCeq⟩ :=
    Finset.card_eq_three.mp hC
  set S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 5 ×ˢ Finset.Icc 1 5 ×ˢ Finset.Icc 1 5).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 7) with hS
  have hnotP : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPR⟩
  have hnotQ : Q ∉ ({R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hQR
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (5040
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
      have htS : t.1 + t.2.1 + t.2.2 = 7
          ∧ t.1 ∈ Finset.Icc 1 5 ∧ t.2.1 ∈ Finset.Icc 1 5
          ∧ t.2.2 ∈ Finset.Icc 1 5 :=
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
        simp only [multSupport_eq_filter7, Finset.mem_filter, Finset.mem_univ,
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
      have hk7 : ∑ X ∈ Finset.univ, k X = 7 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 7 := by
        rw [← hsupp, ← sum_univ_eq_sum_multSupport7]
        exact hk7
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
      have hkP5 : k P ≤ 5 := by omega
      have hkQ5 : k Q ≤ 5 := by omega
      have hkR5 : k R ≤ 5 := by omega
      have hsumC' : k P + k Q + k R = 7 := by omega
      refine ⟨(k P, k Q, k R), ?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_product,
          Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          Finset.mem_Icc]
        exact ⟨⟨⟨hkP1, hkP5⟩, ⟨hkQ1, hkQ5⟩, ⟨hkR1, hkR5⟩⟩,
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
      have htS : t.1 + t.2.1 + t.2.2 = 7
          ∧ t.1 ∈ Finset.Icc 1 5 ∧ t.2.1 ∈ Finset.Icc 1 5
          ∧ t.2.2 ∈ Finset.Icc 1 5 :=
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
            else if X = R then t.2.2 else 0) X = 7 := by
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
          = 5040 / ((Nat.factorial t.1 * Nat.factorial t.2.1
              * Nat.factorial t.2.2 : ℕ) : ℝ) :=
        multinomial7_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : multSupport (fun X => if X = P then t.1
            else if X = Q then t.2.1
            else if X = R then t.2.2 else 0) = C := by
        refine Finset.ext fun X => ?_
        simp only [multSupport_eq_filter7, Finset.mem_filter, Finset.mem_univ,
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
        rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_card_le_three7 ρ μG hN hN3
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
  have hSeq : S = {(5, 1, 1), (1, 5, 1), (1, 1, 5),
      (4, 2, 1), (4, 1, 2), (2, 4, 1), (2, 1, 4),
      (1, 4, 2), (1, 2, 4), (3, 3, 1), (3, 1, 3),
      (1, 3, 3), (3, 2, 2), (2, 3, 2), (2, 2, 3)} := by
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
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩) <;>
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
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring

end Fiber7

/-! ## B7-2b-i close: what this brick owns, and the seam

This brick (B7-2b-i) owns: the order-7 fiber expansion
machinery — the integrated seventh-power expansion
(`integral_layerDensSum_pow_seven`), the migration
lemmas moving between the word-sum (piAntidiag over
all columns) and fiber-sum (grouped by `multSupport`)
presentations (`sum_univ_eq_sum_multSupport7`,
`integral_colDens_prod_pow_univ_seven`,
`sum_piAntidiag7_fiberwise`,
`fiber7_eq_empty_of_card_ne`,
`multinomial7_univ_eq`, `multSupport_eq_filter7`),
the small-support factorization engine in its order-7
form (the three `card_le_three7` / `triple_pow7`
theorems, proved by their exponent-blind order-6
counterparts), and the constant fibers: the card-1
fiber (pattern `(7)`, value `A₇`), the card-2 fiber
(splits `(6,1)`, `(5,2)`, `(4,3)` with reversals, at
coefficients `7, 21, 35, 35, 21, 7`), and the card-3
fiber (patterns `(5,1,1)`, `(4,2,1)`, `(3,3,1)`,
`(3,2,2)` with all permutations, at coefficients
`42, 105, 140, 210`). In each fiber the summand is
the B6 form: the multinomial coefficient of the
exponent function times the integral of the
column-density monomial over its multiplicity
support, and the constant fibers evaluate that
integral to the product of the columns'
`densMomentValue`s. **Not this brick**: the
card-by-card fiber accounting for cards 7/6/5/4
(B7-2b-ii / 2b-iii), the total decomposition, and
`kappa7dep_eq` (B7-2b-iv/v) are not asserted here;
B7-0's claims-to-check stay open. No sign is asserted
for `kappa7dep` or for any fiber sum here: the β⁷
general sign remains FRONTIER. NO CLAIM; parts of
the Clay Yang–Mills statement closed by this brick:
0; dials 0/4. -/

/-! ## B7-2b-ii: card-7 and card-6 fiber accounting

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this section: **0**.
Dials 0/4. This section is B7-2b-ii, appended to
`ThetLogos.PlaneCrossingBeta7Fibers` (B7-2b-i's fiber
machinery above), mirroring B6-2's
`PlaneCrossingBeta6Assembly` card-6 / card-5 fiber
accounting at one order up. Variable context, named
exactly: general `(G, ρ)` in the β-line's section
context (no irreducibility); the fiber evaluations
additionally carry `Even N`, `3 ≤ N`, and continuity
of `g ↦ repMatrix ρ g`, as at order 6. This section
owns the card-7 fiber (the all-distinct support,
pattern `(1,1,1,1,1,1,1)`, single pattern per support,
multinomial coefficient `5040`, value the septuple
pattern value below) and the card-6 fiber (pattern
`(2,1,1,1,1,1)` only: exactly six patterns per
6-support, one per doubled column, multinomial
coefficient `2520`, values the doubled sextuple
pattern value below, in powersetCard form).

**B7-0's card-6 claim, status.** The fiber-structure
part is settled HERE, in the predicted direction:
`fiber_card_six7` proves that over any 6-support the
order-7 fiber consists of exactly the six
`(2,1,1,1,1,1)` patterns (via B7-0's
`pattern_of_card_six_seven`) — no other exponent
pattern occurs on a 6-support. The remaining part of
the claim — the split of the summed card-6 fibers
over the support families (`C₆` and `Θ(2,2,2)` LIVE,
the rest factoring by the private-column erasure
recursion, via B7-1's doubled strips) — is NOT
settled here: it is assembly-side work, deferred to
B7-2b-iii, named. **Not this section**: cards 5/4
accounting (B7-2b-iii), the total decomposition, and
`kappa7dep_eq` (B7-2b-iv/v) are not asserted; no sign
is asserted for any fiber sum: the β⁷ general sign is
FRONTIER. -/

section Fiber7b

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The septuple pattern value.** For a 7-support
`C`, the all-distinct density value is the fully-split
baseline `B⁷` plus `d⁻⁴` times the sum of the order-4
excesses of its 4-subsupports, minus `d⁻⁵` times the
sum of the order-5 excesses of its 5-subsupports, plus
`d⁻⁶` times the sum of the order-6 excesses of its
6-subsupports, minus `d⁻⁷` times the sevenfold excess
`heptaReMoment C − e₁⁷`. Proved by the subset expansion
over the powerset of `C`: subsets of size at most `3`
factor, the 4-, 5- and 6-subsets contribute their
excesses at weights `c⁴`, `c⁵`, `c⁶`, and the top
subset contributes the sevenfold excess at weight
`c⁷`, with `c = −d⁻¹`. The mirror of
`integral_colDens_prod_sextuple` at one support size
up, with one extra subset level. -/
theorem integral_colDens_prod_septuple (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 7) :
    ∫ α : LayerSite N → G, ∏ Q ∈ C, colDensC ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 7
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 6 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
        - ((d : ℝ)⁻¹) ^ 7
          * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hc7 : c ^ 7 = -((d : ℝ)⁻¹) ^ 7 := by rw [hc]; ring
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
          + (if T ∈ Finset.powersetCard 6 C then
              c ^ 6 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
             else 0)
          + (if T = C then
              c ^ 7 * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C := Finset.mem_powerset.mp hT
    rw [integral_const_mul]
    by_cases hT7 : T = C
    · subst hT7
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
      have hnotpc6 : T ∉ Finset.powersetCard 6 T :=
        fun h => by
          have h6 := (Finset.mem_powersetCard.mp h).2
          rw [hC] at h6
          exact absurd h6 (by norm_num)
      rw [if_neg hnotpc4, if_neg hnotpc5, if_neg hnotpc6,
        if_pos rfl, hC]
      show c ^ 7 * heptaReMoment ρ μG T u u'
        = c ^ 7 * (e1 ρ μG) ^ 7 + 0 + 0 + 0
          + c ^ 7 * (heptaReMoment ρ μG T u u' - (e1 ρ μG) ^ 7)
      ring
    · rw [if_neg hT7]
      by_cases hT6 : T ∈ Finset.powersetCard 6 C
      · have hcard6 : T.card = 6 :=
          (Finset.mem_powersetCard.mp hT6).2
        have hnotpc4 : T ∉ Finset.powersetCard 4 C :=
          fun h => by
            have h4 := (Finset.mem_powersetCard.mp h).2
            rw [hcard6] at h4
            exact absurd h4 (by norm_num)
        have hnotpc5 : T ∉ Finset.powersetCard 5 C :=
          fun h => by
            have h5 := (Finset.mem_powersetCard.mp h).2
            rw [hcard6] at h5
            exact absurd h5 (by norm_num)
        rw [if_neg hnotpc4, if_neg hnotpc5, if_pos hT6, hcard6]
        show c ^ 6 * quadReMoment ρ μG T u u'
          = c ^ 6 * (e1 ρ μG) ^ 6 + 0 + 0
            + c ^ 6 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
            + 0
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
              + 0 + 0
          ring
        · rw [if_neg hT5]
          by_cases hT4 : T ∈ Finset.powersetCard 4 C
          · rw [if_pos hT4]
            have hcard4 : T.card = 4 :=
              (Finset.mem_powersetCard.mp hT4).2
            rw [hcard4]
            show c ^ 4 * quadReMoment ρ μG T u u'
              = c ^ 4 * (e1 ρ μG) ^ 4
                + c ^ 4 * (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4)
                + 0 + 0 + 0
            ring
          · rw [if_neg hT4, add_zero, add_zero, add_zero, add_zero]
            have hcard : T.card ≤ 3 := by
              have h1 : T.card ≤ 7 := le_trans
                (Finset.card_le_card hsub) (le_of_eq hC)
              have hne4 : T.card ≠ 4 := fun h4 =>
                hT4 (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
              have hne5 : T.card ≠ 5 := fun h5 =>
                hT5 (Finset.mem_powersetCard.mpr ⟨hsub, h5⟩)
              have hne6 : T.card ≠ 6 := fun h6 =>
                hT6 (Finset.mem_powersetCard.mpr ⟨hsub, h6⟩)
              have hne7 : T.card ≠ 7 := fun h7 =>
                hT7 (Finset.eq_of_subset_of_card_le hsub
                  (by rw [hC]; omega))
              omega
            rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3
              hρcont u u' T hcard]
  have hBase7 : (∑ T ∈ C.powerset, c ^ T.card * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 7 := by
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
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 7 := by
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
  have hMid6 : (∑ T ∈ C.powerset,
        (if T ∈ Finset.powersetCard 6 C then
          c ^ 6 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
         else 0))
      = c ^ 6 * ∑ T ∈ Finset.powersetCard 6 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6) := by
    have hsubpc : Finset.powersetCard 6 C ⊆ C.powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ C.powerset,
          (if T ∈ Finset.powersetCard 6 C then
            c ^ 6 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
           else 0))
        = ∑ T ∈ Finset.powersetCard 6 C,
            c ^ 6 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6) :=
      (Finset.sum_subset hsubpc (fun T _ hT => if_neg hT)).symm.trans
        (Finset.sum_congr rfl fun T hT => if_pos hT)
    rw [step1, ← Finset.mul_sum]
  have hTop7 : (∑ T ∈ C.powerset,
        (if T = C then
          c ^ 7 * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)
         else 0))
      = c ^ 7 * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7) := by
    rw [Finset.sum_ite_eq' C.powerset C
      (fun _ => c ^ 7
        * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun T _ =>
      Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl
              fun Q _ => pow_one (colRe ρ u u' Q α))) _),
    Finset.sum_congr rfl hval, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hBase7,
    hMid4, hMid5, hMid6, hTop7, hc4, hc5, hc6, hc7]
  ring

/-- **The card-7 fiber.** Over a 7-support `C`, the
fiber of the expansion is the single all-ones pattern:
every exponent on the support is `1` (B7-0's
`eq_one_of_card_seven`, since the exponents sum to `7`
over a 7-element support of exponents at least `1`),
its multinomial coefficient is `5040`, and its value
is the septuple pattern value. This is the pattern
feeding the `Θ(1,3,3)`-book and `C₆`-side channels
when the fibers are summed over their support
families in the later assembly bricks. -/
theorem fiber_card_seven7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 7) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 5040 * ((1 - e1 ρ μG / (d : ℝ)) ^ 7
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)) := by
  classical
  have hfib : (Finset.piAntidiag Finset.univ 7).filter
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
      have hk7 : ∑ P ∈ Finset.univ, k P = 7 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
      have hcard : (multSupport k).card = 7 := by rw [hsupp]; exact hC
      funext P
      by_cases hP : P ∈ C
      · have hPs : P ∈ multSupport k := hsupp ▸ hP
        rw [eq_one_of_card_seven k hk7 hcard P hPs, if_pos hP]
      · have hPs : P ∉ multSupport k := hsupp ▸ hP
        have hk0 : k P = 0 := by
          by_contra hne
          exact hPs (Finset.mem_filter.mpr
            ⟨Finset.mem_univ P, hne⟩)
        rw [hk0, if_neg hP]
  rw [hfib, Finset.sum_singleton]
  have hmult : (Nat.multinomial Finset.univ
        (fun P => if P ∈ C then 1 else 0) : ℝ) = 5040 := by
    have hp : ∏ P ∈ Finset.univ,
        Nat.factorial ((fun P => if P ∈ C then 1 else 0) P)
          = 1 := by
      exact (Finset.prod_subset (Finset.subset_univ C)
        (fun P _ hP => by simp [hP])).symm.trans
        (Finset.prod_eq_one fun P _ => by
          by_cases hP : P ∈ C <;> simp [hP])
    have hk7 : ∑ P ∈ Finset.univ,
        (fun P => if P ∈ C then 1 else 0) P = 7 := by
      have h1 : ∀ P ∈ Finset.univ,
          (fun P => if P ∈ C then (1 : ℕ) else 0) P
            = if P ∈ C then 1 else 0 := fun P _ => rfl
      rw [Finset.sum_congr rfl h1, Finset.sum_boole]
      simp [hC]
    have h := multinomial7_univ_eq
      (fun P => if P ∈ C then 1 else 0) hk7 1 hp one_ne_zero
    rw [h]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ,
          (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 7
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 6 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
        - ((d : ℝ)⁻¹) ^ 7
          * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7) := by
    have hsupp : multSupport (fun P => if P ∈ C then 1 else 0)
        = C := by
      refine Finset.ext fun P => ?_
      simp only [multSupport, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases hP : P ∈ C <;> simp [hP]
    rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont u u'
      (fun P => if P ∈ C then 1 else 0), hsupp]
    have hprod : ∀ α : LayerSite N → G,
        ∏ P ∈ C, (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
          = ∏ P ∈ C, colDensC ρ u u' P α :=
      fun α => Finset.prod_congr rfl fun P hP => by
        simp [hP]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_septuple ρ μG hN hN3 hρcont
      u u' C hC
  rw [hmult, hval]

/-- The `(2,1,1,1,1,1)` pattern at `(C, P)`: exponent
`2` at `P`, exponent `1` on the rest of `C`, `0` off
`C`. The order-7 analogue of `doubledPentaPattern`. -/
noncomputable def doubledSextuplePattern (C : Finset (LayerColumn N))
    (P : LayerColumn N) : LayerColumn N → ℕ :=
  fun Q => if Q = P then 2 else if Q ∈ C then 1 else 0

/-- **The doubled sextuple pattern value.** For a
6-support `C` and a distinguished column `P ∈ C`, the
`(2,1,1,1,1,1)` density pattern value splits into its
fully-split baseline `A₂B⁵`, the order-4 and order-5
excesses of the 4- and 5-subsupports of the erased
support `C.erase P` at weights `d⁻⁴` and `−d⁻⁵`, twice
the order-4 and order-5 excesses of the 4- and
5-subsupports through `P` at weights `d⁻⁴` and
`−d⁻⁵`, twice the sixfold excess at weight `d⁻⁶`, the
doubled excesses of the 4- and 5-subsupports through
`P` at weights `−d⁻⁵` and `d⁻⁶`, and the doubled
6-support excess at weight `−d⁻⁷`. Proved by the
two-level subset expansion: `x_P²` by `add_pow` over
`range 3`, the remaining five densities by the
powerset expansion — the mirror of
`integral_colDens_prod_quintuple_doubled` at one
support size up, with the subset sums kept in
powersetCard form (as in
`integral_colDens_prod_septuple`), not converted to
erasure sums. -/
theorem integral_colDens_prod_sextuple_doubled (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledHexaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hRcard : (C.erase P).card = 5 := by
    rw [Finset.card_erase_of_mem hP, hC]
  have hnotP : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
  have hc6 : c ^ 6 = ((d : ℝ)⁻¹) ^ 6 := by rw [hc]; ring
  have hc7 : c ^ 7 = -((d : ℝ)⁻¹) ^ 7 := by rw [hc]; ring
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
          + (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
             else 0)
          + (if T = C.erase P then
              (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    by_cases hTS : T = C.erase P
    · subst hTS
      have hnotpc : (C.erase P) ∉ Finset.powersetCard 4 (C.erase P) :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h4
          omega
      rw [if_neg hnotpc, if_pos rfl, hRcard]
      show quadReMoment ρ μG (C.erase P) u u'
        = (e1 ρ μG) ^ 5 + 0
          + (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
      ring
    · rw [if_neg hTS]
      by_cases hT4 : T ∈ Finset.powersetCard 4 (C.erase P)
      · rw [if_pos hT4]
        have hcardT : T.card = 4 :=
          (Finset.mem_powersetCard.mp hT4).2
        rw [hcardT]
        show quadReMoment ρ μG T u u'
          = (e1 ρ μG) ^ 4
            + (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) + 0
        ring
      · rw [if_neg hT4, add_zero, add_zero]
        have hcardT : T.card ≤ 3 := by
          have h1 : T.card ≤ 5 := le_trans (Finset.card_le_card hsub)
            (le_of_eq hRcard)
          have hne5 : T.card ≠ 5 := fun h5 => hTS
            (Finset.eq_of_subset_of_card_le hsub
              (by rw [hRcard]; omega))
          have hne4 : T.card ≠ 4 := fun h4 => hT4
            (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
          omega
        rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
          u u' T hcardT]
  have hB : ∀ T ∈ (C.erase P).powerset,
      ∫ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ T, colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (e1 ρ μG) ^ (T.card + 1)
          + (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
             else 0)
          + (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
             else 0)
          + (if T = C.erase P then
              (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    have hPT : P ∉ T := fun h => hnotP (hsub h)
    by_cases hTS : T = C.erase P
    · subst hTS
      have hnotpc3 : (C.erase P) ∉ Finset.powersetCard 3 (C.erase P) :=
        fun h => by
          have h3 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h3
          omega
      have hnotpc4 : (C.erase P) ∉ Finset.powersetCard 4 (C.erase P) :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h4
          omega
      rw [if_neg hnotpc3, if_neg hnotpc4, if_pos rfl, hRcard]
      have hpt : ∀ α : LayerSite N → G,
          colRe ρ u u' P α * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
          = ∏ Q ∈ C, colRe ρ u u' Q α := fun α =>
        Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hP
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      show hexaReMoment ρ μG C u u'
        = (e1 ρ μG) ^ (5 + 1) + 0 + 0
          + (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
      ring
    · rw [if_neg hTS]
      by_cases hT4 : T ∈ Finset.powersetCard 4 (C.erase P)
      · rw [if_pos hT4]
        have hnotpc3 : T ∉ Finset.powersetCard 3 (C.erase P) :=
          fun h => by
            have h3 := (Finset.mem_powersetCard.mp h).2
            have h4 := (Finset.mem_powersetCard.mp hT4).2
            omega
        rw [if_neg hnotpc3]
        have hcardT : T.card = 4 :=
          (Finset.mem_powersetCard.mp hT4).2
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
          = (e1 ρ μG) ^ (4 + 1) + 0
            + (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 5) + 0
        ring
      · rw [if_neg hT4]
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
                - (e1 ρ μG) ^ 4) + 0 + 0
          ring
        · rw [if_neg hT3, add_zero, add_zero, add_zero]
          have hcardT : T.card ≤ 2 := by
            have h1 : T.card ≤ 5 := le_trans
              (Finset.card_le_card hsub) (le_of_eq hRcard)
            have hne5 : T.card ≠ 5 := fun h5 => hTS
              (Finset.eq_of_subset_of_card_le hsub
                (by rw [hRcard]; omega))
            have hne4 : T.card ≠ 4 := fun h4 => hT4
              (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
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
            integral_colRe_prod_pow_card_le_three7 ρ μG hN hN3
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
          + (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
             else 0)
          + (if T = C.erase P then
              (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C.erase P := Finset.mem_powerset.mp hT
    have hPT : P ∉ T := fun h => hnotP (hsub h)
    by_cases hTS : T = C.erase P
    · subst hTS
      have hnotpc3 : (C.erase P) ∉ Finset.powersetCard 3 (C.erase P) :=
        fun h => by
          have h3 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h3
          omega
      have hnotpc4 : (C.erase P) ∉ Finset.powersetCard 4 (C.erase P) :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hRcard] at h4
          omega
      rw [if_neg hnotpc3, if_neg hnotpc4, if_pos rfl, hRcard]
      show doubledHexaReMoment ρ μG C P u u'
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 5 + 0 + 0
          + (doubledHexaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      ring
    · rw [if_neg hTS]
      by_cases hT4 : T ∈ Finset.powersetCard 4 (C.erase P)
      · rw [if_pos hT4]
        have hnotpc3 : T ∉ Finset.powersetCard 3 (C.erase P) :=
          fun h => by
            have h3 := (Finset.mem_powersetCard.mp h).2
            have h4 := (Finset.mem_powersetCard.mp hT4).2
            omega
        rw [if_neg hnotpc3]
        have hcardT : T.card = 4 :=
          (Finset.mem_powersetCard.mp hT4).2
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
      · rw [if_neg hT4]
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
        · rw [if_neg hT3, add_zero, add_zero, add_zero]
          have hcardT : T.card ≤ 2 := by
            have h1 : T.card ≤ 5 := le_trans (Finset.card_le_card hsub)
              (le_of_eq hRcard)
            have hne5 : T.card ≠ 5 := fun h5 => hTS
              (Finset.eq_of_subset_of_card_le hsub
                (by rw [hRcard]; omega))
            have hne4 : T.card ≠ 4 := fun h4 => hT4
              (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
            have hne3 : T.card ≠ 3 := fun h3 => hT3
              (Finset.mem_powersetCard.mpr ⟨hsub, h3⟩)
            omega
          rw [integral_congr_ae (Filter.Eventually.of_forall
              fun α => hcong T hsub 2 α),
            integral_colRe_prod_pow_card_le_three7 ρ μG hN hN3
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
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
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
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 5)
               else 0)
            + (if T = C.erase P then
                (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
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
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (doubledHexaReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
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
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
    calc ∑ T ∈ (C.erase P).powerset, (c * e1 ρ μG) ^ T.card
        = ∑ T ∈ (C.erase P).powerset,
            (∏ Q ∈ T, (c * e1 ρ μG))
              * ∏ Q ∈ (C.erase P) \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const, Finset.prod_const_one, mul_one]
      _ = ∏ Q ∈ C.erase P, (c * e1 ρ μG + 1) :=
          (Finset.prod_add _ _ _).symm
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
          rw [Finset.prod_const, hRcard]
          congr 1
          rw [div_eq_inv_mul]
          ring
  have hB0base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
    have hT0 : ∀ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (e1 ρ μG) ^ T.card
          = (c * e1 ρ μG) ^ T.card := by
      intro T _
      simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
        one_mul]
      exact (mul_pow _ _ _).symm
    exact (Finset.sum_congr rfl hT0).trans hBS
  have hB0pc4 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
             else 0))
      = ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have hsubpc : Finset.powersetCard 4 (C.erase P)
        ⊆ (C.erase P).powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ (C.erase P).powerset,
          ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
               else 0))
        = ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
              * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
      (Finset.sum_subset hsubpc (fun T _ hT => by
        rw [if_neg hT, mul_zero])).symm.trans
        (Finset.sum_congr rfl fun T hT => by rw [if_pos hT])
    have step2 : (∑ T ∈ Finset.powersetCard 4 (C.erase P),
          ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        = ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 4 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (0 + 4 : ℕ) = 4 from rfl, hc4]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [step1, step2]
  have hB0top : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (if T = C.erase P then
              (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
             else 0))
      = -(((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [show (0 + 5 : ℕ) = 5 from rfl, hc5]
    ring
  have hB0 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * ((e1 ρ μG) ^ T.card
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
               else 0)))
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5) := by
    rw [Finset.sum_congr rfl (fun T _ => by
        rw [mul_add, mul_add]),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hB0base,
      hB0pc4, hB0top]
    ring

  have hB1base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (e1 ρ μG) ^ (T.card + 1))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
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
  have hB1mid3 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
             else 0))
      = 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4) := by
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
  have hB1mid4 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
             else 0))
      = -(2 * ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)) := by
    have hsubpc : Finset.powersetCard 4 (C.erase P)
        ⊆ (C.erase P).powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ (C.erase P).powerset,
          ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 5)
               else 0))
        = ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
              * (quadReMoment ρ μG (insert P T) u u'
                - (e1 ρ μG) ^ 5) :=
      (Finset.sum_subset hsubpc (fun T _ hT => by
        rw [if_neg hT, mul_zero])).symm.trans
        (Finset.sum_congr rfl fun T hT => by rw [if_pos hT])
    have step2 : (∑ T ∈ Finset.powersetCard 4 (C.erase P),
          ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
            * (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 5))
        = -(2 * ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u'
              - (e1 ρ μG) ^ 5)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 4 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (1 + 4 : ℕ) = 5 from rfl, hc5]
      simp only [Nat.choose_one_right, Nat.cast_ofNat]
      ring
    rw [step1, step2]
  have hB1top : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T = C.erase P then
              (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
             else 0))
      = 2 * ((d : ℝ)⁻¹) ^ 6
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard]
    rw [show (1 + 5 : ℕ) = 6 from rfl, hc6]
    simp only [Nat.choose_one_right, Nat.cast_ofNat]
  have hB1 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 4)
               else 0)
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (quadReMoment ρ μG (insert P T) u u'
                  - (e1 ρ μG) ^ 5)
               else 0)
            + (if T = C.erase P then
                (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
               else 0)))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 5
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) := by
    rw [Finset.sum_congr rfl (fun T _ => by
        rw [mul_add, mul_add, mul_add]),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hB1base, hB1mid3, hB1mid4, hB1top]
    ring

  have hB2base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
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
  have hB2mid3 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T ∈ Finset.powersetCard 3 (C.erase P) then
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
      = -(((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
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
        = -(((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 3 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (2 + 3 : ℕ) = 5 from rfl, hc5]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
      ring
    rw [step1, step2]
  have hB2mid4 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T ∈ Finset.powersetCard 4 (C.erase P) then
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
             else 0))
      = ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    have hsubpc : Finset.powersetCard 4 (C.erase P)
        ⊆ (C.erase P).powerset :=
      fun T hT => Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp hT).1
    have step1 : (∑ T ∈ (C.erase P).powerset,
          ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
               else 0))
        = ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
              * (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
      (Finset.sum_subset hsubpc (fun T _ hT => by
        rw [if_neg hT, mul_zero])).symm.trans
        (Finset.sum_congr rfl fun T hT => by rw [if_pos hT])
    have step2 : (∑ T ∈ Finset.powersetCard 4 (C.erase P),
          ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
            * (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
        = ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hcardT : T.card = 4 :=
        (Finset.mem_powersetCard.mp hT).2
      rw [hcardT, show (2 + 4 : ℕ) = 6 from rfl, hc6]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
    rw [step1, step2]
  have hB2top : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T = C.erase P then
              (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
             else 0))
      = -(((d : ℝ)⁻¹) ^ 7
          * (doubledHexaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (doubledHexaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hRcard, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show (2 + 5 : ℕ) = 7 from rfl, hc7]
    ring
  have hB2 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T ∈ Finset.powersetCard 3 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)
            + (if T ∈ Finset.powersetCard 4 (C.erase P) then
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
               else 0)
            + (if T = C.erase P then
                (doubledHexaReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
               else 0)))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 5
        - ((d : ℝ)⁻¹) ^ 5
          * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 6
          * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
            (doubledQuadReMoment ρ μG (insert P T) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledHexaReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
    rw [Finset.sum_congr rfl (fun T _ => by
        rw [mul_add, mul_add, mul_add]),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hB2base, hB2mid3, hB2mid4, hB2top]
    ring

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
    _ = ((1 - e1 ρ μG / (d : ℝ)) ^ 5
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5))
          + ((2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))
          + ((c ^ 2 * realMoment ρ μG 2)
              * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
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
    _ = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
          + 2 * ((d : ℝ)⁻¹) ^ 6
            * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 7
            * (doubledHexaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
        rw [hA2]
        ring

/-- **The card-6 fiber.** Over a 6-support `C`, the
fiber of the expansion is the six doubled patterns
(one per `P ∈ C`): the pattern is `(2,1,1,1,1,1)` by
B7-0's `pattern_of_card_six_seven`. Each pattern has
multinomial coefficient `2520` and value the doubled
sextuple pattern value. These are the fibers feeding
the `kappa7chan211111C6` / `Θ` excesses of B7-2a when
summed over their support families. -/
theorem fiber_card_six7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (2520 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            + ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
  classical
  have hsuppPat : ∀ P ∈ C,
      multSupport (doubledSextuplePattern C P) = C := by
    intro P hP
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hQP : Q = P
    · subst hQP
      simp [doubledSextuplePattern, hP]
    · by_cases hQC : Q ∈ C <;>
        simp [doubledSextuplePattern, hQP, hQC]
  have hsumPat : ∀ P ∈ C,
      ∑ Q ∈ Finset.univ, doubledSextuplePattern C P Q = 7 := by
    intro P hP
    have h1 : ∑ Q ∈ Finset.univ, doubledSextuplePattern C P Q
        = ∑ Q ∈ C, doubledSextuplePattern C P Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
          simp [doubledSextuplePattern, hQ, hQP])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP]
    have h2 : ∀ Q ∈ C.erase P, doubledSextuplePattern C P Q = 1 :=
      fun Q hQ => by
        simp [doubledSextuplePattern, (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP, hC]
    have hPP : doubledSextuplePattern C P P = 2 := by
      simp [doubledSextuplePattern]
    rw [hPP]
    decide
  have hmemPat : ∀ P ∈ C, doubledSextuplePattern C P
      ∈ (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C) := by
    intro P hP
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsumPat P hP, fun Q _ => Finset.mem_univ Q⟩,
      hsuppPat P hP⟩
  have hvalPat : ∀ P ∈ C,
      ((Nat.multinomial Finset.univ (doubledSextuplePattern C P) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ Q ∈ Finset.univ,
                (colDensC ρ u u' Q α) ^ (doubledSextuplePattern C P Q)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (2520 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            + ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
    intro P hP
    have hfact : ∏ Q ∈ Finset.univ,
        Nat.factorial (doubledSextuplePattern C P Q) = 2 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial (doubledSextuplePattern C P Q)
          = ∏ Q ∈ C, Nat.factorial (doubledSextuplePattern C P Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
            simp [doubledSextuplePattern, hQ, hQP])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP]
      have h2 : ∀ Q ∈ C.erase P,
          Nat.factorial (doubledSextuplePattern C P Q) = 1 :=
        fun Q hQ => by
          simp [doubledSextuplePattern, (Finset.mem_erase.mp hQ).1,
            (Finset.mem_erase.mp hQ).2]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      simp [doubledSextuplePattern]
    have hmult : (Nat.multinomial Finset.univ
          (doubledSextuplePattern C P) : ℝ) = 2520 := by
      have h := multinomial7_univ_eq (doubledSextuplePattern C P)
        (hsumPat P hP) 2 hfact two_ne_zero
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ Q ∈ Finset.univ,
            (colDensC ρ u u' Q α) ^ (doubledSextuplePattern C P Q)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
          - 2 * ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
          + 2 * ((d : ℝ)⁻¹) ^ 6
            * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
              (doubledQuadReMoment ρ μG (insert P T) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 7
            * (doubledHexaReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont u u'
        (doubledSextuplePattern C P), hsuppPat P hP]
      have hprod : ∀ α : LayerSite N → G,
          ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (doubledSextuplePattern C P Q)
            = ∏ Q ∈ C,
              (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1) :=
        fun α => Finset.prod_congr rfl fun Q hQ => by
          by_cases hQP : Q = P <;> simp [doubledSextuplePattern, hQP, hQ]
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
      exact integral_colDens_prod_sextuple_doubled ρ μG hN hN3
        hρcont u u' C hC P hP
    rw [hmult, hint]
  have hsurj : ∀ k ∈ (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C),
      ∃ P, ∃ _ : P ∈ C, doubledSextuplePattern C P = k := by
    intro k hk
    have hk7 : ∑ Q ∈ Finset.univ, k Q = 7 :=
      (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
    have hsupp : multSupport k = C := (Finset.mem_filter.mp hk).2
    have hcard : (multSupport k).card = 6 := by rw [hsupp]; exact hC
    obtain ⟨P₀, hP₀S, hkP₀, hrest⟩ :=
      pattern_of_card_six_seven k hk7 hcard
    have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
    refine ⟨P₀, hP₀C, ?_⟩
    funext Q
    by_cases hQP : Q = P₀
    · rw [hQP, hkP₀]
      simp [doubledSextuplePattern]
    · by_cases hQC : Q ∈ C
      · have hkQ : k Q = 1 := hrest Q (hsupp ▸ hQC) hQP
        rw [hkQ]
        simp [doubledSextuplePattern, hQP, hQC]
      · have hkQ : k Q = 0 := by
          by_contra hne
          have hQs : Q ∈ multSupport k := Finset.mem_filter.mpr
            ⟨Finset.mem_univ Q, hne⟩
          rw [hsupp] at hQs
          exact hQC hQs
        rw [hkQ]
        simp [doubledSextuplePattern, hQP, hQC]
  exact (Finset.sum_bij (fun P _ => doubledSextuplePattern C P)
    hmemPat
    (fun P hP P' hP' h => by
      by_contra hne
      have h2 := congrFun h P
      simp [doubledSextuplePattern, hne, hP] at h2)
    hsurj
    (fun P hP => (hvalPat P hP).symm)).symm

end Fiber7b

/-! ## B7-2b-ii close: what this brick owns, and the seam

This brick (B7-2b-ii) owns: the septuple pattern value
(`integral_colDens_prod_septuple`: baseline `B⁷`, the
4-, 5- and 6-subsupport excess sums at weights `d⁻⁴`,
`−d⁻⁵`, `d⁻⁶`, and the sevenfold excess
`heptaReMoment C − e₁⁷` at weight `−d⁻⁷`); the card-7
fiber (`fiber_card_seven7`: over any 7-support the
fiber is the single `(1⁷)` pattern, multinomial
coefficient `5040`, value `5040` times the septuple
pattern value); the doubled sextuple pattern value
(`integral_colDens_prod_sextuple_doubled`, in
powersetCard form); and the card-6 fiber
(`fiber_card_six7`: over any 6-support the fiber is
exactly the six `(2,1,1,1,1,1)` patterns, one per
doubled column, each of multinomial coefficient
`2520` and value the doubled sextuple pattern value).
**B7-0's card-6 claim**: its fiber-structure part is
settled here in the predicted direction (the card-6
fibers are exactly the `(2,1,1,1,1,1)` patterns, via
B7-0's `pattern_of_card_six_seven`); its family-split
part (`C₆` / `Θ(2,2,2)` LIVE, the rest erasure) is
assembly-side and is deferred to B7-2b-iii, named.
No per-support adjacent/opposite-style count arises
in the card-6 accounting here (the doubled column is
the only distinguished data, counted by the six
patterns themselves); any such count in the later
family split is carried there as B7-2a carried its
counts — defined, not fitted. **Not this brick**:
cards 5/4 accounting (B7-2b-iii), the total
decomposition, and `kappa7dep_eq` (B7-2b-iv/v) are
not asserted here. No sign is asserted for
`kappa7dep` or for any fiber sum here: the β⁷ general
sign remains FRONTIER. NO CLAIM; parts of the Clay
Yang–Mills statement closed by this brick: 0; dials
0/4. -/

/-! ## B7-2b-iii: card-5 / card-4 accounting, the
B7-0 settlements, and the ADJ/OPP counts

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this section: **0**.
Dials 0/4. This section is B7-2b-iii, appended to
`ThetLogos.PlaneCrossingBeta7Fibers` (B7-2b-i/ii
above), mirroring B6-2's card-5 / card-4 fiber
accounting at one order up. Variable context, named
exactly: general `(G, ρ)` in the β-line's section
context (no irreducibility); the fiber evaluations
additionally carry `Even N`, `3 ≤ N`, and continuity
of `g ↦ repMatrix ρ g`, as at order 6. This section
owns: the card-5 fiber (patterns `(3,1,1,1,1)`,
multinomial `840`, and `(2,2,1,1,1)`, multinomial
`1260` carried at fiber coefficient `630` per ordered
pair after the two-to-one pattern symmetry) and the
card-4 fiber (patterns `(4,1,1,1)`, multinomial
`210`, `(3,2,1,1)`, multinomial `420`, and
`(2,2,2,1)`, multinomial `630` carried at fiber
coefficient `105` per ordered triple after the
six-to-one pattern symmetry), each fiber decomposed
per pattern with its pattern
values in closed form through ONE generic engine:
the binomial expansion of the density monomial
`∏ (c·r_P + 1)^(k P)` (with `c = -d⁻¹`), whose value
is the explicit finite sum, over all exponent choices
`j ≤ k` on the support, of the binomial coefficient
times the generalized character moment
`colReMomentPow`. The top generalized moment of each
pattern (`j = k`) is identified with the pattern's
named channel moment (the B7-1b quad moments at card
4; the penta moments at card 5, two of them new
here); every other term has `j` supported on a proper
subsupport or with strictly smaller exponents — the
lower-order data the erasure recursion feeds on.

**The settlements, stated here and proved below.**
(1) **B7-0's card-5 claim** ("the `(3,1,1,1,1)` /
`(2,2,1,1,1)` card is erased through the lower
excesses", B7-0 §5): **CONFIRMED in the predicted
direction.** The card-5 fibers consist of exactly
those two patterns (`fiber_card_five7`, via B7-0's
`patterns_of_card_five_seven`); every order-7
configuration on a 5-support has a private column
(B7-0's `card_five_erasure_death`, landed); and the
two card-5 top moments factor at a private column
through card-4 moments (`tripledPentaReMoment` and
`doubledDoubledPentaReMoment` strip lemmas below),
while every non-top term of the pattern values is a
generalized moment at a non-channel exponent, equal
to its moment over its own exponent support inside
the fiber support (`colReMomentPow_support_reduce`;
a proper subsupport whenever some exponent
vanishes). The
card-5 card therefore carries no live channel: it
dies by the private-column erasure recursion, as
predicted. (2) **B7-0's card-6 claim, family-split
part** (deferred from B7-2b-ii by name): **SETTLED
in the predicted direction.** The summed card-6
fibers over all 6-supports split as the `C₆` family
sum plus the `Θ(2,2,2)` family sum plus the rest
(`card_six_fiber_split`), the two families are
exactly the LIVE supports (every 6-support is a `C₆`
pattern, a `Θ(2,2,2)` pattern, or has a private
column — B7-0's `card_six_live_or_private` mechanism,
restated for bare supports as
`card_six_support_live_or_private` below), and on
the rest the doubled top moment factors by
private-column erasure through B7-1's doubled strips
(`doubledHexaReMoment_factor_of_private`). (3)
**B7-2a's ADJ/OPP counting sums**: the fiber
accounting at card 4 proves the per-quad counts
**CONSTANT**: in a primitive quad every column has
exactly two adjacent and one opposite partner (the
quad is a `C₄` pattern: all sites have degree `2` and
there is no digon pair), so `kappa7adjPairCount`
evaluates to `8 · |primitiveQuads|` and
`kappa7oppPairCount` to `4 · |primitiveQuads|`
(`kappa7adjPairCount_eq`, `kappa7oppPairCount_eq`).
**Not this section**: the total decomposition and
`kappa7dep_eq` (B7-2b-iv/v) are not asserted; no sign
is asserted for any fiber sum: the β⁷ general sign
is FRONTIER. -/

section Fiber7c

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The generalized character moment**: for a finite
set of columns `C` and an exponent function `a`, the
integral of `∏_{P ∈ C} (colRe P)^(a P)`. The named
moments of the β-line are its specializations:
`quadReMoment` at `a ≡ 1`, the doubled / tripled /
quadrupled quad moments at their multiplicity
patterns, the penta / hexa / hepta moments at `a ≡ 1`
on larger supports. -/
noncomputable def colReMomentPow (C : Finset (LayerColumn N))
    (a : LayerColumn N → ℕ) (u u' : LayerLink N → G) : ℝ :=
  ∫ α : LayerSite N → G, ∏ P ∈ C, (colRe ρ u u' P α) ^ (a P)
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The generalized moment at the constant exponent
`1` is `quadReMoment` (the moment construction is
support-size and pattern blind at exponent `1`). -/
theorem colReMomentPow_one (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C (fun _ => 1) u u'
      = quadReMoment ρ μG C u u' := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  exact Finset.prod_congr rfl fun P _ => pow_one _

/-- **The binomial expansion engine (universal
form).** For any exponent function `k`, the density
monomial integral over all columns expands over all
exponent choices `j ≤ k`: each column's density
`colDensC P = c · colRe P + 1` (with `c = -d⁻¹`)
contributes its binomial expansion (`Finset.prod_univ_sum`),
and the value is the explicit finite sum of the
binomial coefficients times the generalized character
moments over the universal support. -/
theorem integral_colDens_prod_pow_univ_eq_sum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (k : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset (fun P => Finset.range (k P + 1)),
          (∏ P ∈ Finset.univ, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
            * colReMomentPow ρ μG Finset.univ j u u' := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hx : ∀ (Z : LayerColumn N) (α : LayerSite N → G),
      colDensC ρ u u' Z α = c * colRe ρ u u' Z α + 1 := by
    intro Z α
    rw [colDensC_eq, div_eq_inv_mul]
    ring
  have hpt : ∀ α : LayerSite N → G,
      ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
        = ∑ j ∈ Fintype.piFinset
              (fun P => Finset.range (k P + 1)),
            ∏ P ∈ Finset.univ,
              (((k P).choose (j P) : ℝ) * c ^ (j P))
                * (colRe ρ u u' P α) ^ (j P) := by
    intro α
    have hfac : ∀ P ∈ Finset.univ,
        (colDensC ρ u u' P α) ^ (k P)
          = ∑ j ∈ Finset.range (k P + 1),
              ((k P).choose j : ℝ) * c ^ j
                * (colRe ρ u u' P α) ^ j := by
      intro P _
      rw [hx P α, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, one_pow, mul_one]
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_univ_sum]
  have hInt : ∀ j ∈ Fintype.piFinset
        (fun P => Finset.range (k P + 1)),
      Integrable (fun α : LayerSite N → G =>
          ∏ P ∈ Finset.univ,
            (((k P).choose (j P) : ℝ) * c ^ (j P))
              * (colRe ρ u u' P α) ^ (j P))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro j _
    have hfun : (fun α : LayerSite N → G =>
          ∏ P ∈ Finset.univ,
            (((k P).choose (j P) : ℝ) * c ^ (j P))
              * (colRe ρ u u' P α) ^ (j P))
        = fun α : LayerSite N → G =>
            (∏ P ∈ Finset.univ,
              ((k P).choose (j P) : ℝ) * c ^ (j P))
              * ∏ P ∈ Finset.univ,
                (colRe ρ u u' P α) ^ (j P) := by
      funext α
      rw [Finset.prod_mul_distrib]
    rw [hfun]
    exact Integrable.const_mul
      (integrable_colRe_prod_pow ρ μG hρcont u u'
        Finset.univ j) _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ hInt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
    Finset.prod_mul_distrib (s := Finset.univ)
      (f := fun P => ((k P).choose (j P) : ℝ) * c ^ (j P))
      (g := fun P => (colRe ρ u u' P α) ^ (j P))),
    integral_const_mul]
  rfl

/-- **The binomial expansion engine (support form).**
For an exponent function `k` vanishing off a finite
support `C`, the density monomial integral over `C`
is the finite sum, over all exponent choices
`j ≤ k`, of the binomial coefficient (a product over
`C` only: off `C` every `j` is forced to `0` and
contributes the factor `1`) times the generalized
character moment over `C`. This is the form the
card-5 and card-4 pattern values take below. -/
theorem integral_colDens_prod_pow_eq_sum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (k : LayerColumn N → ℕ) (hk : ∀ P ∉ C, k P = 0) :
    ∫ α : LayerSite N → G, ∏ P ∈ C, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset (fun P => Finset.range (k P + 1)),
          (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
            * colReMomentPow ρ μG C j u u' := by
  classical
  have hLHS : ∫ α : LayerSite N → G,
        ∏ P ∈ C, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun α => ?_)
    show ∏ P ∈ C, (colDensC ρ u u' P α) ^ (k P)
      = ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
    exact Finset.prod_subset (Finset.subset_univ C)
      (fun P _ hP => by rw [hk P hP, pow_zero])
  rw [hLHS, integral_colDens_prod_pow_univ_eq_sum ρ μG
    hρcont u u' k]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : ∀ P ∉ C, j P = 0 := by
    intro P hP
    have hmem : j P ∈ Finset.range (k P + 1) :=
      Fintype.mem_piFinset.mp hj P
    rw [hk P hP] at hmem
    have hlt : j P < 1 := Finset.mem_range.mp hmem
    omega
  have hcoef : ∏ P ∈ Finset.univ,
        ((k P).choose (j P) : ℝ) * (-(d : ℝ)⁻¹) ^ (j P)
      = ∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P) :=
    (Finset.prod_subset (Finset.subset_univ C)
      (fun P _ hP => by rw [hk P hP, hj0 P hP]; norm_num)).symm
  have hmom : colReMomentPow ρ μG Finset.univ j u u'
      = colReMomentPow ρ μG C j u u' := by
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun α => ?_)
    show ∏ P ∈ Finset.univ, (colRe ρ u u' P α) ^ (j P)
      = ∏ P ∈ C, (colRe ρ u u' P α) ^ (j P)
    exact (Finset.prod_subset (Finset.subset_univ C)
      (fun P _ hP => by rw [hj0 P hP, pow_zero])).symm
  rw [hcoef, hmom]

#print axioms integral_colDens_prod_septuple
#print axioms fiber_card_seven7
#print axioms integral_colDens_prod_sextuple_doubled
#print axioms fiber_card_six7


/-! ## The card-5 and card-4 patterns and their values -/

/-- The `(3,1,1,1,1)` pattern at `(C, P)`: exponent
`3` at `P`, exponent `1` on the rest of `C`, `0` off
`C`. -/
noncomputable def tripledQuintuplePattern
    (C : Finset (LayerColumn N)) (P : LayerColumn N) :
    LayerColumn N → ℕ :=
  fun Q => if Q = P then 3 else if Q ∈ C then 1 else 0

/-- The `(2,2,1,1,1)` pattern at `(C, P, Q)`: exponent
`2` at `P` and at `Q`, exponent `1` on the rest of
`C`, `0` off `C`. -/
noncomputable def doubledDoubledQuintuplePattern
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N) :
    LayerColumn N → ℕ :=
  fun R => if R = P then 2 else if R = Q then 2
    else if R ∈ C then 1 else 0

/-- The `(4,1,1,1)` pattern at `(C, P)`: exponent `4`
at `P`, exponent `1` on the rest of `C`, `0` off `C`. -/
noncomputable def quadrupledQuadPattern7
    (C : Finset (LayerColumn N)) (P : LayerColumn N) :
    LayerColumn N → ℕ :=
  fun Q => if Q = P then 4 else if Q ∈ C then 1 else 0

/-- The `(3,2,1,1)` pattern at `(C, P, Q)`: exponent
`3` at `P`, exponent `2` at `Q`, exponent `1` on the
rest of `C`, `0` off `C`. -/
noncomputable def tripledDoubledQuadPattern7
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N) :
    LayerColumn N → ℕ :=
  fun R => if R = P then 3 else if R = Q then 2
    else if R ∈ C then 1 else 0

/-- The `(2,2,2,1)` pattern at `(C, P, Q, R)`:
exponent `2` at each of `P`, `Q`, `R`, exponent `1`
on the rest of `C`, `0` off `C`. -/
noncomputable def doubledDoubledDoubledQuadPattern7
    (C : Finset (LayerColumn N)) (P Q R : LayerColumn N) :
    LayerColumn N → ℕ :=
  fun S => if S = P then 2 else if S = Q then 2
    else if S = R then 2 else if S ∈ C then 1 else 0

/-- **The `(3,1,1,1,1)` pattern value**: the binomial
expansion of the tripled quintuple density monomial,
by the engine. -/
theorem integral_colDens_prod_quintuple_tripled
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α)
          ^ (tripledQuintuplePattern C P Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset
            (fun Q => Finset.range
              (tripledQuintuplePattern C P Q + 1)),
          (∏ Q ∈ C,
            ((tripledQuintuplePattern C P Q).choose (j Q) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j Q))
            * colReMomentPow ρ μG C j u u' :=
  integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
    (tripledQuintuplePattern C P)
    (fun Q hQ => by
      by_cases hQP : Q = P
      · subst hQP; exact absurd hP hQ
      · simp [tripledQuintuplePattern, hQP, hQ])

/-- **The `(2,2,1,1,1)` pattern value**: the binomial
expansion of the doubled-doubled quintuple density
monomial, by the engine. -/
theorem integral_colDens_prod_quintuple_doubled_doubled
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (P Q : LayerColumn N) (hP : P ∈ C) (hQ : Q ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ R ∈ C, (colDensC ρ u u' R α)
          ^ (doubledDoubledQuintuplePattern C P Q R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset
            (fun R => Finset.range
              (doubledDoubledQuintuplePattern C P Q R + 1)),
          (∏ R ∈ C,
            ((doubledDoubledQuintuplePattern C P Q R).choose
                (j R) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j R))
            * colReMomentPow ρ μG C j u u' :=
  integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
    (doubledDoubledQuintuplePattern C P Q)
    (fun R hR => by
      by_cases hRP : R = P
      · subst hRP; exact absurd hP hR
      · by_cases hRQ : R = Q
        · subst hRQ; exact absurd hQ hR
        · simp [doubledDoubledQuintuplePattern, hRP, hRQ,
            hR])

/-- **The `(4,1,1,1)` pattern value**: the binomial
expansion of the quadrupled quad density monomial,
by the engine. -/
theorem integral_colDens_prod_quadrupled7
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α)
          ^ (quadrupledQuadPattern7 C P Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset
            (fun Q => Finset.range
              (quadrupledQuadPattern7 C P Q + 1)),
          (∏ Q ∈ C,
            ((quadrupledQuadPattern7 C P Q).choose (j Q) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j Q))
            * colReMomentPow ρ μG C j u u' :=
  integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
    (quadrupledQuadPattern7 C P)
    (fun Q hQ => by
      by_cases hQP : Q = P
      · subst hQP; exact absurd hP hQ
      · simp [quadrupledQuadPattern7, hQP, hQ])

/-- **The `(3,2,1,1)` pattern value**: the binomial
expansion of the tripled-doubled quad density
monomial, by the engine. -/
theorem integral_colDens_prod_tripled_doubled7
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (P Q : LayerColumn N) (hP : P ∈ C) (hQ : Q ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ R ∈ C, (colDensC ρ u u' R α)
          ^ (tripledDoubledQuadPattern7 C P Q R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset
            (fun R => Finset.range
              (tripledDoubledQuadPattern7 C P Q R + 1)),
          (∏ R ∈ C,
            ((tripledDoubledQuadPattern7 C P Q R).choose
                (j R) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j R))
            * colReMomentPow ρ μG C j u u' :=
  integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
    (tripledDoubledQuadPattern7 C P Q)
    (fun R hR => by
      by_cases hRP : R = P
      · subst hRP; exact absurd hP hR
      · by_cases hRQ : R = Q
        · subst hRQ; exact absurd hQ hR
        · simp [tripledDoubledQuadPattern7, hRP, hRQ,
            hR])

/-- **The `(2,2,2,1)` pattern value**: the binomial
expansion of the triple-doubled quad density
monomial, by the engine. -/
theorem integral_colDens_prod_doubled_doubled_doubled7
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (P Q R : LayerColumn N) (hP : P ∈ C) (hQ : Q ∈ C)
    (hR : R ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ S ∈ C, (colDensC ρ u u' S α)
          ^ (doubledDoubledDoubledQuadPattern7 C P Q R S)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ j ∈ Fintype.piFinset
            (fun S => Finset.range
              (doubledDoubledDoubledQuadPattern7 C P Q R S
                + 1)),
          (∏ S ∈ C,
            ((doubledDoubledDoubledQuadPattern7 C P Q R S).choose
                (j S) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j S))
            * colReMomentPow ρ μG C j u u' :=
  integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
    (doubledDoubledDoubledQuadPattern7 C P Q R)
    (fun S hS => by
      by_cases hSP : S = P
      · subst hSP; exact absurd hP hS
      · by_cases hSQ : S = Q
        · subst hSQ; exact absurd hQ hS
        · by_cases hSR : S = R
          · subst hSR; exact absurd hR hS
          · simp [doubledDoubledDoubledQuadPattern7, hSP,
              hSQ, hSR, hS])

/-! ## The top generalized moments are the channel
moments -/

/-- The top generalized moment of the `(4,1,1,1)`
pattern is the B7-1b quadrupled quad moment. -/
theorem colReMomentPow_quadrupledQuadPattern7
    (C : Finset (LayerColumn N)) {P : LayerColumn N}
    (hP : P ∈ C) (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C (quadrupledQuadPattern7 C P) u u'
      = quadrupledQuadReMoment ρ μG C P u u' := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ Q ∈ C, (colRe ρ u u' Q α)
      ^ (quadrupledQuadPattern7 C P Q)
    = (colRe ρ u u' P α) ^ 4
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C
    (fun Q => (colRe ρ u u' Q α)
      ^ (quadrupledQuadPattern7 C P Q)) hP]
  refine congrArg₂ _ ?_ ?_
  · simp [quadrupledQuadPattern7]
  · refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    simp [quadrupledQuadPattern7, hQP, hQC]

/-- The top generalized moment of the `(3,2,1,1)`
pattern is the B7-1b tripled-doubled quad moment. -/
theorem colReMomentPow_tripledDoubledQuadPattern7
    (C : Finset (LayerColumn N)) {P Q : LayerColumn N}
    (hP : P ∈ C) (hQ : Q ∈ C) (hQP : Q ≠ P)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (tripledDoubledQuadPattern7 C P Q) u u'
      = tripledDoubledQuadReMoment ρ μG C P Q u u' := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQ⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ R ∈ C, (colRe ρ u u' R α)
      ^ (tripledDoubledQuadPattern7 C P Q R)
    = (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
  rw [← Finset.mul_prod_erase C
    (fun R => (colRe ρ u u' R α)
      ^ (tripledDoubledQuadPattern7 C P Q R)) hP,
    ← Finset.mul_prod_erase (C.erase P)
    (fun R => (colRe ρ u u' R α)
      ^ (tripledDoubledQuadPattern7 C P Q R)) hQmem,
    mul_assoc]
  have hP' : (colRe ρ u u' P α)
        ^ (tripledDoubledQuadPattern7 C P Q P)
      = (colRe ρ u u' P α) ^ 3 := by
    simp [tripledDoubledQuadPattern7]
  have hQ' : (colRe ρ u u' Q α)
        ^ (tripledDoubledQuadPattern7 C P Q Q)
      = (colRe ρ u u' Q α) ^ 2 := by
    simp [tripledDoubledQuadPattern7, hQP]
  have hR' : ∏ R ∈ (C.erase P).erase Q,
        (colRe ρ u u' R α)
          ^ (tripledDoubledQuadPattern7 C P Q R)
      = ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α :=
    Finset.prod_congr rfl fun R hR => by
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
  rw [hP', hQ', hR']

/-- The top generalized moment of the `(2,2,2,1)`
pattern is the B7-1b triple-doubled quad moment. -/
theorem colReMomentPow_doubledDoubledDoubledQuadPattern7
    (C : Finset (LayerColumn N)) {P Q R : LayerColumn N}
    (hP : P ∈ C) (hQ : Q ∈ C) (hR : R ∈ C)
    (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (doubledDoubledDoubledQuadPattern7 C P Q R) u u'
      = doubledDoubledDoubledQuadReMoment ρ μG C P Q R
        u u' := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQ⟩
  have hRmem : R ∈ (C.erase P).erase Q :=
    Finset.mem_erase.mpr ⟨hRQ,
      Finset.mem_erase.mpr ⟨hRP, hR⟩⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ S ∈ C, (colRe ρ u u' S α)
      ^ (doubledDoubledDoubledQuadPattern7 C P Q R S)
    = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * (colRe ρ u u' R α) ^ 2
      * ∏ S ∈ ((C.erase P).erase Q).erase R,
          colRe ρ u u' S α
  rw [← Finset.mul_prod_erase C
    (fun S => (colRe ρ u u' S α)
      ^ (doubledDoubledDoubledQuadPattern7 C P Q R S)) hP,
    ← Finset.mul_prod_erase (C.erase P)
    (fun S => (colRe ρ u u' S α)
      ^ (doubledDoubledDoubledQuadPattern7 C P Q R S))
      hQmem,
    ← Finset.mul_prod_erase ((C.erase P).erase Q)
    (fun S => (colRe ρ u u' S α)
      ^ (doubledDoubledDoubledQuadPattern7 C P Q R S))
      hRmem,
    mul_assoc, mul_assoc]
  have hP' : (colRe ρ u u' P α)
        ^ (doubledDoubledDoubledQuadPattern7 C P Q R P)
      = (colRe ρ u u' P α) ^ 2 := by
    simp [doubledDoubledDoubledQuadPattern7]
  have hQ' : (colRe ρ u u' Q α)
        ^ (doubledDoubledDoubledQuadPattern7 C P Q R Q)
      = (colRe ρ u u' Q α) ^ 2 := by
    simp [doubledDoubledDoubledQuadPattern7, hQP]
  have hR' : (colRe ρ u u' R α)
        ^ (doubledDoubledDoubledQuadPattern7 C P Q R R)
      = (colRe ρ u u' R α) ^ 2 := by
    simp [doubledDoubledDoubledQuadPattern7, hRP, hRQ]
  have hS' : ∏ S ∈ ((C.erase P).erase Q).erase R,
        (colRe ρ u u' S α)
          ^ (doubledDoubledDoubledQuadPattern7 C P Q R S)
      = ∏ S ∈ ((C.erase P).erase Q).erase R,
          colRe ρ u u' S α :=
    Finset.prod_congr rfl fun S hS => by
      have hSP : S ≠ P :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hS).2).2).1
      have hSQ : S ≠ Q :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp hS).2).1
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hS).2).2).2
      simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ,
        hSR, hSC]
  rw [hP', hQ', hR', hS']

/-! ## The card-5 top moments -/

/-- The raw `(3,1,1,1,1)` moment at a 5-support `C`
with distinguished tripled column `P`: the stratum
integral of `(colRe P)³ · ∏_{Q ∈ C.erase P} colRe Q`
— the character moment of the multiset `C + {P, P}`.
This is `tripledQuadReMoment`'s construction at
support size 5, named for the card-5 fiber as
`pentaReMoment` names the all-distinct moment at
support size 5. -/
noncomputable def tripledPentaReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 3
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The tripled 5-support moment is
`tripledQuadReMoment` itself: the moment construction
is support-size blind. -/
theorem tripledPentaReMoment_eq_tripledQuadReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) :
    tripledPentaReMoment ρ μG C P u u'
      = tripledQuadReMoment ρ μG C P u u' :=
  rfl

/-- The raw `(2,2,1,1,1)` moment at a 5-support `C`
with distinguished doubled columns `P`, `Q`: the
stratum integral of `(colRe P)² · (colRe Q)² ·
∏_{R ∈ (C.erase P).erase Q} colRe R` — the character
moment of the multiset `C + {P, Q}`. This is
`doubledDoubledQuadReMoment`'s construction at
support size 5. -/
noncomputable def doubledDoubledPentaReMoment
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The doubled-doubled 5-support moment is
`doubledDoubledQuadReMoment` itself: the moment
construction is support-size blind. -/
theorem doubledDoubledPentaReMoment_eq
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N)
    (u u' : LayerLink N → G) :
    doubledDoubledPentaReMoment ρ μG C P Q u u'
      = doubledDoubledQuadReMoment ρ μG C P Q u u' :=
  rfl

/-- The top generalized moment of the `(3,1,1,1,1)`
pattern is the tripled penta moment. -/
theorem colReMomentPow_tripledQuintuplePattern
    (C : Finset (LayerColumn N)) {P : LayerColumn N}
    (hP : P ∈ C) (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C (tripledQuintuplePattern C P)
        u u'
      = tripledPentaReMoment ρ μG C P u u' := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ Q ∈ C, (colRe ρ u u' Q α)
      ^ (tripledQuintuplePattern C P Q)
    = (colRe ρ u u' P α) ^ 3
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C
    (fun Q => (colRe ρ u u' Q α)
      ^ (tripledQuintuplePattern C P Q)) hP]
  refine congrArg₂ _ ?_ ?_
  · simp [tripledQuintuplePattern]
  · refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    simp [tripledQuintuplePattern, hQP, hQC]

/-- The top generalized moment of the `(2,2,1,1,1)`
pattern is the doubled-doubled penta moment. -/
theorem colReMomentPow_doubledDoubledQuintuplePattern
    (C : Finset (LayerColumn N)) {P Q : LayerColumn N}
    (hP : P ∈ C) (hQ : Q ∈ C) (hQP : Q ≠ P)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (doubledDoubledQuintuplePattern C P Q) u u'
      = doubledDoubledPentaReMoment ρ μG C P Q u u' := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQ⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ R ∈ C, (colRe ρ u u' R α)
      ^ (doubledDoubledQuintuplePattern C P Q R)
    = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
  rw [← Finset.mul_prod_erase C
    (fun R => (colRe ρ u u' R α)
      ^ (doubledDoubledQuintuplePattern C P Q R)) hP,
    ← Finset.mul_prod_erase (C.erase P)
    (fun R => (colRe ρ u u' R α)
      ^ (doubledDoubledQuintuplePattern C P Q R)) hQmem,
    mul_assoc]
  have hP' : (colRe ρ u u' P α)
        ^ (doubledDoubledQuintuplePattern C P Q P)
      = (colRe ρ u u' P α) ^ 2 := by
    simp [doubledDoubledQuintuplePattern]
  have hQ' : (colRe ρ u u' Q α)
        ^ (doubledDoubledQuintuplePattern C P Q Q)
      = (colRe ρ u u' Q α) ^ 2 := by
    simp [doubledDoubledQuintuplePattern, hQP]
  have hR' : ∏ R ∈ (C.erase P).erase Q,
        (colRe ρ u u' R α)
          ^ (doubledDoubledQuintuplePattern C P Q R)
      = ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α :=
    Finset.prod_congr rfl fun R hR => by
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      simp [doubledDoubledQuintuplePattern, hRP, hRQ, hRC]
  rw [hP', hQ', hR']

/-! ## The card-5 fiber -/

/-- The doubled-doubled quintuple pattern is symmetric
in its two doubled columns. -/
theorem doubledDoubledQuintuplePattern_symm
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N) :
    doubledDoubledQuintuplePattern C P Q
      = doubledDoubledQuintuplePattern C Q P := by
  funext R
  by_cases hRP : R = P
  · rw [hRP]
    by_cases hPQ : P = Q
    · rw [hPQ]
    · simp [doubledDoubledQuintuplePattern, hPQ]
  · by_cases hRQ : R = Q
    · rw [hRQ]
      have hQP : Q ≠ P := fun h => hRP (hRQ.trans h)
      simp [doubledDoubledQuintuplePattern, hQP]
    · simp [doubledDoubledQuintuplePattern, hRP, hRQ]

/-- **The card-5 fiber.** Over a 5-support `C`, the
fiber of the expansion is the five `(3,1,1,1,1)`
patterns (one per `P ∈ C`, multinomial coefficient
`840`, value the tripled quintuple pattern value)
plus the `(2,2,1,1,1)` patterns (one per unordered
pair of doubled columns, multinomial coefficient
`1260`; displayed as the ordered-pair sum at the
halved coefficient `630`, the pattern being symmetric
in its doubled columns). Classification by B7-0's
`patterns_of_card_five_seven`. -/
theorem fiber_card_five7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (840 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (tripledQuintuplePattern C P Q + 1)),
            (∏ Q ∈ C,
              ((tripledQuintuplePattern C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u')
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (doubledDoubledQuintuplePattern C P Q R
                  + 1)),
            (∏ R ∈ C,
              ((doubledDoubledQuintuplePattern C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u') := by
  classical
  -- The two pattern families, as finsets of exponent functions.
  set S3 : Finset (LayerColumn N → ℕ) :=
    C.image (tripledQuintuplePattern C) with hS3
  set S22 : Finset (LayerColumn N → ℕ) :=
    (C.sigma (fun P => C.erase P)).image
      (fun x => doubledDoubledQuintuplePattern C x.1 x.2)
    with hS22
  have hsupp3 : ∀ P ∈ C,
      multSupport (tripledQuintuplePattern C P) = C := by
    intro P hP
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hQP : Q = P
    · subst hQP
      simp [tripledQuintuplePattern, hP]
    · by_cases hQC : Q ∈ C <;>
        simp [tripledQuintuplePattern, hQP, hQC]
  have hsum3 : ∀ P ∈ C,
      ∑ Q ∈ Finset.univ, tripledQuintuplePattern C P Q
        = 7 := by
    intro P hP
    have h1 : ∑ Q ∈ Finset.univ, tripledQuintuplePattern C P Q
        = ∑ Q ∈ C, tripledQuintuplePattern C P Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
          simp [tripledQuintuplePattern, hQ, hQP])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP]
    have h2 : ∀ Q ∈ C.erase P,
        tripledQuintuplePattern C P Q = 1 :=
      fun Q hQ => by
        simp [tripledQuintuplePattern,
          (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP, hC]
    have hPP : tripledQuintuplePattern C P P = 3 := by
      simp [tripledQuintuplePattern]
    rw [hPP]
    decide
  have hmem3 : ∀ P ∈ C, tripledQuintuplePattern C P
      ∈ (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C) := by
    intro P hP
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsum3 P hP, fun Q _ => Finset.mem_univ Q⟩,
      hsupp3 P hP⟩
  have hval3 : ∀ P ∈ C,
      ((Nat.multinomial Finset.univ
          (tripledQuintuplePattern C P) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ Q ∈ Finset.univ,
                (colDensC ρ u u' Q α)
                  ^ (tripledQuintuplePattern C P Q)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (840 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (tripledQuintuplePattern C P Q + 1)),
            (∏ Q ∈ C,
              ((tripledQuintuplePattern C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u') := by
    intro P hP
    have hfact : ∏ Q ∈ Finset.univ,
        Nat.factorial (tripledQuintuplePattern C P Q) = 6 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial (tripledQuintuplePattern C P Q)
          = ∏ Q ∈ C,
            Nat.factorial (tripledQuintuplePattern C P Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
            simp [tripledQuintuplePattern, hQ, hQP])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP]
      have h2 : ∀ Q ∈ C.erase P,
          Nat.factorial (tripledQuintuplePattern C P Q) = 1 :=
        fun Q hQ => by
          simp [tripledQuintuplePattern,
            (Finset.mem_erase.mp hQ).1,
            (Finset.mem_erase.mp hQ).2]
      have hPP3 : tripledQuintuplePattern C P P = 3 := by
        simp [tripledQuintuplePattern]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one,
        hPP3]
      decide
    have hmult : (Nat.multinomial Finset.univ
          (tripledQuintuplePattern C P) : ℝ) = 840 := by
      have h := multinomial7_univ_eq
        (tripledQuintuplePattern C P) (hsum3 P hP) 6 hfact
        (by norm_num)
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ Q ∈ Finset.univ,
            (colDensC ρ u u' Q α)
              ^ (tripledQuintuplePattern C P Q)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ j ∈ Fintype.piFinset
            (fun Q => Finset.range
              (tripledQuintuplePattern C P Q + 1)),
          (∏ Q ∈ C,
            ((tripledQuintuplePattern C P Q).choose
                (j Q) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j Q))
            * colReMomentPow ρ μG C j u u' := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont
        u u' (tripledQuintuplePattern C P), hsupp3 P hP]
      exact integral_colDens_prod_quintuple_tripled ρ μG
        hρcont u u' C P hP
    rw [hmult, hint]
  have hsupp22 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      multSupport (doubledDoubledQuintuplePattern C P Q)
        = C := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    refine Finset.ext fun R => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hRP : R = P
    · subst hRP
      simp [doubledDoubledQuintuplePattern, hP]
    · by_cases hRQ : R = Q
      · subst hRQ
        simp [doubledDoubledQuintuplePattern, hQP, hQC]
      · by_cases hRC : R ∈ C <;>
          simp [doubledDoubledQuintuplePattern, hRP, hRQ,
            hRC]
  have hsum22 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∑ R ∈ Finset.univ,
        doubledDoubledQuintuplePattern C P Q R = 7 := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have h1 : ∑ R ∈ Finset.univ,
          doubledDoubledQuintuplePattern C P Q R
        = ∑ R ∈ C, doubledDoubledQuintuplePattern C P Q R :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun R _ hR => by
          have hRP : R ≠ P := fun h => hR (h.symm ▸ hP)
          have hRQ : R ≠ Q := fun h => hR (h.symm ▸ hQC)
          simp [doubledDoubledQuintuplePattern, hR, hRP,
            hRQ])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP,
      ← Finset.add_sum_erase (C.erase P) _
        (Finset.mem_erase.mpr ⟨hQP, hQC⟩)]
    have h2 : ∀ R ∈ (C.erase P).erase Q,
        doubledDoubledQuintuplePattern C P Q R = 1 :=
      fun R hR => by
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hR).2).1
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hR).2).2
        simp [doubledDoubledQuintuplePattern, hRP, hRQ,
          hRC]
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
    have hQQ : doubledDoubledQuintuplePattern C P Q Q
        = 2 := by
      simp [doubledDoubledQuintuplePattern, hQP]
    have hPP : doubledDoubledQuintuplePattern C P Q P
        = 2 := by
      simp [doubledDoubledQuintuplePattern]
    have hcardE : ((C.erase P).erase Q).card = 3 := by
      rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hQP, hQC⟩),
        Finset.card_erase_of_mem hP, hC]
    rw [hQQ, hPP, hcardE]
    decide
  have hmem22 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      doubledDoubledQuintuplePattern C P Q
        ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C) := by
    intro P hP Q hQ
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsum22 P hP Q hQ,
      fun R _ => Finset.mem_univ R⟩, hsupp22 P hP Q hQ⟩
  have hval22 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ((Nat.multinomial Finset.univ
          (doubledDoubledQuintuplePattern C P Q) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ R ∈ Finset.univ,
                (colDensC ρ u u' R α)
                  ^ (doubledDoubledQuintuplePattern C P Q R)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (1260 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (doubledDoubledQuintuplePattern C P Q R
                  + 1)),
            (∏ R ∈ C,
              ((doubledDoubledQuintuplePattern C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u') := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hfact : ∏ R ∈ Finset.univ,
        Nat.factorial
          (doubledDoubledQuintuplePattern C P Q R) = 4 := by
      have h1 : ∏ R ∈ Finset.univ,
            Nat.factorial
              (doubledDoubledQuintuplePattern C P Q R)
          = ∏ R ∈ C, Nat.factorial
              (doubledDoubledQuintuplePattern C P Q R) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun R _ hR => by
            have hRP : R ≠ P := fun h => hR (h.symm ▸ hP)
            have hRQ : R ≠ Q := fun h => hR (h.symm ▸ hQC)
            simp [doubledDoubledQuintuplePattern, hR, hRP,
              hRQ])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _
          (Finset.mem_erase.mpr ⟨hQP, hQC⟩)]
      have h2 : ∀ R ∈ (C.erase P).erase Q,
          Nat.factorial
            (doubledDoubledQuintuplePattern C P Q R) = 1 :=
        fun R hR => by
          have hRP : R ≠ P :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR).2).1
          have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
          have hRC : R ∈ C :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR).2).2
          simp [doubledDoubledQuintuplePattern, hRP, hRQ,
            hRC]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      have hQQ : Nat.factorial
          (doubledDoubledQuintuplePattern C P Q Q) = 2 := by
        simp [doubledDoubledQuintuplePattern, hQP]
      have hPP : Nat.factorial
          (doubledDoubledQuintuplePattern C P Q P) = 2 := by
        simp [doubledDoubledQuintuplePattern]
      rw [hQQ, hPP]
      decide
    have hmult : (Nat.multinomial Finset.univ
          (doubledDoubledQuintuplePattern C P Q) : ℝ)
        = 1260 := by
      have h := multinomial7_univ_eq
        (doubledDoubledQuintuplePattern C P Q)
        (hsum22 P hP Q hQ) 4 hfact (by norm_num)
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ R ∈ Finset.univ,
            (colDensC ρ u u' R α)
              ^ (doubledDoubledQuintuplePattern C P Q R)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ j ∈ Fintype.piFinset
            (fun R => Finset.range
              (doubledDoubledQuintuplePattern C P Q R
                + 1)),
          (∏ R ∈ C,
            ((doubledDoubledQuintuplePattern C P Q R).choose
                (j R) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j R))
            * colReMomentPow ρ μG C j u u' := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont
        u u' (doubledDoubledQuintuplePattern C P Q),
        hsupp22 P hP Q hQ]
      exact integral_colDens_prod_quintuple_doubled_doubled
        ρ μG hρcont u u' C P Q hP hQC
    rw [hmult, hint]
  -- The fiber is exactly the union of the two pattern families.
  have hfib : (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C) = S3 ∪ S22 := by
    refine Finset.ext fun k => ?_
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hk
      have hk7 : ∑ P ∈ Finset.univ, k P = 7 :=
        (Finset.mem_piAntidiag.mp hk.1).1
      have hsupp : multSupport k = C := hk.2
      have hcard : (multSupport k).card = 5 := by
        rw [hsupp]; exact hC
      rcases patterns_of_card_five_seven k hk7 hcard with
        ⟨P₀, hP₀S, hk3, hrest⟩ | ⟨P₀, hP₀S, P₁, hP₁S,
          hne, hk2₀, hk2₁, hrest⟩
      · left
        have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
        refine Finset.mem_image.mpr ⟨P₀, hP₀C, ?_⟩
        funext Q
        by_cases hQP : Q = P₀
        · rw [hQP, hk3]
          simp [tripledQuintuplePattern]
        · by_cases hQC : Q ∈ C
          · have hkQ : k Q = 1 :=
              hrest Q (hsupp ▸ hQC) hQP
            rw [hkQ]
            simp [tripledQuintuplePattern, hQP, hQC]
          · have hkQ : k Q = 0 := by
              by_contra hne0
              have hQs : Q ∈ multSupport k :=
                Finset.mem_filter.mpr
                  ⟨Finset.mem_univ Q, hne0⟩
              rw [hsupp] at hQs
              exact hQC hQs
            rw [hkQ]
            simp [tripledQuintuplePattern, hQP, hQC]
      · right
        have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
        have hP₁C : P₁ ∈ C := hsupp ▸ hP₁S
        have hP₁e : P₁ ∈ C.erase P₀ :=
          Finset.mem_erase.mpr ⟨Ne.symm hne, hP₁C⟩
        refine Finset.mem_image.mpr
          ⟨⟨P₀, P₁⟩, Finset.mem_sigma.mpr ⟨hP₀C, hP₁e⟩, ?_⟩
        funext Q
        by_cases hQP : Q = P₀
        · rw [hQP, hk2₀]
          simp [doubledDoubledQuintuplePattern]
        · by_cases hQ1 : Q = P₁
          · rw [hQ1, hk2₁]
            have hPQ : P₁ ≠ P₀ := Ne.symm hne
            simp [doubledDoubledQuintuplePattern, hPQ]
          · by_cases hQC : Q ∈ C
            · have hkQ : k Q = 1 :=
                hrest Q (hsupp ▸ hQC) hQP hQ1
              rw [hkQ]
              simp [doubledDoubledQuintuplePattern, hQP,
                hQ1, hQC]
            · have hkQ : k Q = 0 := by
                by_contra hne0
                have hQs : Q ∈ multSupport k :=
                  Finset.mem_filter.mpr
                    ⟨Finset.mem_univ Q, hne0⟩
                rw [hsupp] at hQs
                exact hQC hQs
              rw [hkQ]
              simp [doubledDoubledQuintuplePattern, hQP,
                hQ1, hQC]
    · intro hk
      rcases hk with hk | hk
      · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_filter.mp (hmem3 P hP)
      · obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hk
        have hx1 : x.1 ∈ C := (Finset.mem_sigma.mp hx).1
        have hx2 : x.2 ∈ C.erase x.1 :=
          (Finset.mem_sigma.mp hx).2
        rw [← hxeq]
        exact Finset.mem_filter.mp (hmem22 x.1 hx1 x.2 hx2)
  rw [hfib, Finset.sum_union]
  · -- The S22 sum, via the two-to-one ordered-pair count.
    have hS3sum : ∑ k ∈ S3,
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ,
                (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (840 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (tripledQuintuplePattern C P Q + 1)),
            (∏ Q ∈ C,
              ((tripledQuintuplePattern C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u') := by
      rw [hS3, Finset.sum_image]
      · exact Finset.sum_congr rfl fun P hP => hval3 P hP
      · intro P hP P' hP' h
        by_contra hne
        have h2 := congrFun h P
        have hPP' : tripledQuintuplePattern C P' P = 1 := by
          have hPC : P ∈ C := hP
          simp [tripledQuintuplePattern, hne, hPC]
        rw [hPP'] at h2
        simp [tripledQuintuplePattern] at h2
    have hS22sum : ∑ k ∈ S22,
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ,
                (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (doubledDoubledQuintuplePattern C P Q R
                  + 1)),
            (∏ R ∈ C,
              ((doubledDoubledQuintuplePattern C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u') := by
      -- Double counting over ordered pairs: each
      -- `(2,2,1,1,1)` pattern is hit exactly twice.
      have hdouble : ∑ x ∈ C.sigma (fun P => C.erase P),
          ((Nat.multinomial Finset.univ
              (doubledDoubledQuintuplePattern C x.1 x.2)
              : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ,
                  (colDensC ρ u u' P α)
                    ^ (doubledDoubledQuintuplePattern C
                      x.1 x.2 P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ k ∈ S22, 2
            * (((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG)) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun x : Σ _ : LayerColumn N,
              LayerColumn N =>
            doubledDoubledQuintuplePattern C x.1 x.2)
          (f := fun x =>
            ((Nat.multinomial Finset.univ
                (doubledDoubledQuintuplePattern C x.1 x.2)
                : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α)
                      ^ (doubledDoubledQuintuplePattern C
                        x.1 x.2 P)
                  ∂(Measure.pi fun _ : LayerSite N => μG))]
        · refine Finset.sum_congr rfl fun k hk => ?_
          obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hk
          have hx₀1 : x₀.1 ∈ C :=
            (Finset.mem_sigma.mp hx₀).1
          have hx₀2 : x₀.2 ∈ C.erase x₀.1 :=
            (Finset.mem_sigma.mp hx₀).2
          have hx₀2C : x₀.2 ∈ C :=
            (Finset.mem_erase.mp hx₀2).2
          have hne : x₀.2 ≠ x₀.1 :=
            (Finset.mem_erase.mp hx₀2).1
          have hfilt : (C.sigma (fun P => C.erase P)).filter
                (fun x =>
                  doubledDoubledQuintuplePattern C x.1 x.2
                    = doubledDoubledQuintuplePattern C
                      x₀.1 x₀.2)
              = {x₀, ⟨x₀.2, x₀.1⟩} := by
            refine Finset.ext fun x => ?_
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · intro hx
              have hx1 : x.1 ∈ C :=
                (Finset.mem_sigma.mp hx.1).1
              have hx2 : x.2 ∈ C.erase x.1 :=
                (Finset.mem_sigma.mp hx.1).2
              have hx2C : x.2 ∈ C :=
                (Finset.mem_erase.mp hx2).2
              have hxne : x.2 ≠ x.1 :=
                (Finset.mem_erase.mp hx2).1
              have heq := hx.2
              have hA : x.1 = x₀.1 ∨ x.1 = x₀.2 := by
                have h2 : doubledDoubledQuintuplePattern C
                      x₀.1 x₀.2 x.1 = 2 := by
                  rw [← heq]
                  simp [doubledDoubledQuintuplePattern]
                by_contra hcon
                push_neg at hcon
                have hle : doubledDoubledQuintuplePattern C
                      x₀.1 x₀.2 x.1 ≤ 1 := by
                  simp [doubledDoubledQuintuplePattern,
                    hcon.1, hcon.2, hx1]
                omega
              have hB : x.2 = x₀.1 ∨ x.2 = x₀.2 := by
                have h2 : doubledDoubledQuintuplePattern C
                      x₀.1 x₀.2 x.2 = 2 := by
                  rw [← heq]
                  simp [doubledDoubledQuintuplePattern, hxne]
                by_contra hcon
                push_neg at hcon
                have hle : doubledDoubledQuintuplePattern C
                      x₀.1 x₀.2 x.2 ≤ 1 := by
                  simp [doubledDoubledQuintuplePattern,
                    hcon.1, hcon.2, hx2C]
                omega
              rcases hA with hA | hA <;>
                rcases hB with hB | hB
              · exact absurd (hB.trans hA.symm) hxne
              · exact Or.inl (Sigma.ext hA (heq_of_eq hB))
              · exact Or.inr (Sigma.ext hA (heq_of_eq hB))
              · exact absurd (hB.trans hA.symm) hxne
            · intro hx
              rcases hx with rfl | rfl
              · exact ⟨hx₀, rfl⟩
              · refine ⟨Finset.mem_sigma.mpr ⟨hx₀2C,
                  Finset.mem_erase.mpr ⟨Ne.symm hne,
                    hx₀1⟩⟩, ?_⟩
                rw [doubledDoubledQuintuplePattern_symm]
          have hpair : (⟨x₀.2, x₀.1⟩ :
              Σ _ : LayerColumn N, LayerColumn N) ≠ x₀ := by
            intro hcon
            have h21 : x₀.2 = x₀.1 :=
              congrArg Sigma.fst hcon
            exact hne h21
          rw [hfilt, Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            exact fun h => hpair h.symm),
            Finset.sum_singleton,
            doubledDoubledQuintuplePattern_symm]
          ring
        · intro x hx
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hordered : ∑ x ∈ C.sigma (fun P => C.erase P),
          ((Nat.multinomial Finset.univ
              (doubledDoubledQuintuplePattern C x.1 x.2)
              : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ,
                  (colDensC ρ u u' P α)
                    ^ (doubledDoubledQuintuplePattern C
                      x.1 x.2 P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ P ∈ C, ∑ Q ∈ C.erase P, (1260 : ℝ)
            * (∑ j ∈ Fintype.piFinset
                (fun R => Finset.range
                  (doubledDoubledQuintuplePattern C P Q R
                    + 1)),
              (∏ R ∈ C,
                ((doubledDoubledQuintuplePattern C P Q R).choose
                    (j R) : ℝ)
                  * (-(d : ℝ)⁻¹) ^ (j R))
                * colReMomentPow ρ μG C j u u') := by
        rw [Finset.sum_sigma]
        exact Finset.sum_congr rfl fun P hP =>
          Finset.sum_congr rfl fun Q hQ => hval22 P hP Q hQ
      have h2L : 2 * (∑ k ∈ S22,
            ((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG))
          = 2 * (∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ)
              * (∑ j ∈ Fintype.piFinset
                  (fun R => Finset.range
                    (doubledDoubledQuintuplePattern C P Q R
                      + 1)),
                (∏ R ∈ C,
                  ((doubledDoubledQuintuplePattern C P Q
                      R).choose (j R) : ℝ)
                    * (-(d : ℝ)⁻¹) ^ (j R))
                  * colReMomentPow ρ μG C j u u')) := by
        rw [Finset.mul_sum, ← hdouble, hordered,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Q _ => ?_
        ring
      exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
        h2L
    rw [hS3sum, hS22sum]
  · -- Disjointness of the two pattern families.
    refine Finset.disjoint_left.mpr fun k hk3 hk22 => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hk3
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hk22
    have h3 : tripledQuintuplePattern C P P = 3 := by
      simp [tripledQuintuplePattern]
    have hle : tripledQuintuplePattern C P P ≤ 2 := by
      have h := congrFun hxeq P
      rw [h3] at h
      have hle2 : doubledDoubledQuintuplePattern C x.1 x.2 P
          ≤ 2 := by
        by_cases h1 : P = x.1
        · simp [doubledDoubledQuintuplePattern, h1]
        · by_cases h2 : P = x.2
          · simp [doubledDoubledQuintuplePattern, h1, h2]
          · by_cases hPC : P ∈ C
            · simp [doubledDoubledQuintuplePattern, h1, h2,
                hPC]
            · simp [doubledDoubledQuintuplePattern, h1, h2,
                hPC]
      omega
    omega

/-! ## The card-4 fiber -/

/-- The triple-doubled quad pattern is invariant
under swapping its last two doubled columns. -/
theorem doubledDoubledDoubledQuadPattern7_swap_snd
    (C : Finset (LayerColumn N)) (P Q R : LayerColumn N) :
    doubledDoubledDoubledQuadPattern7 C P Q R
      = doubledDoubledDoubledQuadPattern7 C P R Q := by
  funext S
  by_cases hSP : S = P
  · rw [hSP]
    simp [doubledDoubledDoubledQuadPattern7]
  · by_cases hSQ : S = Q
    · rw [hSQ]
      by_cases hQR : Q = R
      · rw [hQR]
      · simp [doubledDoubledDoubledQuadPattern7, hSP, hQR]
    · by_cases hSR : S = R
      · rw [hSR]
        simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ]
      · simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ,
          hSR]

/-- The triple-doubled quad pattern is invariant
under swapping its first two doubled columns. -/
theorem doubledDoubledDoubledQuadPattern7_swap_fst
    (C : Finset (LayerColumn N)) (P Q R : LayerColumn N) :
    doubledDoubledDoubledQuadPattern7 C P Q R
      = doubledDoubledDoubledQuadPattern7 C Q P R := by
  funext S
  by_cases hSP : S = P
  · rw [hSP]
    by_cases hPQ : P = Q
    · rw [hPQ]
    · simp [doubledDoubledDoubledQuadPattern7, hPQ]
  · by_cases hSQ : S = Q
    · rw [hSQ]
      simp [doubledDoubledDoubledQuadPattern7, hSP]
    · simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ]

/-- **The card-4 fiber.** Over a 4-support `C`, the
fiber of the expansion is the four `(4,1,1,1)`
patterns (one per `P ∈ C`, multinomial coefficient
`210`, value the quadrupled quad pattern value), the
twelve `(3,2,1,1)` patterns (one per ordered heavy
pair, multinomial coefficient `420`, value the
tripled-doubled quad pattern value), and the
`(2,2,2,1)` patterns (one per unordered triple of
doubled columns, multinomial coefficient `630`;
displayed as the ordered-triple sum at the divided
coefficient `105`, the pattern being invariant under
permutations of its doubled columns). Classification
by B7-0's `patterns_of_card_four_seven`. -/
theorem fiber_card_four7 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (210 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (quadrupledQuadPattern7 C P Q + 1)),
            (∏ Q ∈ C,
              ((quadrupledQuadPattern7 C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u')
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (tripledDoubledQuadPattern7 C P Q R + 1)),
            (∏ R ∈ C,
              ((tripledDoubledQuadPattern7 C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u')
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun S => Finset.range
                (doubledDoubledDoubledQuadPattern7 C P Q R S
                  + 1)),
            (∏ S ∈ C,
              ((doubledDoubledDoubledQuadPattern7 C P Q R
                  S).choose (j S) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j S))
              * colReMomentPow ρ μG C j u u') := by
  classical
  set S4 : Finset (LayerColumn N → ℕ) :=
    C.image (quadrupledQuadPattern7 C) with hS4
  set S32 : Finset (LayerColumn N → ℕ) :=
    (C.sigma (fun P => C.erase P)).image
      (fun x => tripledDoubledQuadPattern7 C x.1 x.2)
    with hS32
  set S222 : Finset (LayerColumn N → ℕ) :=
    (C.sigma (fun P => (C.erase P).sigma
      (fun Q => (C.erase P).erase Q))).image
      (fun x => doubledDoubledDoubledQuadPattern7 C x.1
        x.2.1 x.2.2) with hS222
  -- Pattern bookkeeping for the three families.
  have hsupp4 : ∀ P ∈ C,
      multSupport (quadrupledQuadPattern7 C P) = C := by
    intro P hP
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hQP : Q = P
    · subst hQP
      simp [quadrupledQuadPattern7, hP]
    · by_cases hQC : Q ∈ C <;>
        simp [quadrupledQuadPattern7, hQP, hQC]
  have hsum4 : ∀ P ∈ C,
      ∑ Q ∈ Finset.univ, quadrupledQuadPattern7 C P Q
        = 7 := by
    intro P hP
    have h1 : ∑ Q ∈ Finset.univ, quadrupledQuadPattern7 C P Q
        = ∑ Q ∈ C, quadrupledQuadPattern7 C P Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
          simp [quadrupledQuadPattern7, hQ, hQP])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP]
    have h2 : ∀ Q ∈ C.erase P,
        quadrupledQuadPattern7 C P Q = 1 :=
      fun Q hQ => by
        simp [quadrupledQuadPattern7,
          (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP, hC]
    have hPP : quadrupledQuadPattern7 C P P = 4 := by
      simp [quadrupledQuadPattern7]
    rw [hPP]
    decide
  have hmem4 : ∀ P ∈ C, quadrupledQuadPattern7 C P
      ∈ (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C) := by
    intro P hP
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsum4 P hP, fun Q _ => Finset.mem_univ Q⟩,
      hsupp4 P hP⟩
  have hval4 : ∀ P ∈ C,
      ((Nat.multinomial Finset.univ
          (quadrupledQuadPattern7 C P) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ Q ∈ Finset.univ,
                (colDensC ρ u u' Q α)
                  ^ (quadrupledQuadPattern7 C P Q)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (210 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (quadrupledQuadPattern7 C P Q + 1)),
            (∏ Q ∈ C,
              ((quadrupledQuadPattern7 C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u') := by
    intro P hP
    have hfact : ∏ Q ∈ Finset.univ,
        Nat.factorial (quadrupledQuadPattern7 C P Q)
          = 24 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial (quadrupledQuadPattern7 C P Q)
          = ∏ Q ∈ C,
            Nat.factorial (quadrupledQuadPattern7 C P Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
            simp [quadrupledQuadPattern7, hQ, hQP])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP]
      have h2 : ∀ Q ∈ C.erase P,
          Nat.factorial (quadrupledQuadPattern7 C P Q)
            = 1 :=
        fun Q hQ => by
          simp [quadrupledQuadPattern7,
            (Finset.mem_erase.mp hQ).1,
            (Finset.mem_erase.mp hQ).2]
      have hPP : quadrupledQuadPattern7 C P P = 4 := by
        simp [quadrupledQuadPattern7]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one,
        hPP]
      decide
    have hmult : (Nat.multinomial Finset.univ
          (quadrupledQuadPattern7 C P) : ℝ) = 210 := by
      have h := multinomial7_univ_eq
        (quadrupledQuadPattern7 C P) (hsum4 P hP) 24 hfact
        (by norm_num)
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ Q ∈ Finset.univ,
            (colDensC ρ u u' Q α)
              ^ (quadrupledQuadPattern7 C P Q)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ j ∈ Fintype.piFinset
            (fun Q => Finset.range
              (quadrupledQuadPattern7 C P Q + 1)),
          (∏ Q ∈ C,
            ((quadrupledQuadPattern7 C P Q).choose
                (j Q) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j Q))
            * colReMomentPow ρ μG C j u u' := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont
        u u' (quadrupledQuadPattern7 C P), hsupp4 P hP]
      exact integral_colDens_prod_quadrupled7 ρ μG hρcont
        u u' C P hP
    rw [hmult, hint]
  have hsupp32 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      multSupport (tripledDoubledQuadPattern7 C P Q)
        = C := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    refine Finset.ext fun R => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hRP : R = P
    · subst hRP
      simp [tripledDoubledQuadPattern7, hP]
    · by_cases hRQ : R = Q
      · subst hRQ
        simp [tripledDoubledQuadPattern7, hQP, hQC]
      · by_cases hRC : R ∈ C <;>
          simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
  have hsum32 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∑ R ∈ Finset.univ,
        tripledDoubledQuadPattern7 C P Q R = 7 := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have h1 : ∑ R ∈ Finset.univ,
          tripledDoubledQuadPattern7 C P Q R
        = ∑ R ∈ C, tripledDoubledQuadPattern7 C P Q R :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun R _ hR => by
          have hRP : R ≠ P := fun h => hR (h.symm ▸ hP)
          have hRQ : R ≠ Q := fun h => hR (h.symm ▸ hQC)
          simp [tripledDoubledQuadPattern7, hR, hRP,
            hRQ])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP,
      ← Finset.add_sum_erase (C.erase P) _
        (Finset.mem_erase.mpr ⟨hQP, hQC⟩)]
    have h2 : ∀ R ∈ (C.erase P).erase Q,
        tripledDoubledQuadPattern7 C P Q R = 1 :=
      fun R hR => by
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hR).2).1
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hR).2).2
        simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
    have hQQ : tripledDoubledQuadPattern7 C P Q Q = 2 := by
      simp [tripledDoubledQuadPattern7, hQP]
    have hPP : tripledDoubledQuadPattern7 C P Q P = 3 := by
      simp [tripledDoubledQuadPattern7]
    have hcardE : ((C.erase P).erase Q).card = 2 := by
      rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hQP, hQC⟩),
        Finset.card_erase_of_mem hP, hC]
    rw [hQQ, hPP, hcardE]
    decide
  have hmem32 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      tripledDoubledQuadPattern7 C P Q
        ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C) := by
    intro P hP Q hQ
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsum32 P hP Q hQ,
      fun R _ => Finset.mem_univ R⟩, hsupp32 P hP Q hQ⟩
  have hval32 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ((Nat.multinomial Finset.univ
          (tripledDoubledQuadPattern7 C P Q) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ R ∈ Finset.univ,
                (colDensC ρ u u' R α)
                  ^ (tripledDoubledQuadPattern7 C P Q R)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (420 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (tripledDoubledQuadPattern7 C P Q R + 1)),
            (∏ R ∈ C,
              ((tripledDoubledQuadPattern7 C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u') := by
    intro P hP Q hQ
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hfact : ∏ R ∈ Finset.univ,
        Nat.factorial
          (tripledDoubledQuadPattern7 C P Q R) = 12 := by
      have h1 : ∏ R ∈ Finset.univ,
            Nat.factorial
              (tripledDoubledQuadPattern7 C P Q R)
          = ∏ R ∈ C, Nat.factorial
              (tripledDoubledQuadPattern7 C P Q R) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun R _ hR => by
            have hRP : R ≠ P := fun h => hR (h.symm ▸ hP)
            have hRQ : R ≠ Q := fun h => hR (h.symm ▸ hQC)
            simp [tripledDoubledQuadPattern7, hR, hRP,
              hRQ])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _
          (Finset.mem_erase.mpr ⟨hQP, hQC⟩)]
      have h2 : ∀ R ∈ (C.erase P).erase Q,
          Nat.factorial
            (tripledDoubledQuadPattern7 C P Q R) = 1 :=
        fun R hR => by
          have hRP : R ≠ P :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR).2).1
          have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
          have hRC : R ∈ C :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR).2).2
          simp [tripledDoubledQuadPattern7, hRP, hRQ,
            hRC]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      have hQQ : Nat.factorial
          (tripledDoubledQuadPattern7 C P Q Q) = 2 := by
        simp [tripledDoubledQuadPattern7, hQP]
      have hPP : Nat.factorial
          (tripledDoubledQuadPattern7 C P Q P) = 6 := by
        have h3 : tripledDoubledQuadPattern7 C P Q P
            = 3 := by
          simp [tripledDoubledQuadPattern7]
        calc Nat.factorial
              (tripledDoubledQuadPattern7 C P Q P)
            = Nat.factorial 3 := congrArg Nat.factorial h3
          _ = 6 := by decide
      rw [hQQ, hPP]
      decide
    have hmult : (Nat.multinomial Finset.univ
          (tripledDoubledQuadPattern7 C P Q) : ℝ)
        = 420 := by
      have h := multinomial7_univ_eq
        (tripledDoubledQuadPattern7 C P Q)
        (hsum32 P hP Q hQ) 12 hfact (by norm_num)
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ R ∈ Finset.univ,
            (colDensC ρ u u' R α)
              ^ (tripledDoubledQuadPattern7 C P Q R)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ j ∈ Fintype.piFinset
            (fun R => Finset.range
              (tripledDoubledQuadPattern7 C P Q R + 1)),
          (∏ R ∈ C,
            ((tripledDoubledQuadPattern7 C P Q R).choose
                (j R) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j R))
            * colReMomentPow ρ μG C j u u' := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont
        u u' (tripledDoubledQuadPattern7 C P Q),
        hsupp32 P hP Q hQ]
      exact integral_colDens_prod_tripled_doubled7 ρ μG
        hρcont u u' C P Q hP hQC
    rw [hmult, hint]
  have hsupp222 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∀ R ∈ (C.erase P).erase Q,
      multSupport
          (doubledDoubledDoubledQuadPattern7 C P Q R)
        = C := by
    intro P hP Q hQ R hR
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hRC : R ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    refine Finset.ext fun S => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hSP : S = P
    · subst hSP
      simp [doubledDoubledDoubledQuadPattern7, hP]
    · by_cases hSQ : S = Q
      · subst hSQ
        simp [doubledDoubledDoubledQuadPattern7, hQP, hQC]
      · by_cases hSR : S = R
        · subst hSR
          simp [doubledDoubledDoubledQuadPattern7, hRP,
            hRQ, hRC]
        · by_cases hSC : S ∈ C <;>
            simp [doubledDoubledDoubledQuadPattern7, hSP,
              hSQ, hSR, hSC]
  have hsum222 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∀ R ∈ (C.erase P).erase Q,
      ∑ S ∈ Finset.univ,
        doubledDoubledDoubledQuadPattern7 C P Q R S
        = 7 := by
    intro P hP Q hQ R hR
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hRC : R ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    have hQmem : Q ∈ C.erase P :=
      Finset.mem_erase.mpr ⟨hQP, hQC⟩
    have hRmem : R ∈ (C.erase P).erase Q := hR
    have h1 : ∑ S ∈ Finset.univ,
          doubledDoubledDoubledQuadPattern7 C P Q R S
        = ∑ S ∈ C,
            doubledDoubledDoubledQuadPattern7 C P Q R S :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun S _ hS => by
          have hSP : S ≠ P := fun h => hS (h.symm ▸ hP)
          have hSQ : S ≠ Q := fun h => hS (h.symm ▸ hQC)
          have hSR : S ≠ R := fun h => hS (h.symm ▸ hRC)
          simp [doubledDoubledDoubledQuadPattern7, hS,
            hSP, hSQ, hSR])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP,
      ← Finset.add_sum_erase (C.erase P) _ hQmem,
      ← Finset.add_sum_erase ((C.erase P).erase Q) _ hRmem]
    have h2 : ∀ S ∈ ((C.erase P).erase Q).erase R,
        doubledDoubledDoubledQuadPattern7 C P Q R S
          = 1 :=
      fun S hS => by
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hS).2).2).1
        have hSQ : S ≠ Q :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hS).2).1
        have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hS).2).2).2
        simp [doubledDoubledDoubledQuadPattern7, hSP,
          hSQ, hSR, hSC]
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
    have hRR : doubledDoubledDoubledQuadPattern7 C P Q R R
        = 2 := by
      simp [doubledDoubledDoubledQuadPattern7, hRP, hRQ]
    have hQQ : doubledDoubledDoubledQuadPattern7 C P Q R Q
        = 2 := by
      simp [doubledDoubledDoubledQuadPattern7, hQP]
    have hPP : doubledDoubledDoubledQuadPattern7 C P Q R P
        = 2 := by
      simp [doubledDoubledDoubledQuadPattern7]
    have hcardE : (((C.erase P).erase Q).erase R).card
        = 1 := by
      rw [Finset.card_erase_of_mem hRmem,
        Finset.card_erase_of_mem hQmem,
        Finset.card_erase_of_mem hP, hC]
    rw [hRR, hQQ, hPP, hcardE]
    decide
  have hmem222 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∀ R ∈ (C.erase P).erase Q,
      doubledDoubledDoubledQuadPattern7 C P Q R
        ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C) := by
    intro P hP Q hQ R hR
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsum222 P hP Q hQ R hR,
      fun S _ => Finset.mem_univ S⟩,
      hsupp222 P hP Q hQ R hR⟩
  have hval222 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∀ R ∈ (C.erase P).erase Q,
      ((Nat.multinomial Finset.univ
          (doubledDoubledDoubledQuadPattern7 C P Q R)
          : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ S ∈ Finset.univ,
                (colDensC ρ u u' S α)
                  ^ (doubledDoubledDoubledQuadPattern7
                    C P Q R S)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (630 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun S => Finset.range
                (doubledDoubledDoubledQuadPattern7 C P Q R S
                  + 1)),
            (∏ S ∈ C,
              ((doubledDoubledDoubledQuadPattern7 C P Q R
                  S).choose (j S) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j S))
              * colReMomentPow ρ μG C j u u') := by
    intro P hP Q hQ R hR
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hRC : R ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    have hQmem : Q ∈ C.erase P :=
      Finset.mem_erase.mpr ⟨hQP, hQC⟩
    have hfact : ∏ S ∈ Finset.univ,
        Nat.factorial
          (doubledDoubledDoubledQuadPattern7 C P Q R S)
          = 8 := by
      have h1 : ∏ S ∈ Finset.univ,
            Nat.factorial
              (doubledDoubledDoubledQuadPattern7 C P Q R S)
          = ∏ S ∈ C, Nat.factorial
              (doubledDoubledDoubledQuadPattern7
                C P Q R S) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun S _ hS => by
            have hSP : S ≠ P := fun h => hS (h.symm ▸ hP)
            have hSQ : S ≠ Q := fun h => hS (h.symm ▸ hQC)
            have hSR : S ≠ R := fun h => hS (h.symm ▸ hRC)
            simp [doubledDoubledDoubledQuadPattern7, hS,
              hSP, hSQ, hSR])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _ hQmem,
        ← Finset.mul_prod_erase ((C.erase P).erase Q) _
          hR]
      have h2 : ∀ S ∈ ((C.erase P).erase Q).erase R,
          Nat.factorial
            (doubledDoubledDoubledQuadPattern7 C P Q R S)
            = 1 :=
        fun S hS => by
          have hSP : S ≠ P :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp
                (Finset.mem_erase.mp hS).2).2).1
          have hSQ : S ≠ Q :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hS).2).1
          have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
          have hSC : S ∈ C :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp
                (Finset.mem_erase.mp hS).2).2).2
          simp [doubledDoubledDoubledQuadPattern7, hSP,
            hSQ, hSR, hSC]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      have hRR : Nat.factorial
          (doubledDoubledDoubledQuadPattern7 C P Q R R)
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, hRP,
          hRQ]
      have hQQ : Nat.factorial
          (doubledDoubledDoubledQuadPattern7 C P Q R Q)
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, hQP]
      have hPP : Nat.factorial
          (doubledDoubledDoubledQuadPattern7 C P Q R P)
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7]
      rw [hRR, hQQ, hPP]
      decide
    have hmult : (Nat.multinomial Finset.univ
          (doubledDoubledDoubledQuadPattern7 C P Q R)
          : ℝ) = 630 := by
      have h := multinomial7_univ_eq
        (doubledDoubledDoubledQuadPattern7 C P Q R)
        (hsum222 P hP Q hQ R hR) 8 hfact (by norm_num)
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ S ∈ Finset.univ,
            (colDensC ρ u u' S α)
              ^ (doubledDoubledDoubledQuadPattern7
                C P Q R S)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ j ∈ Fintype.piFinset
            (fun S => Finset.range
              (doubledDoubledDoubledQuadPattern7 C P Q R S
                + 1)),
          (∏ S ∈ C,
            ((doubledDoubledDoubledQuadPattern7 C P Q R
                S).choose (j S) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j S))
            * colReMomentPow ρ μG C j u u' := by
      rw [integral_colDens_prod_pow_univ_seven ρ μG hρcont
        u u' (doubledDoubledDoubledQuadPattern7 C P Q R),
        hsupp222 P hP Q hQ R hR]
      exact integral_colDens_prod_doubled_doubled_doubled7
        ρ μG hρcont u u' C P Q R hP hQC hRC
    rw [hmult, hint]
  -- The fiber is exactly the union of the three families.
  have hfib : (Finset.piAntidiag Finset.univ 7).filter
        (fun k => multSupport k = C)
      = S4 ∪ S32 ∪ S222 := by
    refine Finset.ext fun k => ?_
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hk
      have hk7 : ∑ P ∈ Finset.univ, k P = 7 :=
        (Finset.mem_piAntidiag.mp hk.1).1
      have hsupp : multSupport k = C := hk.2
      have hcard : (multSupport k).card = 4 := by
        rw [hsupp]; exact hC
      rcases patterns_of_card_four_seven k hk7 hcard with
        ⟨P₀, hP₀S, hk4, hrest⟩
        | ⟨P₀, hP₀S, P₁, hP₁S, hne, hk3, hk2, hrest⟩
        | ⟨P₀, hP₀S, P₁, hP₁S, P₂, hP₂S, hne₀₁, hne₀₂,
            hne₁₂, hk2₀, hk2₁, hk2₂, hrest⟩
      · left; left
        have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
        refine Finset.mem_image.mpr ⟨P₀, hP₀C, ?_⟩
        funext Q
        by_cases hQP : Q = P₀
        · rw [hQP, hk4]
          simp [quadrupledQuadPattern7]
        · by_cases hQC : Q ∈ C
          · have hkQ : k Q = 1 :=
              hrest Q (hsupp ▸ hQC) hQP
            rw [hkQ]
            simp [quadrupledQuadPattern7, hQP, hQC]
          · have hkQ : k Q = 0 := by
              by_contra hne0
              have hQs : Q ∈ multSupport k :=
                Finset.mem_filter.mpr
                  ⟨Finset.mem_univ Q, hne0⟩
              rw [hsupp] at hQs
              exact hQC hQs
            rw [hkQ]
            simp [quadrupledQuadPattern7, hQP, hQC]
      · left; right
        have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
        have hP₁C : P₁ ∈ C := hsupp ▸ hP₁S
        have hP₁e : P₁ ∈ C.erase P₀ :=
          Finset.mem_erase.mpr ⟨Ne.symm hne, hP₁C⟩
        refine Finset.mem_image.mpr
          ⟨⟨P₀, P₁⟩, Finset.mem_sigma.mpr ⟨hP₀C, hP₁e⟩, ?_⟩
        funext Q
        by_cases hQP : Q = P₀
        · rw [hQP, hk3]
          simp [tripledDoubledQuadPattern7]
        · by_cases hQ1 : Q = P₁
          · rw [hQ1, hk2]
            have hPQ : P₁ ≠ P₀ := Ne.symm hne
            simp [tripledDoubledQuadPattern7, hPQ]
          · by_cases hQC : Q ∈ C
            · have hkQ : k Q = 1 :=
                hrest Q (hsupp ▸ hQC) hQP hQ1
              rw [hkQ]
              simp [tripledDoubledQuadPattern7, hQP, hQ1,
                hQC]
            · have hkQ : k Q = 0 := by
                by_contra hne0
                have hQs : Q ∈ multSupport k :=
                  Finset.mem_filter.mpr
                    ⟨Finset.mem_univ Q, hne0⟩
                rw [hsupp] at hQs
                exact hQC hQs
              rw [hkQ]
              simp [tripledDoubledQuadPattern7, hQP, hQ1,
                hQC]
      · right
        have hP₀C : P₀ ∈ C := hsupp ▸ hP₀S
        have hP₁C : P₁ ∈ C := hsupp ▸ hP₁S
        have hP₂C : P₂ ∈ C := hsupp ▸ hP₂S
        have hP₁e : P₁ ∈ C.erase P₀ :=
          Finset.mem_erase.mpr ⟨Ne.symm hne₀₁, hP₁C⟩
        have hP₂e : P₂ ∈ (C.erase P₀).erase P₁ :=
          Finset.mem_erase.mpr ⟨Ne.symm hne₁₂,
            Finset.mem_erase.mpr ⟨Ne.symm hne₀₂, hP₂C⟩⟩
        refine Finset.mem_image.mpr
          ⟨⟨P₀, P₁, P₂⟩, Finset.mem_sigma.mpr
            ⟨hP₀C, Finset.mem_sigma.mpr ⟨hP₁e, hP₂e⟩⟩, ?_⟩
        funext Q
        by_cases hQP : Q = P₀
        · rw [hQP, hk2₀]
          simp [doubledDoubledDoubledQuadPattern7]
        · by_cases hQ1 : Q = P₁
          · rw [hQ1, hk2₁]
            simp [doubledDoubledDoubledQuadPattern7, hQP]
          · by_cases hQ2 : Q = P₂
            · rw [hQ2, hk2₂]
              simp [doubledDoubledDoubledQuadPattern7,
                hQP, hQ1]
            · by_cases hQC : Q ∈ C
              · have hkQ : k Q = 1 :=
                  hrest Q (hsupp ▸ hQC) hQP hQ1 hQ2
                rw [hkQ]
                simp [doubledDoubledDoubledQuadPattern7,
                  hQP, hQ1, hQ2, hQC]
              · have hkQ : k Q = 0 := by
                  by_contra hne0
                  have hQs : Q ∈ multSupport k :=
                    Finset.mem_filter.mpr
                      ⟨Finset.mem_univ Q, hne0⟩
                  rw [hsupp] at hQs
                  exact hQC hQs
                rw [hkQ]
                simp [doubledDoubledDoubledQuadPattern7,
                  hQP, hQ1, hQ2, hQC]
    · intro hk
      rcases hk with (hk | hk) | hk
      · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_filter.mp (hmem4 P hP)
      · obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hk
        have hx1 : x.1 ∈ C := (Finset.mem_sigma.mp hx).1
        have hx2 : x.2 ∈ C.erase x.1 :=
          (Finset.mem_sigma.mp hx).2
        rw [← hxeq]
        exact Finset.mem_filter.mp (hmem32 x.1 hx1 x.2 hx2)
      · obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hk
        have hx1 : x.1 ∈ C :=
          (Finset.mem_sigma.mp hx).1
        have hx2 : x.2.1 ∈ C.erase x.1 :=
          (Finset.mem_sigma.mp
            (Finset.mem_sigma.mp hx).2).1
        have hx3 : x.2.2 ∈ (C.erase x.1).erase x.2.1 :=
          (Finset.mem_sigma.mp
            (Finset.mem_sigma.mp hx).2).2
        rw [← hxeq]
        exact Finset.mem_filter.mp
          (hmem222 x.1 hx1 x.2.1 hx2 x.2.2 hx3)
  rw [hfib, Finset.sum_union, Finset.sum_union]
  · -- The S222 sum, via the six-to-one ordered-triple count.
    have hS4sum : ∑ k ∈ S4,
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ,
                (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (210 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (quadrupledQuadPattern7 C P Q + 1)),
            (∏ Q ∈ C,
              ((quadrupledQuadPattern7 C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u') := by
      rw [hS4, Finset.sum_image]
      · exact Finset.sum_congr rfl fun P hP => hval4 P hP
      · intro P hP P' hP' h
        by_contra hne
        have h2 := congrFun h P
        have hmem : P ∈ C := hP
        have hPP' : quadrupledQuadPattern7 C P' P = 1 := by
          show (if P = P' then (4 : ℕ)
            else if P ∈ C then 1 else 0) = 1
          rw [if_neg hne, if_pos hmem]
        rw [hPP'] at h2
        simp [quadrupledQuadPattern7] at h2
    have hS32sum : ∑ k ∈ S32,
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ,
                (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (tripledDoubledQuadPattern7 C P Q R + 1)),
            (∏ R ∈ C,
              ((tripledDoubledQuadPattern7 C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u') := by
      rw [hS32, Finset.sum_image]
      · rw [Finset.sum_sigma]
        exact Finset.sum_congr rfl fun P hP =>
          Finset.sum_congr rfl fun Q hQ => hval32 P hP Q hQ
      · intro x hx y hy h
        have hx1 : x.1 ∈ C := (Finset.mem_sigma.mp hx).1
        have hx2 : x.2 ∈ C.erase x.1 :=
          (Finset.mem_sigma.mp hx).2
        have hy1 : y.1 ∈ C := (Finset.mem_sigma.mp hy).1
        have hy2 : y.2 ∈ C.erase y.1 :=
          (Finset.mem_sigma.mp hy).2
        have hx2C : x.2 ∈ C := (Finset.mem_erase.mp hx2).2
        have hy2C : y.2 ∈ C := (Finset.mem_erase.mp hy2).2
        have hxne : x.2 ≠ x.1 := (Finset.mem_erase.mp hx2).1
        have hyne : y.2 ≠ y.1 := (Finset.mem_erase.mp hy2).1
        have hfst : x.1 = y.1 := by
          by_contra hne1
          have h3 : tripledDoubledQuadPattern7 C y.1 y.2
                x.1 = 3 := by
            have h2 : tripledDoubledQuadPattern7 C x.1 x.2
                  x.1
                = tripledDoubledQuadPattern7 C y.1 y.2
                  x.1 := congrFun h x.1
            rw [show tripledDoubledQuadPattern7 C x.1 x.2
                x.1 = 3 from by
              simp [tripledDoubledQuadPattern7]] at h2
            exact h2.symm
          have hle : tripledDoubledQuadPattern7 C y.1 y.2
              x.1 ≤ 2 := by
            by_cases h12 : x.1 = y.2
            · have e : tripledDoubledQuadPattern7 C y.1 y.2
                    x.1 = 2 := by
                rw [h12]
                show (if y.2 = y.1 then (3 : ℕ)
                  else if y.2 = y.2 then 2
                  else if y.2 ∈ C then 1 else 0) = 2
                rw [if_neg hyne, if_pos rfl]
              omega
            · simp [tripledDoubledQuadPattern7, hne1, h12,
                hx1]
          omega
        have hsnd : x.2 = y.2 := by
          by_contra hne2
          have h2v : tripledDoubledQuadPattern7 C y.1 y.2
                x.2 = 2 := by
            have h2 : tripledDoubledQuadPattern7 C x.1 x.2
                  x.2
                = tripledDoubledQuadPattern7 C y.1 y.2
                  x.2 := congrFun h x.2
            rw [show tripledDoubledQuadPattern7 C x.1 x.2
                x.2 = 2 from by
              simp [tripledDoubledQuadPattern7, hxne]] at h2
            exact h2.symm
          have hne12 : x.2 ≠ y.1 := by
            rw [← hfst]
            exact hxne
          have hle : tripledDoubledQuadPattern7 C y.1 y.2
              x.2 ≤ 1 := by
            simp [tripledDoubledQuadPattern7, hne12, hne2,
              hx2C]
          omega
        exact Sigma.ext hfst (heq_of_eq hsnd)
    have hS222sum : ∑ k ∈ S222,
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ,
                (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, ∑ Q ∈ C.erase P,
          ∑ R ∈ (C.erase P).erase Q, (105 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun S => Finset.range
                (doubledDoubledDoubledQuadPattern7 C P Q R S
                  + 1)),
            (∏ S ∈ C,
              ((doubledDoubledDoubledQuadPattern7 C P Q R
                  S).choose (j S) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j S))
              * colReMomentPow ρ μG C j u u') := by
      have hdouble : ∑ x ∈ C.sigma (fun P =>
            (C.erase P).sigma (fun Q => (C.erase P).erase Q)),
          ((Nat.multinomial Finset.univ
              (doubledDoubledDoubledQuadPattern7 C x.1
                x.2.1 x.2.2) : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ,
                  (colDensC ρ u u' P α)
                    ^ (doubledDoubledDoubledQuadPattern7 C
                      x.1 x.2.1 x.2.2 P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ k ∈ S222, 6
            * (((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG)) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun x : Σ _ : LayerColumn N,
              Σ _ : LayerColumn N, LayerColumn N =>
            doubledDoubledDoubledQuadPattern7 C x.1
              x.2.1 x.2.2)
          (f := fun x =>
            ((Nat.multinomial Finset.univ
                (doubledDoubledDoubledQuadPattern7 C x.1
                  x.2.1 x.2.2) : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α)
                      ^ (doubledDoubledDoubledQuadPattern7
                        C x.1 x.2.1 x.2.2 P)
                  ∂(Measure.pi fun _ : LayerSite N => μG))]
        · refine Finset.sum_congr rfl fun k hk => ?_
          obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hk
          -- The six permutations of the doubled triple.
          rcases x₀ with ⟨P₀, Q₀, R₀⟩
          have hP₀ : P₀ ∈ C := (Finset.mem_sigma.mp hx₀).1
          have hQ₀ : Q₀ ∈ C.erase P₀ :=
            (Finset.mem_sigma.mp
              (Finset.mem_sigma.mp hx₀).2).1
          have hR₀ : R₀ ∈ (C.erase P₀).erase Q₀ :=
            (Finset.mem_sigma.mp
              (Finset.mem_sigma.mp hx₀).2).2
          have hQ₀C : Q₀ ∈ C :=
            (Finset.mem_erase.mp hQ₀).2
          have hR₀C : R₀ ∈ C :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR₀).2).2
          have hneQ : Q₀ ≠ P₀ :=
            (Finset.mem_erase.mp hQ₀).1
          have hneR1 : R₀ ≠ P₀ :=
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hR₀).2).1
          have hneR2 : R₀ ≠ Q₀ :=
            (Finset.mem_erase.mp hR₀).1
          have pe2 : doubledDoubledDoubledQuadPattern7 C
                P₀ R₀ Q₀
              = doubledDoubledDoubledQuadPattern7 C
                P₀ Q₀ R₀ :=
            (doubledDoubledDoubledQuadPattern7_swap_snd
              C P₀ Q₀ R₀).symm
          have pe3 : doubledDoubledDoubledQuadPattern7 C
                Q₀ P₀ R₀
              = doubledDoubledDoubledQuadPattern7 C
                P₀ Q₀ R₀ :=
            (doubledDoubledDoubledQuadPattern7_swap_fst
              C P₀ Q₀ R₀).symm
          have pe4 : doubledDoubledDoubledQuadPattern7 C
                Q₀ R₀ P₀
              = doubledDoubledDoubledQuadPattern7 C
                P₀ Q₀ R₀ :=
            (doubledDoubledDoubledQuadPattern7_swap_fst
              C Q₀ R₀ P₀).trans
              ((doubledDoubledDoubledQuadPattern7_swap_snd
                C R₀ Q₀ P₀).trans
                ((doubledDoubledDoubledQuadPattern7_swap_fst
                  C R₀ P₀ Q₀).trans
                  (doubledDoubledDoubledQuadPattern7_swap_snd
                    C P₀ R₀ Q₀)))
          have pe5 : doubledDoubledDoubledQuadPattern7 C
                R₀ P₀ Q₀
              = doubledDoubledDoubledQuadPattern7 C
                P₀ Q₀ R₀ :=
            (doubledDoubledDoubledQuadPattern7_swap_fst
              C R₀ P₀ Q₀).trans
              (doubledDoubledDoubledQuadPattern7_swap_snd
                C P₀ R₀ Q₀)
          have pe6 : doubledDoubledDoubledQuadPattern7 C
                R₀ Q₀ P₀
              = doubledDoubledDoubledQuadPattern7 C
                P₀ Q₀ R₀ :=
            (doubledDoubledDoubledQuadPattern7_swap_snd
              C R₀ Q₀ P₀).trans
              ((doubledDoubledDoubledQuadPattern7_swap_fst
                C R₀ P₀ Q₀).trans
                (doubledDoubledDoubledQuadPattern7_swap_snd
                  C P₀ R₀ Q₀))
          have me2 : (⟨P₀, R₀, Q₀⟩ :
              Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)
              ∈ C.sigma (fun P => (C.erase P).sigma
                (fun Q => (C.erase P).erase Q)) :=
            Finset.mem_sigma.mpr ⟨hP₀,
              Finset.mem_sigma.mpr
                ⟨Finset.mem_erase.mpr ⟨hneR1, hR₀C⟩,
                  Finset.mem_erase.mpr
                    ⟨Ne.symm hneR2, hQ₀⟩⟩⟩
          have me3 : (⟨Q₀, P₀, R₀⟩ :
              Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)
              ∈ C.sigma (fun P => (C.erase P).sigma
                (fun Q => (C.erase P).erase Q)) :=
            Finset.mem_sigma.mpr ⟨hQ₀C,
              Finset.mem_sigma.mpr
                ⟨Finset.mem_erase.mpr
                    ⟨Ne.symm hneQ, hP₀⟩,
                  Finset.mem_erase.mpr ⟨hneR1,
                    Finset.mem_erase.mpr
                      ⟨hneR2, hR₀C⟩⟩⟩⟩
          have me4 : (⟨Q₀, R₀, P₀⟩ :
              Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)
              ∈ C.sigma (fun P => (C.erase P).sigma
                (fun Q => (C.erase P).erase Q)) :=
            Finset.mem_sigma.mpr ⟨hQ₀C,
              Finset.mem_sigma.mpr
                ⟨Finset.mem_erase.mpr ⟨hneR2, hR₀C⟩,
                  Finset.mem_erase.mpr
                    ⟨Ne.symm hneR1,
                      Finset.mem_erase.mpr
                        ⟨Ne.symm hneQ, hP₀⟩⟩⟩⟩
          have me5 : (⟨R₀, P₀, Q₀⟩ :
              Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)
              ∈ C.sigma (fun P => (C.erase P).sigma
                (fun Q => (C.erase P).erase Q)) :=
            Finset.mem_sigma.mpr ⟨hR₀C,
              Finset.mem_sigma.mpr
                ⟨Finset.mem_erase.mpr
                    ⟨Ne.symm hneR1, hP₀⟩,
                  Finset.mem_erase.mpr ⟨hneQ,
                    Finset.mem_erase.mpr
                      ⟨Ne.symm hneR2, hQ₀C⟩⟩⟩⟩
          have me6 : (⟨R₀, Q₀, P₀⟩ :
              Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)
              ∈ C.sigma (fun P => (C.erase P).sigma
                (fun Q => (C.erase P).erase Q)) :=
            Finset.mem_sigma.mpr ⟨hR₀C,
              Finset.mem_sigma.mpr
                ⟨Finset.mem_erase.mpr
                    ⟨Ne.symm hneR2, hQ₀C⟩,
                  Finset.mem_erase.mpr
                    ⟨Ne.symm hneQ,
                      Finset.mem_erase.mpr
                        ⟨Ne.symm hneR1, hP₀⟩⟩⟩⟩
          have hfilt : (C.sigma (fun P =>
                (C.erase P).sigma
                  (fun Q => (C.erase P).erase Q))).filter
                (fun x =>
                  doubledDoubledDoubledQuadPattern7 C x.1
                    x.2.1 x.2.2
                    = doubledDoubledDoubledQuadPattern7 C
                      P₀ Q₀ R₀)
              = {⟨P₀, Q₀, R₀⟩, ⟨P₀, R₀, Q₀⟩, ⟨Q₀, P₀, R₀⟩,
                  ⟨Q₀, R₀, P₀⟩, ⟨R₀, P₀, Q₀⟩,
                  ⟨R₀, Q₀, P₀⟩} := by
            refine Finset.ext fun x => ?_
            rcases x with ⟨A, B, D⟩
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · intro hx
              have hA : A ∈ C :=
                (Finset.mem_sigma.mp hx.1).1
              have hB : B ∈ C.erase A :=
                (Finset.mem_sigma.mp
                  (Finset.mem_sigma.mp hx.1).2).1
              have hD : D ∈ (C.erase A).erase B :=
                (Finset.mem_sigma.mp
                  (Finset.mem_sigma.mp hx.1).2).2
              have hBC : B ∈ C :=
                (Finset.mem_erase.mp hB).2
              have hDC : D ∈ C :=
                (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hD).2).2
              have hneB : B ≠ A :=
                (Finset.mem_erase.mp hB).1
              have hneD1 : D ≠ A :=
                (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hD).2).1
              have hneD2 : D ≠ B :=
                (Finset.mem_erase.mp hD).1
              have heq := hx.2
              have hA3 : A = P₀ ∨ A = Q₀ ∨ A = R₀ := by
                have h2 : doubledDoubledDoubledQuadPattern7
                      C P₀ Q₀ R₀ A = 2 := by
                  rw [← heq]
                  simp [doubledDoubledDoubledQuadPattern7]
                by_contra hcon
                push Not at hcon
                have hle :
                    doubledDoubledDoubledQuadPattern7 C
                      P₀ Q₀ R₀ A ≤ 1 := by
                  simp [doubledDoubledDoubledQuadPattern7,
                    hcon.1, hcon.2.1, hcon.2.2, hA]
                omega
              have hB3 : B = P₀ ∨ B = Q₀ ∨ B = R₀ := by
                have h2 : doubledDoubledDoubledQuadPattern7
                      C P₀ Q₀ R₀ B = 2 := by
                  rw [← heq]
                  simp [doubledDoubledDoubledQuadPattern7,
                    hneB]
                by_contra hcon
                push Not at hcon
                have hle :
                    doubledDoubledDoubledQuadPattern7 C
                      P₀ Q₀ R₀ B ≤ 1 := by
                  simp [doubledDoubledDoubledQuadPattern7,
                    hcon.1, hcon.2.1, hcon.2.2, hBC]
                omega
              have hD3 : D = P₀ ∨ D = Q₀ ∨ D = R₀ := by
                have h2 : doubledDoubledDoubledQuadPattern7
                      C P₀ Q₀ R₀ D = 2 := by
                  rw [← heq]
                  simp [doubledDoubledDoubledQuadPattern7,
                    hneD1, hneD2]
                by_contra hcon
                push Not at hcon
                have hle :
                    doubledDoubledDoubledQuadPattern7 C
                      P₀ Q₀ R₀ D ≤ 1 := by
                  simp [doubledDoubledDoubledQuadPattern7,
                    hcon.1, hcon.2.1, hcon.2.2, hDC]
                omega
              rcases hA3 with rfl | rfl | rfl <;>
                rcases hB3 with rfl | rfl | rfl <;>
                rcases hD3 with rfl | rfl | rfl <;>
                first
                  | exact (hneB rfl).elim
                  | exact (hneD1 rfl).elim
                  | exact (hneD2 rfl).elim
                  | simp only [Sigma.mk.injEq,
                      eq_self_iff_true, true_and, and_true,
                      or_true, true_or]
            · intro hx
              rcases hx with h | h | h | h | h | h
              · have hA' : A = P₀ := congrArg Sigma.fst h
                have hB' : B = Q₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = R₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨hx₀, rfl⟩
              · have hA' : A = P₀ := congrArg Sigma.fst h
                have hB' : B = R₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = Q₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨me2, pe2⟩
              · have hA' : A = Q₀ := congrArg Sigma.fst h
                have hB' : B = P₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = R₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨me3, pe3⟩
              · have hA' : A = Q₀ := congrArg Sigma.fst h
                have hB' : B = R₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = P₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨me4, pe4⟩
              · have hA' : A = R₀ := congrArg Sigma.fst h
                have hB' : B = P₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = Q₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨me5, pe5⟩
              · have hA' : A = R₀ := congrArg Sigma.fst h
                have hB' : B = Q₀ :=
                  congrArg (fun z => z.2.1) h
                have hD' : D = P₀ :=
                  congrArg (fun z => z.2.2) h
                subst hA'; subst hB'; subst hD'
                exact ⟨me6, pe6⟩
          have hcard6 : ({⟨P₀, Q₀, R₀⟩, ⟨P₀, R₀, Q₀⟩,
                ⟨Q₀, P₀, R₀⟩, ⟨Q₀, R₀, P₀⟩, ⟨R₀, P₀, Q₀⟩,
                ⟨R₀, Q₀, P₀⟩} :
              Finset (Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)).card
              = 6 := by
            have hne : ∀ a b : LayerColumn N, a ≠ b →
                ∀ c d : LayerColumn N, c ≠ d →
                True := fun _ _ _ _ _ _ => trivial
            rw [Finset.card_insert_of_notMem (by
              simp [Sigma.mk.injEq, hneQ, hneR1, hneR2,
                Ne.symm hneQ, Ne.symm hneR1,
                Ne.symm hneR2]),
              Finset.card_insert_of_notMem (by
              simp [Sigma.mk.injEq, hneQ, hneR1, hneR2,
                Ne.symm hneQ, Ne.symm hneR1,
                Ne.symm hneR2]),
              Finset.card_insert_of_notMem (by
              simp [Sigma.mk.injEq, hneQ, hneR1, hneR2,
                Ne.symm hneQ, Ne.symm hneR1,
                Ne.symm hneR2]),
              Finset.card_insert_of_notMem (by
              simp [Sigma.mk.injEq, hneQ, hneR1, hneR2,
                Ne.symm hneQ, Ne.symm hneR1,
                Ne.symm hneR2]),
              Finset.card_insert_of_notMem (by
              simp [Sigma.mk.injEq, hneQ, hneR1, hneR2,
                Ne.symm hneQ, Ne.symm hneR1,
                Ne.symm hneR2]),
              Finset.card_singleton]
          rw [hfilt]
          have hsum6 : ∑ x ∈ ({⟨P₀, Q₀, R₀⟩, ⟨P₀, R₀, Q₀⟩,
                ⟨Q₀, P₀, R₀⟩, ⟨Q₀, R₀, P₀⟩, ⟨R₀, P₀, Q₀⟩,
                ⟨R₀, Q₀, P₀⟩} :
              Finset (Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)),
              ((Nat.multinomial Finset.univ
                  (doubledDoubledDoubledQuadPattern7 C x.1
                    x.2.1 x.2.2) : ℝ))
                * ∫ α : LayerSite N → G,
                    ∏ P ∈ Finset.univ,
                      (colDensC ρ u u' P α)
                        ^ (doubledDoubledDoubledQuadPattern7
                          C x.1 x.2.1 x.2.2 P)
                    ∂(Measure.pi fun _ : LayerSite N => μG)
            = ∑ _x ∈ ({⟨P₀, Q₀, R₀⟩, ⟨P₀, R₀, Q₀⟩,
                ⟨Q₀, P₀, R₀⟩, ⟨Q₀, R₀, P₀⟩, ⟨R₀, P₀, Q₀⟩,
                ⟨R₀, Q₀, P₀⟩} :
              Finset (Σ _ : LayerColumn N,
                Σ _ : LayerColumn N, LayerColumn N)),
              ((Nat.multinomial Finset.univ
                  (doubledDoubledDoubledQuadPattern7 C
                    P₀ Q₀ R₀) : ℝ))
                * ∫ α : LayerSite N → G,
                    ∏ P ∈ Finset.univ,
                      (colDensC ρ u u' P α)
                        ^ (doubledDoubledDoubledQuadPattern7
                          C P₀ Q₀ R₀ P)
                    ∂(Measure.pi fun _ : LayerSite N
                      => μG) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            simp only [Finset.mem_insert,
              Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl
              | rfl
            · rfl
            · rw [pe2]
            · rw [pe3]
            · rw [pe4]
            · rw [pe5]
            · rw [pe6]
          rw [hsum6, Finset.sum_const, hcard6,
            nsmul_eq_mul]
          norm_num
        · intro x hx
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hordered : ∑ x ∈ C.sigma (fun P =>
            (C.erase P).sigma (fun Q => (C.erase P).erase Q)),
          ((Nat.multinomial Finset.univ
              (doubledDoubledDoubledQuadPattern7 C x.1
                x.2.1 x.2.2) : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ,
                  (colDensC ρ u u' P α)
                    ^ (doubledDoubledDoubledQuadPattern7 C
                      x.1 x.2.1 x.2.2 P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (630 : ℝ)
            * (∑ j ∈ Fintype.piFinset
                (fun S => Finset.range
                  (doubledDoubledDoubledQuadPattern7
                    C P Q R S + 1)),
              (∏ S ∈ C,
                ((doubledDoubledDoubledQuadPattern7
                    C P Q R S).choose (j S) : ℝ)
                  * (-(d : ℝ)⁻¹) ^ (j S))
                * colReMomentPow ρ μG C j u u') := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [Finset.sum_sigma]
        exact Finset.sum_congr rfl fun Q hQ =>
          Finset.sum_congr rfl fun R hR =>
            hval222 P hP Q hQ R hR
      have h6L : 6 * (∑ k ∈ S222,
            ((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG))
          = 6 * (∑ P ∈ C, ∑ Q ∈ C.erase P,
              ∑ R ∈ (C.erase P).erase Q, (105 : ℝ)
              * (∑ j ∈ Fintype.piFinset
                  (fun S => Finset.range
                    (doubledDoubledDoubledQuadPattern7
                      C P Q R S + 1)),
                (∏ S ∈ C,
                  ((doubledDoubledDoubledQuadPattern7
                      C P Q R S).choose (j S) : ℝ)
                    * (-(d : ℝ)⁻¹) ^ (j S))
                  * colReMomentPow ρ μG C j u u')) := by
        rw [Finset.mul_sum, ← hdouble, hordered,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun R _ => ?_
        ring
      exact mul_left_cancel₀ (by norm_num : (6 : ℝ) ≠ 0)
        h6L
    rw [hS4sum, hS32sum, hS222sum]
  · -- Disjointness: `S4` against `S32` (value `4` vs `≤ 3`).
    refine Finset.disjoint_left.mpr fun k hk4 hk32 => ?_
    obtain ⟨P, hP, hPeq⟩ := Finset.mem_image.mp hk4
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hk32
    have hyne : y.2 ≠ y.1 :=
      (Finset.mem_erase.mp (Finset.mem_sigma.mp hy).2).1
    have h4 : k P = 4 := by
      rw [← hPeq]
      simp [quadrupledQuadPattern7]
    have hle3 : k P ≤ 3 := by
      rw [← hyeq]
      by_cases h1 : P = y.1
      · simp [tripledDoubledQuadPattern7, h1]
      · by_cases h2 : P = y.2
        · have e : tripledDoubledQuadPattern7 C y.1 y.2
                P = 2 := by
            rw [h2]
            show (if y.2 = y.1 then (3 : ℕ)
              else if y.2 = y.2 then 2
              else if y.2 ∈ C then 1 else 0) = 2
            rw [if_neg hyne, if_pos rfl]
          omega
        · by_cases hPC : P ∈ C
          · simp [tripledDoubledQuadPattern7, h1, h2, hPC]
          · simp [tripledDoubledQuadPattern7, h1, h2, hPC]
    omega

  · -- Disjointness: `S4 ∪ S32` against `S222` (value `≥ 3` vs `≤ 2`).
    refine Finset.disjoint_left.mpr fun k hkA hk222 => ?_
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hk222
    have hle2 : ∀ A, k A ≤ 2 := by
      intro A
      rw [← hxeq]
      by_cases h1 : A = x.1
      · simp [doubledDoubledDoubledQuadPattern7, h1]
      · by_cases h2 : A = x.2.1
        · simp [doubledDoubledDoubledQuadPattern7, h1, h2]
        · by_cases h3 : A = x.2.2
          · simp [doubledDoubledDoubledQuadPattern7, h1,
              h2, h3]
          · by_cases hAC : A ∈ C
            · simp [doubledDoubledDoubledQuadPattern7, h1,
                h2, h3, hAC]
            · simp [doubledDoubledDoubledQuadPattern7, h1,
                h2, h3, hAC]
    rcases Finset.mem_union.mp hkA with hk4 | hk32
    · obtain ⟨P, hP, hPeq⟩ := Finset.mem_image.mp hk4
      have h4 : k P = 4 := by
        rw [← hPeq]
        simp [quadrupledQuadPattern7]
      have := hle2 P
      omega
    · obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hk32
      have h3 : k y.1 = 3 := by
        rw [← hyeq]
        simp [tripledDoubledQuadPattern7]
      have := hle2 y.1
      omega

/-! ## B7-2b-iii settlements: privacy helper and the
card-5 erasure settlement -/

/-- **Privacy from degree one.** If `siteDegree S s = 1`
and `Q ∈ S` reads `s`, then no other column of `S`
reads `s`: the filter defining the degree is the
singleton `{Q}`. -/
theorem privateSite_forall_of_siteDegree_eq_one
    {S : Finset (LayerColumn N)}
    {Q : LayerColumn N} {s : LayerSite N}
    (hQS : Q ∈ S) (hsQ : s ∈ colSites Q)
    (hdeg : siteDegree S s = 1) :
    ∀ Y ∈ S, Y ≠ Q → s ∉ colSites Y := by
  intro Y hYS hYQ hsY
  have hQf : Q ∈ S.filter (fun P => s ∈ colSites P) :=
    Finset.mem_filter.mpr ⟨hQS, hsQ⟩
  have hYf : Y ∈ S.filter (fun P => s ∈ colSites P) :=
    Finset.mem_filter.mpr ⟨hYS, hsY⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdeg
  have hQa : Q = a := Finset.mem_singleton.mp (ha ▸ hQf)
  have hYa : Y = a := Finset.mem_singleton.mp (ha ▸ hYf)
  exact hYQ (hYa.trans hQa.symm)

/-- **The tripled penta moment factors at a private
column.** Let `Q ∈ C` have a site `s` of degree `1` in
`C` (a private site). For every `P ∈ C`, the tripled
penta moment at `P` factors through the erasure of
`Q`: at `P = Q` it is `realMoment 3` times the plain
moment on the erased (card-4, when `|C| = 5`) support,
by B6's `tripledQuadReMoment_strip_tripled`; at
`P ≠ Q` it is `e₁` times the tripled penta moment on
the erased support, by B6's
`tripledQuadReMoment_strip_single`. The penta moment
is `tripledQuadReMoment` itself
(`tripledPentaReMoment_eq_tripledQuadReMoment`). -/
theorem tripledPentaReMoment_factor_of_private
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {Q : LayerColumn N} {s : LayerSite N}
    (hQC : Q ∈ C) (hsQ : s ∈ colSites Q)
    (hdeg : siteDegree C s = 1)
    (P : LayerColumn N) (hPC : P ∈ C) :
    tripledPentaReMoment ρ μG C P u u'
      = if P = Q then
          realMoment ρ μG 3
            * quadReMoment ρ μG (C.erase Q) u u'
        else e1 ρ μG
          * tripledPentaReMoment ρ μG (C.erase Q) P u u' := by
  have hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y :=
    privateSite_forall_of_siteDegree_eq_one hQC hsQ hdeg
  rw [tripledPentaReMoment_eq_tripledQuadReMoment]
  by_cases hPQ : P = Q
  · subst hPQ
    rw [if_pos rfl]
    exact tripledQuadReMoment_strip_tripled (ρ := ρ)
      (μG := μG) hN hN3 hρcont u u' hsQ hpriv
  · rw [if_neg hPQ]
    have h := tripledQuadReMoment_strip_single (ρ := ρ)
      (μG := μG) hN hN3 hρcont u u' hPC hQC
      (fun h => hPQ h.symm) hsQ hpriv
    calc tripledQuadReMoment ρ μG C P u u'
        = e1 ρ μG
            * tripledQuadReMoment ρ μG (C.erase Q) P u u' :=
          h
      _ = e1 ρ μG
            * tripledPentaReMoment ρ μG (C.erase Q) P u u' := by
          rw [tripledPentaReMoment_eq_tripledQuadReMoment]

/-- **The doubled-doubled penta moment factors at a
private column.** Let `Q ∈ C` have a private site in
`C`. For every pair of distinct doubled columns
`P, R ∈ C`, the `(2,2,1,1,1)` penta moment factors
through the erasure of `Q`: at `Q = P` it is
`realMoment 2` times the doubled moment on the erased
support (B6's `doubledDoubledQuadReMoment_strip_first`);
at `Q = R` likewise with the seats exchanged
(`_strip_second`); at a third column `Q` it is `e₁`
times the doubled-doubled penta moment on the erased
support (`_strip_single`). The penta moment is
`doubledDoubledQuadReMoment` itself
(`doubledDoubledPentaReMoment_eq`). -/
theorem doubledDoubledPentaReMoment_factor_of_private
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {Q : LayerColumn N} {s : LayerSite N}
    (hQC : Q ∈ C) (hsQ : s ∈ colSites Q)
    (hdeg : siteDegree C s = 1)
    (P : LayerColumn N) (hPC : P ∈ C)
    (R : LayerColumn N) (hRC : R ∈ C) (hRP : R ≠ P) :
    doubledDoubledPentaReMoment ρ μG C P R u u'
      = if Q = P then
          realMoment ρ μG 2
            * doubledQuadReMoment ρ μG (C.erase Q) R u u'
        else if Q = R then
          realMoment ρ μG 2
            * doubledQuadReMoment ρ μG (C.erase Q) P u u'
        else e1 ρ μG
          * doubledDoubledPentaReMoment ρ μG (C.erase Q)
            P R u u' := by
  have hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y :=
    privateSite_forall_of_siteDegree_eq_one hQC hsQ hdeg
  rw [doubledDoubledPentaReMoment_eq]
  by_cases hQP : Q = P
  · subst hQP
    rw [if_pos rfl]
    exact doubledDoubledQuadReMoment_strip_first (ρ := ρ)
      (μG := μG) hN hN3 hρcont u u' hRC hRP hsQ hpriv
  · rw [if_neg hQP]
    by_cases hQR : Q = R
    · subst hQR
      rw [if_pos rfl]
      exact doubledDoubledQuadReMoment_strip_second
        (ρ := ρ) (μG := μG) hN hN3 hρcont u u' hPC hRP
        hsQ hpriv
    · rw [if_neg hQR]
      have h := doubledDoubledQuadReMoment_strip_single
        (ρ := ρ) (μG := μG) hN hN3 hρcont u u' hPC hRC
        hQC hQP hQR hRP hsQ hpriv
      calc doubledDoubledQuadReMoment ρ μG C P R u u'
          = e1 ρ μG
              * doubledDoubledQuadReMoment ρ μG
                (C.erase Q) P R u u' := h
        _ = e1 ρ μG
              * doubledDoubledPentaReMoment ρ μG
                (C.erase Q) P R u u' := by
            rw [doubledDoubledPentaReMoment_eq]

/-- **Support reduction for generalized moments.** A
generalized moment over `C` at exponent function `j`
equals the same moment over its own exponent support
inside `C`: the columns where `j` vanishes contribute
the factor `colRe ^ 0 = 1`. Every term of the pattern
values in this section is therefore a generalized
moment over a subset of its fiber support — a proper
subset whenever some exponent vanishes. -/
theorem colReMomentPow_support_reduce
    {C : Finset (LayerColumn N)} (j : LayerColumn N → ℕ)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C j u u'
      = colReMomentPow ρ μG
          (C.filter (fun Q => j Q ≠ 0)) j u u' := by
  classical
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (∏ P ∈ C, (colRe ρ u u' P α) ^ (j P))
    = ∏ P ∈ C.filter (fun Q => j Q ≠ 0),
      (colRe ρ u u' P α) ^ (j P)
  have h1 : ∏ Q ∈ C.filter (fun Q => ¬ j Q ≠ 0),
        (colRe ρ u u' Q α) ^ (j Q) = 1 :=
    Finset.prod_eq_one fun Q hQ => by
      have hj0 : j Q = 0 :=
        not_not.mp (Finset.mem_filter.mp hQ).2
      rw [hj0, pow_zero]
  rw [← Finset.prod_filter_mul_prod_filter_not C
    (fun Q => j Q ≠ 0), h1, mul_one]

/-- **B7-0 settlement, card 5: the erasure claim is
CONFIRMED in the predicted direction.** For every
5-support `C` (at general `(G, ρ)`, even `N ≥ 3`,
continuous representation): (1) the card-5 fiber over
`C` is exactly the two pattern families
`(3,1,1,1,1)` and `(2,2,1,1,1)`
(`fiber_card_five7`); (2) `C` has a private column
(B7-0's `card_five_erasure_death`, applied to the
tripled pattern at any column of `C`); (3) at any
private column of `C`, both card-5 top moments factor
through the private-column erasure into card-4
content (`tripledPentaReMoment_factor_of_private`,
`doubledDoubledPentaReMoment_factor_of_private`).
Together with `colReMomentPow_support_reduce` — every
non-top term of the fiber value is a generalized
moment over a subset of `C` at a non-channel exponent
— the card-5 card carries no live channel: it is
erased through the lower excesses, as B7-0 §5
predicted. This is a settlement of the erasure claim
only: no sign for any fiber sum is asserted, and the
dressing/excess conversion of the pattern values is
B7-2b-iv/v work. -/
theorem card_five_erasure_settlement (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    (∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (840 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (tripledQuintuplePattern C P Q + 1)),
            (∏ Q ∈ C,
              ((tripledQuintuplePattern C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u')
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (doubledDoubledQuintuplePattern C P Q R
                  + 1)),
            (∏ R ∈ C,
              ((doubledDoubledQuintuplePattern C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u'))
    ∧ HasPrivateColumn C
    ∧ (∀ Q ∈ C, ∀ s ∈ colSites Q, siteDegree C s = 1 →
        (∀ P ∈ C, tripledPentaReMoment ρ μG C P u u'
          = if P = Q then
              realMoment ρ μG 3
                * quadReMoment ρ μG (C.erase Q) u u'
            else e1 ρ μG
              * tripledPentaReMoment ρ μG (C.erase Q) P
                u u')
        ∧ (∀ P ∈ C, ∀ R ∈ C, R ≠ P →
            doubledDoubledPentaReMoment ρ μG C P R u u'
            = if Q = P then
                realMoment ρ μG 2
                  * doubledQuadReMoment ρ μG (C.erase Q) R
                    u u'
              else if Q = R then
                realMoment ρ μG 2
                  * doubledQuadReMoment ρ μG (C.erase Q) P
                    u u'
              else e1 ρ μG
                * doubledDoubledPentaReMoment ρ μG
                  (C.erase Q) P R u u')) := by
  classical
  obtain ⟨P₀, hP₀⟩ : C.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsupp : multSupport
        (tripledQuintuplePattern C P₀) = C := by
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hQ
      by_cases hQP : Q = P₀
      · exact hQP ▸ hP₀
      · by_contra hQC
        exact hQ (by
          simp [tripledQuintuplePattern, hQP, hQC])
    · intro hQC
      by_cases hQP : Q = P₀
      · subst hQP
        simp [tripledQuintuplePattern]
      · simp [tripledQuintuplePattern, hQP, hQC]
  have hsum : ∑ Q, tripledQuintuplePattern C P₀ Q = 7 := by
    have h1 : ∑ Q, tripledQuintuplePattern C P₀ Q
        = ∑ Q ∈ C, tripledQuintuplePattern C P₀ Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P₀ := fun h => hQ (h.symm ▸ hP₀)
          simp [tripledQuintuplePattern, hQP, hQ])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP₀]
    have h2 : ∀ Q ∈ C.erase P₀,
        tripledQuintuplePattern C P₀ Q = 1 :=
      fun Q hQ => by
        simp [tripledQuintuplePattern,
          (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP₀, hC]
    have hPP : tripledQuintuplePattern C P₀ P₀ = 3 := by
      simp [tripledQuintuplePattern]
    rw [hPP]
    decide
  have hprivC : HasPrivateColumn C := by
    have h := (card_five_erasure_death hN hN3
      (tripledQuintuplePattern C P₀) hsum
      (by rw [hsupp]; exact hC)).2
    rwa [hsupp] at h
  refine ⟨fiber_card_five7 (ρ := ρ) (μG := μG) hN hN3
    hρcont u u' C hC,
    hprivC, ?_⟩
  intro Q hQC s hsQ hdeg
  exact ⟨fun P hPC =>
      tripledPentaReMoment_factor_of_private (ρ := ρ)
        (μG := μG) hN hN3 hρcont u u' hQC hsQ hdeg P hPC,
    fun P hPC R hRC hRP =>
      doubledDoubledPentaReMoment_factor_of_private
        (ρ := ρ) (μG := μG) hN hN3 hρcont u u' hQC hsQ
        hdeg P hPC R hRC hRP⟩

/-! ## B7-2b-iii settlements: the card-6 family split -/

/-- **Bare-support trichotomy at card 6** (B7-0's
`card_six_live_or_private` mechanism, restated for a
bare 6-support): every 6-support is a `C₆` support, a
`Θ(2,2,2)` support, or has a private column. The
multiplicity fed to B7-0 is the doubled sextuple
pattern at any column of `C`; its support is `C`
itself. -/
theorem card_six_support_live_or_private (hN : Even N)
    (hN3 : 3 ≤ N)
    {C : Finset (LayerColumn N)}
    (hC : C ∈ Finset.powersetCard 6 Finset.univ) :
    C ∈ c6Supports ∨ C ∈ thetaSupports
      ∨ HasPrivateColumn C := by
  classical
  have hcard : C.card = 6 :=
    (Finset.mem_powersetCard.mp hC).2
  obtain ⟨P₀, hP₀⟩ : C.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsupp : multSupport
        (doubledSextuplePattern C P₀) = C := by
    refine Finset.ext fun Q => ?_
    simp only [multSupport_eq_filter7, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hQP : Q = P₀
    · subst hQP
      simp [doubledSextuplePattern, hP₀]
    · by_cases hQC : Q ∈ C <;>
        simp [doubledSextuplePattern, hQP, hQC]
  have hsum : ∑ Q, doubledSextuplePattern C P₀ Q = 7 := by
    have h1 : ∑ Q, doubledSextuplePattern C P₀ Q
        = ∑ Q ∈ C, doubledSextuplePattern C P₀ Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P₀ := fun h => hQ (h.symm ▸ hP₀)
          simp [doubledSextuplePattern, hQP, hQ])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP₀]
    have h2 : ∀ Q ∈ C.erase P₀,
        doubledSextuplePattern C P₀ Q = 1 :=
      fun Q hQ => by
        simp [doubledSextuplePattern,
          (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP₀, hcard]
    have hPP : doubledSextuplePattern C P₀ P₀ = 2 := by
      simp [doubledSextuplePattern]
    rw [hPP]
    decide
  have h2 := (card_six_live_or_private hN hN3
    (doubledSextuplePattern C P₀) hsum
    (by rw [hsupp]; exact hcard)).2
  rw [hsupp] at h2
  rcases h2 with h6 | h6 | h6
  · exact Or.inl (Finset.mem_filter.mpr
      ⟨Finset.mem_univ C, hcard, h6⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr
      ⟨Finset.mem_univ C, hcard, h6⟩))
  · exact Or.inr (Or.inr h6)

/-- **The doubled hexa moment factors at a private
column**, through B7-1's doubled strips. Let
`Q ∈ C` have a site `s` of degree `1` in `C`. For
every `P ∈ C`, the doubled moment at `P` factors
through the erasure of `Q`: at `P = Q` it is
`realMoment 2` times the plain moment on the erased
support (B7-1's `doubledHexaReMoment_strip_doubled`);
at `P ≠ Q` it is `e₁` times the doubled moment on the
erased support (`doubledHexaReMoment_strip_single`). -/
theorem doubledHexaReMoment_factor_of_private
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {Q : LayerColumn N} {s : LayerSite N}
    (hQC : Q ∈ C) (hsQ : s ∈ colSites Q)
    (hdeg : siteDegree C s = 1)
    (P : LayerColumn N) (hPC : P ∈ C) :
    doubledHexaReMoment ρ μG C P u u'
      = if P = Q then
          realMoment ρ μG 2
            * quadReMoment ρ μG (C.erase Q) u u'
        else e1 ρ μG
          * doubledHexaReMoment ρ μG (C.erase Q) P u u' := by
  have hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y :=
    privateSite_forall_of_siteDegree_eq_one hQC hsQ hdeg
  by_cases hPQ : P = Q
  · subst hPQ
    rw [if_pos rfl]
    exact doubledHexaReMoment_strip_doubled (ρ := ρ)
      (μG := μG) hN hN3 hρcont u u' hsQ hpriv
  · rw [if_neg hPQ]
    exact doubledHexaReMoment_strip_single (ρ := ρ)
      (μG := μG) hN hN3 hρcont u u' hPC hQC
      (fun h => hPQ h.symm) hsQ hpriv

/-- **The summed card-6 fibers split over the two
live families and the rest.** Summing the card-6
fiber (the filtered `piAntidiag` sum of
`fiber_card_six7`) over all 6-supports: the total is
the `C₆` family sum plus the `Θ(2,2,2)` family sum
plus the sum over the remaining 6-supports. Pure
finset algebra: both families sit inside
`powersetCard 6 univ` (their members have card `6`)
and they are disjoint (their site-supports have
card `6` resp. `5`). -/
theorem card_six_fiber_split (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.powersetCard 6 Finset.univ,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
              (fun k => multSupport k = C),
            ((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ C ∈ c6Supports,
          ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
                (fun k => multSupport k = C),
              ((Nat.multinomial Finset.univ k : ℝ))
                * ∫ α : LayerSite N → G,
                    ∏ P ∈ Finset.univ,
                      (colDensC ρ u u' P α) ^ (k P)
                    ∂(Measure.pi fun _ : LayerSite N => μG)
        + (∑ C ∈ thetaSupports,
            ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
                  (fun k => multSupport k = C),
                ((Nat.multinomial Finset.univ k : ℝ))
                  * ∫ α : LayerSite N → G,
                      ∏ P ∈ Finset.univ,
                        (colDensC ρ u u' P α) ^ (k P)
                      ∂(Measure.pi fun _ : LayerSite N
                        => μG)
          + ∑ C ∈ (Finset.powersetCard 6 Finset.univ
                \ c6Supports) \ thetaSupports,
              ∑ k ∈ (Finset.piAntidiag Finset.univ
                    7).filter
                    (fun k => multSupport k = C),
                  ((Nat.multinomial Finset.univ k : ℝ))
                    * ∫ α : LayerSite N → G,
                        ∏ P ∈ Finset.univ,
                          (colDensC ρ u u' P α) ^ (k P)
                        ∂(Measure.pi fun _ : LayerSite N
                          => μG)) := by
  classical
  have hc6sub : c6Supports (N := N)
      ⊆ Finset.powersetCard 6 Finset.univ := by
    intro S hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S,
        card_eq_six_of_mem_c6Supports hS⟩
  have hthetasub : thetaSupports (N := N)
      ⊆ Finset.powersetCard 6 Finset.univ := by
    intro S hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S,
        card_eq_six_of_mem_thetaSupports hS⟩
  have hdisj : Disjoint (c6Supports (N := N))
      (thetaSupports (N := N)) := by
    refine Finset.disjoint_left.mpr fun S hSc hSt => ?_
    have h6 : (quadSupport S).card = 6 :=
      (hasSixPatternC6_of_mem_c6Supports hSc).1
    have h5 : (quadSupport S).card = 5 :=
      (hasSixPatternTheta_of_mem_thetaSupports hSt).1
    omega
  have htsub : thetaSupports (N := N)
      ⊆ (Finset.powersetCard 6 Finset.univ)
        \ c6Supports (N := N) :=
    Finset.subset_sdiff.mpr ⟨hthetasub, hdisj.symm⟩
  have e1 : ∑ C ∈ Finset.powersetCard 6 Finset.univ,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
              (fun k => multSupport k = C),
            ((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ C ∈ c6Supports (N := N),
          ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
                (fun k => multSupport k = C),
              ((Nat.multinomial Finset.univ k : ℝ))
                * ∫ α : LayerSite N → G,
                    ∏ P ∈ Finset.univ,
                      (colDensC ρ u u' P α) ^ (k P)
                    ∂(Measure.pi fun _ : LayerSite N => μG)
        + ∑ C ∈ (Finset.powersetCard 6 Finset.univ)
              \ c6Supports,
            ∑ k ∈ (Finset.piAntidiag Finset.univ
                  7).filter
                  (fun k => multSupport k = C),
                ((Nat.multinomial Finset.univ k : ℝ))
                  * ∫ α : LayerSite N → G,
                      ∏ P ∈ Finset.univ,
                        (colDensC ρ u u' P α) ^ (k P)
                      ∂(Measure.pi fun _ : LayerSite N
                        => μG) := by
    rw [← Finset.sum_sdiff hc6sub, add_comm]
  have e2 : ∑ C ∈ (Finset.powersetCard 6 Finset.univ)
        \ c6Supports,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
              (fun k => multSupport k = C),
            ((Nat.multinomial Finset.univ k : ℝ))
              * ∫ α : LayerSite N → G,
                  ∏ P ∈ Finset.univ,
                    (colDensC ρ u u' P α) ^ (k P)
                  ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ C ∈ thetaSupports (N := N),
          ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
                (fun k => multSupport k = C),
              ((Nat.multinomial Finset.univ k : ℝ))
                * ∫ α : LayerSite N → G,
                    ∏ P ∈ Finset.univ,
                      (colDensC ρ u u' P α) ^ (k P)
                    ∂(Measure.pi fun _ : LayerSite N => μG)
        + ∑ C ∈ ((Finset.powersetCard 6 Finset.univ)
              \ c6Supports) \ thetaSupports,
            ∑ k ∈ (Finset.piAntidiag Finset.univ
                  7).filter
                  (fun k => multSupport k = C),
                ((Nat.multinomial Finset.univ k : ℝ))
                  * ∫ α : LayerSite N → G,
                      ∏ P ∈ Finset.univ,
                        (colDensC ρ u u' P α) ^ (k P)
                      ∂(Measure.pi fun _ : LayerSite N
                        => μG) := by
    rw [← Finset.sum_sdiff htsub, add_comm]
  rw [e1, e2]

/-- **B7-0 settlement, card 6, family-split part: the
claim is SETTLED in the predicted direction.** The
summed card-6 fibers split as the `C₆` family sum,
the `Θ(2,2,2)` family sum, and the rest
(`card_six_fiber_split`); the trichotomy
(`card_six_support_live_or_private`) says the two
families are exactly the live supports; and on every
remaining 6-support there is a private column at
which the doubled top moment factors by erasure
(`doubledHexaReMoment_factor_of_private`, via B7-1's
doubled strips) — the clause recorded here. The rest
therefore factors by private-column erasure; the two
named families are the live card-6 channels. No sign
is asserted for any family sum: the β⁷ general sign
is FRONTIER, and the dressing/excess conversion of
the fiber values is B7-2b-iv/v work. -/
theorem card_six_family_split_settlement (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∀ C ∈ (Finset.powersetCard 6 Finset.univ \ c6Supports)
        \ thetaSupports,
      ∃ Q ∈ C, ∃ s ∈ colSites Q, siteDegree C s = 1
        ∧ ∀ P ∈ C, doubledHexaReMoment ρ μG C P u u'
          = if P = Q then
              realMoment ρ μG 2
                * quadReMoment ρ μG (C.erase Q) u u'
            else e1 ρ μG
              * doubledHexaReMoment ρ μG (C.erase Q) P
                u u' := by
  intro C hC
  have hCA : C ∈ Finset.powersetCard 6 Finset.univ :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hC).1).1
  have hnotc6 : C ∉ c6Supports :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hC).1).2
  have hnottheta : C ∉ thetaSupports :=
    (Finset.mem_sdiff.mp hC).2
  rcases card_six_support_live_or_private hN hN3 hCA
    with h | h | h
  · exact absurd h hnotc6
  · exact absurd h hnottheta
  · obtain ⟨Q, hQC, s, hsQ, hdeg⟩ := h
    exact ⟨Q, hQC, s, hsQ, hdeg, fun P hPC =>
      doubledHexaReMoment_factor_of_private (ρ := ρ)
        (μG := μG) hN hN3 hρcont u u' hQC hsQ hdeg P hPC⟩

/-! ## B7-2b-iii: B7-2a's ADJ/OPP counting sums are
constant — evaluation -/

/-- **The partner at a degree-2 site.** If `P ∈ C`
reads a site `s` of `siteDegree C s = 2`, there is a
unique other column of `C` through `s`: the filter
defining the degree is a two-element set containing
`P`. -/
theorem exists_partner_of_siteDegree_two
    {C : Finset (LayerColumn N)}
    {P : LayerColumn N} {s : LayerSite N}
    (hPC : P ∈ C) (hsP : s ∈ colSites P)
    (hdeg : siteDegree C s = 2) :
    ∃ A, A ∈ C ∧ A ≠ P ∧ s ∈ colSites A
      ∧ ∀ Q ∈ C, s ∈ colSites Q → Q = P ∨ Q = A := by
  classical
  have hPf : P ∈ C.filter (fun Q => s ∈ colSites Q) :=
    Finset.mem_filter.mpr ⟨hPC, hsP⟩
  obtain ⟨a, b, hab, hfab⟩ :=
    Finset.card_eq_two.mp hdeg
  have haF : a ∈ C.filter (fun Q => s ∈ colSites Q) := by
    rw [hfab]
    exact Finset.mem_insert_self a {b}
  have hbF : b ∈ C.filter (fun Q => s ∈ colSites Q) := by
    rw [hfab]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self b))
  rw [hfab] at hPf
  rcases Finset.mem_insert.mp hPf with hPa | hPb
  · refine ⟨b, (Finset.mem_filter.mp hbF).1, ?_,
      (Finset.mem_filter.mp hbF).2, ?_⟩
    · exact fun h => hab (hPa.symm.trans h.symm)
    · intro Q hQC hsQ
      have hQf : Q ∈ C.filter
          (fun Q => s ∈ colSites Q) :=
        Finset.mem_filter.mpr ⟨hQC, hsQ⟩
      rw [hfab] at hQf
      rcases Finset.mem_insert.mp hQf with h | h
      · exact Or.inl (h.trans hPa.symm)
      · exact Or.inr (Finset.mem_singleton.mp h)
  · have hPb2 : P = b :=
      Finset.mem_singleton.mp hPb
    refine ⟨a, (Finset.mem_filter.mp haF).1, ?_,
      (Finset.mem_filter.mp haF).2, ?_⟩
    · exact fun h => hab (h.trans hPb2)
    · intro Q hQC hsQ
      have hQf : Q ∈ C.filter
          (fun Q => s ∈ colSites Q) :=
        Finset.mem_filter.mpr ⟨hQC, hsQ⟩
      rw [hfab] at hQf
      rcases Finset.mem_insert.mp hQf with h | h
      · exact Or.inr h
      · exact Or.inl
          ((Finset.mem_singleton.mp h).trans hPb2.symm)

/-- **Adjacent partners in a primitive quad: exactly
two.** For `C ∈ primitiveQuads` and `P ∈ C`, exactly
two columns of `C.erase P` share a site with `P`. By
`primitive_pattern_eq_C4` the quad is a `C₄` pattern:
both sites of `P` have degree `2`, each contributing
one partner; the two partners are distinct, for a
column sharing both sites of `P` would have the same
site pair as `P` and equal `P`
(`colSites_eq_imp`) — there is no digon pair. -/
theorem adjPartnerCount_eq_two (hN : Even N)
    (hN3 : 3 ≤ N) {C : Finset (LayerColumn N)}
    (hCmem : C ∈ primitiveQuads)
    {P : LayerColumn N} (hP : P ∈ C) :
    ((C.erase P).filter
      (fun Q => ColsShareSite P Q)).card = 2 := by
  classical
  have hdeg2 : ∀ s ∈ quadSupport C,
      siteDegree C s = 2 :=
    (primitive_pattern_eq_C4 hN hN3 hCmem).1.1.2
  obtain ⟨s₁, s₂, hs12, hsiteP⟩ :=
    Finset.card_eq_two.mp (card_colSites_two hN P)
  have hs₁P : s₁ ∈ colSites P := by
    rw [hsiteP]
    exact Finset.mem_insert_self s₁ {s₂}
  have hs₂P : s₂ ∈ colSites P := by
    rw [hsiteP]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self s₂))
  obtain ⟨A₁, hA₁C, hA₁P, hs₁A₁, huniq₁⟩ :=
    exists_partner_of_siteDegree_two hP hs₁P
      (hdeg2 s₁ (Finset.mem_biUnion.mpr ⟨P, hP, hs₁P⟩))
  obtain ⟨A₂, hA₂C, hA₂P, hs₂A₂, huniq₂⟩ :=
    exists_partner_of_siteDegree_two hP hs₂P
      (hdeg2 s₂ (Finset.mem_biUnion.mpr ⟨P, hP, hs₂P⟩))
  have hA12 : A₁ ≠ A₂ := by
    intro h
    have hsub : colSites P ⊆ colSites A₁ := by
      rw [hsiteP]
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hs₁A₁
      · rw [Finset.mem_singleton] at hs
        rw [hs, h]
        exact hs₂A₂
    have heq : colSites A₁ = colSites P :=
      (Finset.eq_of_subset_of_card_le hsub
        (by rw [card_colSites_two hN A₁,
          card_colSites_two hN P])).symm
    exact hA₁P (colSites_eq_imp hN hN3 heq)
  have hfilt : (C.erase P).filter
        (fun Q => ColsShareSite P Q) = {A₁, A₂} := by
    refine Finset.ext fun Q => ?_
    constructor
    · intro h
      have hmem := Finset.mem_filter.mp h
      obtain ⟨hQP, hQC⟩ := Finset.mem_erase.mp hmem.1
      obtain ⟨s, hsP, hsQ⟩ := hmem.2
      rw [hsiteP] at hsP
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases Finset.mem_insert.mp hsP with hs | hs
      · rcases huniq₁ Q hQC (hs ▸ hsQ) with h | h
        · exact absurd h hQP
        · exact Or.inl h
      · rw [Finset.mem_singleton] at hs
        rcases huniq₂ Q hQC (hs ▸ hsQ) with h | h
        · exact absurd h hQP
        · exact Or.inr h
    · intro h
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hA₁P, hA₁C⟩,
            ⟨s₁, hs₁P, hs₁A₁⟩⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hA₂P, hA₂C⟩,
            ⟨s₂, hs₂P, hs₂A₂⟩⟩
  rw [hfilt, Finset.card_insert_of_notMem
    (by simp [hA12]), Finset.card_singleton]

/-- **Opposite partners in a primitive quad: exactly
one.** `C.erase P` has three columns; the
share/disjoint dichotomy
(`colsDisjointSites_iff_not_share`) splits them into
the two adjacent partners and the rest. -/
theorem oppPartnerCount_eq_one (hN : Even N)
    (hN3 : 3 ≤ N) {C : Finset (LayerColumn N)}
    (hCmem : C ∈ primitiveQuads)
    {P : LayerColumn N} (hP : P ∈ C) :
    ((C.erase P).filter
      (fun Q => ColsDisjointSites P Q)).card = 1 := by
  classical
  have hcard : C.card = 4 :=
    (isPrimitiveQuad_of_mem hCmem).1
  have herase : (C.erase P).card = 3 := by
    rw [Finset.card_erase_of_mem hP, hcard]
  have hfilteq : (C.erase P).filter
        (fun Q => ¬ ColsShareSite P Q)
      = (C.erase P).filter
        (fun Q => ColsDisjointSites P Q) :=
    Finset.filter_congr fun Q _ =>
      (colsDisjointSites_iff_not_share P Q).symm
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := C.erase P) (fun Q => ColsShareSite P Q)
  rw [hfilteq, adjPartnerCount_eq_two hN hN3 hCmem hP,
    herase] at hsplit
  omega

/-- **B7-2a's adjacent counting sum EVALUATED.** The
per-quad adjacent count is constant (`2` per column,
`8` per quad), so `kappa7adjPairCount` is `8` times
the number of primitive quads. (At general `(G, ρ)`:
the count is representation-independent combinatorics
at even `N ≥ 3`.) -/
theorem kappa7adjPairCount_eq (hN : Even N)
    (hN3 : 3 ≤ N) :
    kappa7adjPairCount (N := N)
      = 8 * ((primitiveQuads (N := N)).card : ℝ) := by
  classical
  unfold kappa7adjPairCount
  calc ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
          (((C.erase P).filter
            (fun Q => ColsShareSite P Q)).card : ℝ)
      = ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C, (2 : ℝ) := by
        refine Finset.sum_congr rfl fun C hC =>
          Finset.sum_congr rfl fun P hP => ?_
        rw [adjPartnerCount_eq_two hN hN3 hC hP]
        norm_num
    _ = ∑ C ∈ primitiveQuads (N := N), (8 : ℝ) := by
        refine Finset.sum_congr rfl fun C hC => ?_
        rw [Finset.sum_const, (isPrimitiveQuad_of_mem hC).1,
          nsmul_eq_mul]
        norm_num
    _ = 8 * ((primitiveQuads (N := N)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **B7-2a's opposite counting sum EVALUATED.** The
per-quad opposite count is constant (`1` per column,
`4` per quad), so `kappa7oppPairCount` is `4` times
the number of primitive quads. -/
theorem kappa7oppPairCount_eq (hN : Even N)
    (hN3 : 3 ≤ N) :
    kappa7oppPairCount (N := N)
      = 4 * ((primitiveQuads (N := N)).card : ℝ) := by
  classical
  unfold kappa7oppPairCount
  calc ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
          (((C.erase P).filter
            (fun Q => ColsDisjointSites P Q)).card : ℝ)
      = ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun C hC =>
          Finset.sum_congr rfl fun P hP => ?_
        rw [oppPartnerCount_eq_one hN hN3 hC hP]
        norm_num
    _ = ∑ C ∈ primitiveQuads (N := N), (4 : ℝ) := by
        refine Finset.sum_congr rfl fun C hC => ?_
        rw [Finset.sum_const, (isPrimitiveQuad_of_mem hC).1,
          nsmul_eq_mul]
        norm_num
    _ = 4 * ((primitiveQuads (N := N)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ## B7-2b-iii close

This section (B7-2b-iii) owns: the card-5 and card-4
fiber decompositions per pattern, in engine form
(`fiber_card_five7`, `fiber_card_four7`); the two
B7-0 settlements at full rank — card 5 CONFIRMED
erased (`card_five_erasure_settlement`), card 6
family-split SETTLED with the two named families live
and the rest factoring by private-column erasure
(`card_six_fiber_split`,
`card_six_support_live_or_private`,
`card_six_family_split_settlement`); and the
evaluation of B7-2a's ADJ/OPP counting sums, proved
CONSTANT (`kappa7adjPairCount_eq`:
`8 · |primitiveQuads|`; `kappa7oppPairCount_eq`:
`4 · |primitiveQuads|`). Seams, named: the pattern
values stand in binomial/engine form — their
conversion into dressing-plus-excess form, the
assembly of the total decomposition, and
`kappa7dep_eq` are B7-2b-iv/v, not this brick. No
sign is asserted for any fiber or family sum. -/

end Fiber7c


/-! ## B7-2b-iv: the total decomposition at order 7

This section (B7-2b-iv) sums the landed fiber accounting
(B7-2b-i/ii/iii: the fibers over cards `1`–`7`, both
B7-0 settlements, and the evaluated ADJ/OPP counts
`kappa7adjPairCount_eq` / `kappa7oppPairCount_eq`, which
evaluate the split `(3,2,1,1)` baselines to `8` and `4`
per primitive quad) into the total decomposition of
`kappa7dep`: dressings of `kappa4dep`, `kappa5dep` and
`kappa6dep` with coefficients read off the fibers,
plus the seven B7-2a channel excesses, plus the
residual terms the accounting forces (named on the
face of the closing identity, not hidden). The
variable context is exactly B7-1's: general `(G, ρ)`
in the β-line's section context (no irreducibility),
the fiber evaluations carrying `Even N`, `3 ≤ N` and
continuity of `g ↦ repMatrix ρ g`. NO CLAIM; parts of
the Clay Yang–Mills statement closed by this section:
0; dials 0/4; no sign is asserted for `kappa7dep` or
for any excess or residual: the β⁷ general sign is
FRONTIER.

The engine pattern values of B7-2b-iii (cards `4` and
`5`) are converted here by one generic step: a density
pattern value is its fully-split baseline (a product
of `densMomentValue`s) plus a sum, over the exponent
choices whose support has card at least `4`, of the
binomial coefficient times the excess of the
generalized character moment over its factored value
(on supports of card at most `3` the generalized
moment factors, by
`integral_colRe_prod_pow_card_le_three7`, so exactly
the card-`≥ 4` choices survive). -/

section Total7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- `densMomentValue 0 = 1`: the empty binomial sum. -/
theorem densMomentValue_zero : densMomentValue ρ μG 0 = 1 := by
  unfold densMomentValue
  simp [realMoment_zero]

/-- **The generic pattern-value conversion.** A density
pattern value (exponent function `k` supported on `C`)
is its fully-split baseline `∏_{P ∈ C} A_{k P}` plus
the sum, over exponent choices `j ≤ k` whose support
inside `C` has card at least `4`, of the binomial
coefficient times the excess of the generalized
character moment `colReMomentPow C j` over its
factored value `∏_{P ∈ C} μ_{j P}`. -/
theorem patternValue_eq_baseline_add_top (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (k : LayerColumn N → ℕ) (hk : ∀ P ∉ C, k P = 0) :
    ∫ α : LayerSite N → G,
        ∏ P ∈ C, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (∏ P ∈ C, densMomentValue ρ μG (k P))
        + ∑ j ∈ (Fintype.piFinset
              (fun P => Finset.range (k P + 1))).filter
            (fun j => 4 ≤ (C.filter (fun P => j P ≠ 0)).card),
          (∏ P ∈ C, ((k P).choose (j P) : ℝ)
              * (-(d : ℝ)⁻¹) ^ (j P))
            * (colReMomentPow ρ μG C j u u'
              - ∏ P ∈ C, realMoment ρ μG (j P)) := by
  classical
  have hsmall : ∀ j ∈ Fintype.piFinset
        (fun P => Finset.range (k P + 1)),
      (C.filter (fun P => j P ≠ 0)).card ≤ 3 →
      colReMomentPow ρ μG C j u u'
        = ∏ P ∈ C, realMoment ρ μG (j P) := by
    intro j _ hcard
    rw [colReMomentPow_support_reduce]
    show colReMomentPow ρ μG (C.filter (fun Q => j Q ≠ 0)) j u u'
      = ∏ P ∈ C, realMoment ρ μG (j P)
    unfold colReMomentPow
    rw [integral_colRe_prod_pow_card_le_three7 ρ μG hN hN3
      hρcont u u' _ hcard j]
    refine Finset.prod_subset (Finset.filter_subset _ C)
      (fun P hPC hP => ?_)
    have hjP : j P = 0 := by
      by_contra hne
      exact hP (Finset.mem_filter.mpr ⟨hPC, hne⟩)
    rw [hjP, realMoment_zero]
  have hsumF : ∑ j ∈ Fintype.piFinset
        (fun P => Finset.range (k P + 1)),
        (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
          * ∏ P ∈ C, realMoment ρ μG (j P)
      = ∏ P ∈ C, densMomentValue ρ μG (k P) := by
    have hterm : ∀ j ∈ Fintype.piFinset
          (fun P => Finset.range (k P + 1)),
        (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
          * ∏ P ∈ C, realMoment ρ μG (j P)
        = ∏ P ∈ Finset.univ, (((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P) * realMoment ρ μG (j P)) := by
      intro j hj
      have hj0 : ∀ P ∉ C, j P = 0 := by
        intro P hP
        have hmem := Fintype.mem_piFinset.mp hj P
        rw [hk P hP] at hmem
        have hlt : j P < 1 := Finset.mem_range.mp hmem
        omega
      have hpm : (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
          * ∏ P ∈ C, realMoment ρ μG (j P)
        = ∏ P ∈ C, (((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P) * realMoment ρ μG (j P)) :=
        Finset.prod_mul_distrib.symm
      rw [hpm]
      refine Finset.prod_subset (Finset.subset_univ C)
        (fun P _ hP => ?_)
      rw [hj0 P hP, hk P hP]
      norm_num [realMoment_zero]
    have hprod : (∏ P, densMomentValue ρ μG (k P))
        = ∑ j ∈ Fintype.piFinset
            (fun P => Finset.range (k P + 1)),
          ∏ P, (((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P) * realMoment ρ μG (j P)) :=
      Finset.prod_univ_sum (fun P => Finset.range (k P + 1))
        (fun P a => ((k P).choose a : ℝ) * (-(d : ℝ)⁻¹) ^ a
          * realMoment ρ μG a)
    rw [Finset.sum_congr rfl hterm, ← hprod]
    refine (Finset.prod_subset (Finset.subset_univ C)
      (fun P _ hP => ?_)).symm
    rw [hk P hP, densMomentValue_zero]
  rw [integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C k hk]
  have hsplit : ∀ j ∈ Fintype.piFinset
        (fun P => Finset.range (k P + 1)),
      (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        * colReMomentPow ρ μG C j u u'
      = (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
          * ∏ P ∈ C, realMoment ρ μG (j P)
        + (∏ P ∈ C, ((k P).choose (j P) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j P))
          * (colReMomentPow ρ μG C j u u'
            - ∏ P ∈ C, realMoment ρ μG (j P)) :=
    fun j _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hsumF]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases htop : 4 ≤ (C.filter (fun P => j P ≠ 0)).card
  · rw [if_pos htop]
  · rw [if_neg htop, hsmall j hj (by omega), sub_self, mul_zero]

/-- Generalized character moments depend only on the
values of the exponent function on the support. -/
theorem colReMomentPow_congr_on {C : Finset (LayerColumn N)}
    {a b : LayerColumn N → ℕ} (h : ∀ P ∈ C, a P = b P)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C a u u'
      = colReMomentPow ρ μG C b u u' := by
  unfold colReMomentPow
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  exact Finset.prod_congr rfl fun P hP => by rw [h P hP]

/-- The generalized moment at the `(2,1,…,1)` pattern
on `C` is the doubled quad moment at `P` (any support
size: the moment construction is support-size blind). -/
theorem colReMomentPow_eq_doubledQuadReMoment
    (C : Finset (LayerColumn N)) {P : LayerColumn N}
    (hP : P ∈ C) (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (fun Q => if Q = P then 2 else 1) u u'
      = doubledQuadReMoment ρ μG C P u u' := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ Q ∈ C, (colRe ρ u u' Q α)
      ^ (if Q = P then 2 else 1)
    = (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C
    (fun Q => (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1)) hP]
  refine congrArg₂ _ ?_ ?_
  · simp
  · refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    simp [hQP]

/-- The generalized moment at the `(3,1,…,1)` pattern
on `C` is the tripled quad moment at `P`. -/
theorem colReMomentPow_eq_tripledQuadReMoment
    (C : Finset (LayerColumn N)) {P : LayerColumn N}
    (hP : P ∈ C) (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (fun Q => if Q = P then 3 else 1) u u'
      = tripledQuadReMoment ρ μG C P u u' := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ Q ∈ C, (colRe ρ u u' Q α)
      ^ (if Q = P then 3 else 1)
    = (colRe ρ u u' P α) ^ 3
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C
    (fun Q => (colRe ρ u u' Q α) ^ (if Q = P then 3 else 1)) hP]
  refine congrArg₂ _ ?_ ?_
  · simp
  · refine Finset.prod_congr rfl fun Q hQ => ?_
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    simp [hQP]

/-- The generalized moment at the `(2,2,1,…,1)` pattern
on `C` is the doubled-doubled quad moment at `(P, Q)`. -/
theorem colReMomentPow_eq_doubledDoubledQuadReMoment
    (C : Finset (LayerColumn N)) {P Q : LayerColumn N}
    (hP : P ∈ C) (hQ : Q ∈ C) (hQP : Q ≠ P)
    (u u' : LayerLink N → G) :
    colReMomentPow ρ μG C
        (fun R => if R = P then 2 else if R = Q then 2 else 1)
        u u'
      = doubledDoubledQuadReMoment ρ μG C P Q u u' := by
  have hQmem : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQ⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show ∏ R ∈ C, (colRe ρ u u' R α)
      ^ (if R = P then 2 else if R = Q then 2 else 1)
    = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
  rw [← Finset.mul_prod_erase C
      (fun R => (colRe ρ u u' R α)
        ^ (if R = P then 2 else if R = Q then 2 else 1)) hP,
    ← Finset.mul_prod_erase (C.erase P)
      (fun R => (colRe ρ u u' R α)
        ^ (if R = P then 2 else if R = Q then 2 else 1)) hQmem,
    mul_assoc]
  have hP' : (colRe ρ u u' P α)
        ^ (if P = P then 2 else if P = Q then 2 else 1)
      = (colRe ρ u u' P α) ^ 2 := by simp
  have hQ' : (colRe ρ u u' Q α)
        ^ (if Q = P then 2 else if Q = Q then 2 else 1)
      = (colRe ρ u u' Q α) ^ 2 := by simp [hQP]
  have hR' : ∏ R ∈ (C.erase P).erase Q,
        (colRe ρ u u' R α)
          ^ (if R = P then 2 else if R = Q then 2 else 1)
      = ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α :=
    Finset.prod_congr rfl fun R hR => by
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      simp [hRP, hRQ]
  rw [hP', hQ', hR']

/-- The doubled hexa moment is the doubled penta
moment: both are the same integral construction
(support-size blind). -/
theorem doubledHexaReMoment_eq_doubledPentaReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) :
    doubledHexaReMoment ρ μG C P u u'
      = doubledPentaReMoment ρ μG C P u u' :=
  rfl


/-- Sum over `Icc 1 2`, expanded. -/
theorem sum_Icc_one_two (f : ℕ → ℝ) :
    ∑ a ∈ Finset.Icc 1 2, f a = f 1 + f 2 := by
  rw [show Finset.Icc 1 2 = {1, 2} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Sum over `Icc 1 3`, expanded. -/
theorem sum_Icc_one_three (f : ℕ → ℝ) :
    ∑ a ∈ Finset.Icc 1 3, f a = f 1 + f 2 + f 3 := by
  rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Sum over `Icc 1 4`, expanded. -/
theorem sum_Icc_one_four (f : ℕ → ℝ) :
    ∑ a ∈ Finset.Icc 1 4, f a = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **The `(4,1,1,1)` pattern value.** For a 4-support
`C` and `P ∈ C`, the quadrupled pattern value is its
baseline `A₄B³` plus the order-4 excess of `C` at
weight `4·d⁻⁴`, the doubled excess at `P` at weight
`−6·d⁻⁵`, the tripled excess at `P` at weight
`4·d⁻⁶`, and the quadrupled excess at `P` at weight
`−d⁻⁷` (a summand of B7-2a's `kappa7chan4111Excess`).
By the generic conversion
(`patternValue_eq_baseline_add_top`): the surviving
exponent choices are `(a,1,1,1)`, `a = 1,2,3,4`, with
binomial coefficients `4, 6, 4, 1` at weights
`c^{a+3}`. -/
theorem patternValue4111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α)
          ^ (quadrupledQuadPattern7 C P Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3) := by
  classical
  have hk0 : ∀ Q ∉ C, quadrupledQuadPattern7 C P Q = 0 := by
    intro Q hQ
    have hQP : Q ≠ P := fun h => hQ (h ▸ hP)
    simp [quadrupledQuadPattern7, hQP, hQ]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u'
    C _ hk0]
  -- the baseline product
  have hbase : (∏ Q ∈ C, densMomentValue ρ μG
        (quadrupledQuadPattern7 C P Q))
      = densMomentValue ρ μG 4
        * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    rw [← Finset.mul_prod_erase C _ hP]
    have hPP : quadrupledQuadPattern7 C P P = 4 := by
      simp [quadrupledQuadPattern7]
    have hrest : ∀ Q ∈ C.erase P,
        densMomentValue ρ μG (quadrupledQuadPattern7 C P Q)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro Q hQ
      have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
      have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
      have hval : quadrupledQuadPattern7 C P Q = 1 := by
        simp [quadrupledQuadPattern7, hQP, hQC]
      rw [hval]
      exact densMomentValue_one ρ μG
    rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hP, hC,
      show (4 - 1 : ℕ) = 3 from rfl]
  rw [hbase]
  -- the top sum, evaluated by the bijection `a ↦ (a,1,1,1)`
  set g : ℕ → LayerColumn N → ℕ :=
    fun a Q => if Q = P then a else if Q ∈ C then 1 else 0
    with hg
  have hmem : ∀ a ∈ Finset.Icc 1 4, g a
      ∈ (Fintype.piFinset (fun Q => Finset.range
          (quadrupledQuadPattern7 C P Q + 1))).filter
        (fun j => 4 ≤ (C.filter (fun Q => j Q ≠ 0)).card) := by
    intro a ha
    have ha14 : 1 ≤ a ∧ a ≤ 4 := Finset.mem_Icc.mp ha
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro Q
      rw [Finset.mem_range]
      by_cases hQP : Q = P
      · rw [hQP]
        have hpat : quadrupledQuadPattern7 C P P = 4 := by
          simp [quadrupledQuadPattern7]
        rw [hpat]
        show g a P < 4 + 1
        simp only [hg, if_true]
        omega
      · by_cases hQC : Q ∈ C
        · have hpat : quadrupledQuadPattern7 C P Q = 1 := by
            simp [quadrupledQuadPattern7, hQP, hQC]
          rw [hpat]
          show g a Q < 1 + 1
          simp only [hg, hQP, hQC, if_false, if_true]
          omega
        · have hpat : quadrupledQuadPattern7 C P Q = 0 :=
            hk0 Q hQC
          rw [hpat]
          show g a Q < 0 + 1
          simp only [hg, hQP, hQC, if_false, if_true]
          omega
    · have hfilt : C.filter (fun Q => g a Q ≠ 0) = C := by
        refine Finset.filter_true_of_mem fun Q hQC => ?_
        by_cases hQP : Q = P
        · rw [hQP]
          simp only [hg, if_true]
          omega
        · simp only [hg, hQP, hQC, if_false, if_true]
          norm_num
      rw [hfilt, hC]
  have hinj : ∀ a₁ ∈ Finset.Icc 1 4, ∀ a₂ ∈ Finset.Icc 1 4,
      g a₁ = g a₂ → a₁ = a₂ := by
    intro a₁ _ a₂ _ h
    have h1 : g a₁ P = a₁ := by simp only [hg, if_true]
    have h2 : g a₂ P = a₂ := by simp only [hg, if_true]
    rw [← h1, ← h2, h]
  have hsurj : ∀ j ∈ (Fintype.piFinset (fun Q => Finset.range
          (quadrupledQuadPattern7 C P Q + 1))).filter
        (fun j => 4 ≤ (C.filter (fun Q => j Q ≠ 0)).card),
      ∃ a, ∃ _ : a ∈ Finset.Icc 1 4, g a = j := by
    intro j hj
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hj
    obtain ⟨hjpi, hjcard⟩ := hj
    have hsub : C.filter (fun Q => j Q ≠ 0) ⊆ C :=
      Finset.filter_subset _ _
    have hcardle : (C.filter (fun Q => j Q ≠ 0)).card ≤ 4 := by
      rw [← hC]
      exact Finset.card_le_card hsub
    have hfiltereq : C.filter (fun Q => j Q ≠ 0) = C :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hjne : ∀ Q ∈ C, j Q ≠ 0 := by
      intro Q hQC
      have : Q ∈ C.filter (fun Q => j Q ≠ 0) := by
        rw [hfiltereq]; exact hQC
      exact (Finset.mem_filter.mp this).2
    have hjP : j P ∈ Finset.Icc 1 4 := by
      rw [Finset.mem_Icc]
      have hlt := hjpi P
      rw [Finset.mem_range] at hlt
      have hpat : quadrupledQuadPattern7 C P P = 4 := by
        simp [quadrupledQuadPattern7]
      rw [hpat] at hlt
      exact ⟨Nat.pos_of_ne_zero (hjne P hP), by omega⟩
    refine ⟨j P, hjP, ?_⟩
    funext Q
    by_cases hQP : Q = P
    · rw [hQP]
      simp only [hg, if_true]
    · by_cases hQC : Q ∈ C
      · have hlt := hjpi Q
        rw [Finset.mem_range] at hlt
        have hpat : quadrupledQuadPattern7 C P Q = 1 := by
          simp [quadrupledQuadPattern7, hQP, hQC]
        rw [hpat] at hlt
        have hjQ : j Q = 1 := by
          have hne := hjne Q hQC
          omega
        simp only [hg, hQP, hQC, if_false, if_true, hjQ]
      · have hlt := hjpi Q
        rw [Finset.mem_range] at hlt
        have hpat : quadrupledQuadPattern7 C P Q = 0 := hk0 Q hQC
        rw [hpat] at hlt
        have hjQ : j Q = 0 := by omega
        simp only [hg, hQP, hQC, if_false, if_true, hjQ]
  have htop : (∑ j ∈ (Fintype.piFinset (fun Q => Finset.range
          (quadrupledQuadPattern7 C P Q + 1))).filter
        (fun j => 4 ≤ (C.filter (fun Q => j Q ≠ 0)).card),
      (∏ Q ∈ C, ((quadrupledQuadPattern7 C P Q).choose
          (j Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (j Q))
        * (colReMomentPow ρ μG C j u u'
          - ∏ Q ∈ C, realMoment ρ μG (j Q)))
    = ∑ a ∈ Finset.Icc 1 4,
      (∏ Q ∈ C, ((quadrupledQuadPattern7 C P Q).choose
          (g a Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a Q))
        * (colReMomentPow ρ μG C (g a) u u'
          - ∏ Q ∈ C, realMoment ρ μG (g a Q)) :=
    (Finset.sum_bij (fun a _ => g a) hmem hinj hsurj
      (fun a _ => rfl)).symm
  rw [htop, sum_Icc_one_four]
  -- evaluate the four terms
  have hcoeff : ∀ a : ℕ, ∀ ha : a ≤ 4,
      (∏ Q ∈ C, ((quadrupledQuadPattern7 C P Q).choose
          (g a Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a Q))
        = ((Nat.choose 4 a : ℝ)) * (-(d : ℝ)⁻¹) ^ (a + 3) := by
    intro a _
    rw [← Finset.mul_prod_erase C _ hP]
    have hPP : (quadrupledQuadPattern7 C P P).choose (g a P)
          * (-(d : ℝ)⁻¹) ^ (g a P)
        = ((Nat.choose 4 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a := by
      have hpat : quadrupledQuadPattern7 C P P = 4 := by
        simp [quadrupledQuadPattern7]
      have hgP : g a P = a := by simp only [hg, if_true]
      rw [hpat, hgP]
    have hrest : ∀ Q ∈ C.erase P,
        ((quadrupledQuadPattern7 C P Q).choose (g a Q) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (g a Q) = (-(d : ℝ)⁻¹) := by
      intro Q hQ
      have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
      have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
      have hpat : quadrupledQuadPattern7 C P Q = 1 := by
        simp [quadrupledQuadPattern7, hQP, hQC]
      have hgQ : g a Q = 1 := by
        simp only [hg, hQP, hQC, if_false, if_true]
      rw [hpat, hgQ]
      norm_num
    rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hP, hC,
      show (4 - 1 : ℕ) = 3 from rfl, mul_assoc, ← pow_add]
  have hF : ∀ a : ℕ,
      ∏ Q ∈ C, realMoment ρ μG (g a Q)
        = realMoment ρ μG a * (e1 ρ μG) ^ 3 := by
    intro a
    rw [← Finset.mul_prod_erase C _ hP]
    have hgP : g a P = a := by simp only [hg, if_true]
    have hrest : ∀ Q ∈ C.erase P, realMoment ρ μG (g a Q)
        = e1 ρ μG := by
      intro Q hQ
      have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
      have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
      have hgQ : g a Q = 1 := by
        simp only [hg, hQP, hQC, if_false, if_true]
      rw [hgQ, realMoment_one]
    rw [hgP, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hP, hC,
      show (4 - 1 : ℕ) = 3 from rfl]
  have hM1 : colReMomentPow ρ μG C (g 1) u u'
      = quadReMoment ρ μG C u u' := by
    have hcong : ∀ Q ∈ C, g 1 Q = (fun _ => 1) Q := by
      intro Q hQC
      by_cases hQP : Q = P
      · rw [hQP]
        simp only [hg, if_true]
      · simp only [hg, hQP, hQC, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_one]
  have hM2 : colReMomentPow ρ μG C (g 2) u u'
      = doubledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ Q ∈ C, g 2 Q
        = (fun Q => if Q = P then 2 else 1) Q := by
      intro Q hQC
      by_cases hQP : Q = P
      · rw [hQP]
        simp only [hg, if_true]
      · simp only [hg, hQP, hQC, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
  have hM3 : colReMomentPow ρ μG C (g 3) u u'
      = tripledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ Q ∈ C, g 3 Q
        = (fun Q => if Q = P then 3 else 1) Q := by
      intro Q hQC
      by_cases hQP : Q = P
      · rw [hQP]
        simp only [hg, if_true]
      · simp only [hg, hQP, hQC, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_tripledQuadReMoment ρ μG C hP u u']
  have hM4 : colReMomentPow ρ μG C (g 4) u u'
      = quadrupledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ Q ∈ C, g 4 Q
        = quadrupledQuadPattern7 C P Q := by
      intro Q hQC
      by_cases hQP : Q = P
      · rw [hQP]
        simp only [hg, quadrupledQuadPattern7, if_true]
      · simp only [hg, quadrupledQuadPattern7, hQP, hQC,
          if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_quadrupledQuadPattern7 ρ μG C hP u u']
  rw [hcoeff 1 (by norm_num), hcoeff 2 (by norm_num),
    hcoeff 3 (by norm_num), hcoeff 4 (by norm_num),
    hF 1, hF 2, hF 3, hF 4, hM1, hM2, hM3, hM4]
  norm_num [Nat.choose, realMoment_one]
  ring

/-- **Top-sum split at card 5.** The order-7 top sum
(support at least `4` inside a 5-support `C`) splits
into the full-support part and, for each erased column
`x`, the part supported exactly on `C.erase x`. -/
theorem topSum_card5_split (k : LayerColumn N → ℕ)
    (C : Finset (LayerColumn N)) (hC : C.card = 5)
    (u u' : LayerLink N → G) :
    (∑ j ∈ (Fintype.piFinset
        (fun P => Finset.range (k P + 1))).filter
        (fun j => 4 ≤ (C.filter (fun P => j P ≠ 0)).card),
      (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        * (colReMomentPow ρ μG C j u u'
          - ∏ P ∈ C, realMoment ρ μG (j P)))
    = (∑ j ∈ (Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => (C.filter (fun P => j P ≠ 0)) = C),
      (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        * (colReMomentPow ρ μG C j u u'
          - ∏ P ∈ C, realMoment ρ μG (j P)))
    + ∑ x ∈ C, ∑ j ∈ (Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => j x = 0
          ∧ (C.erase x).filter (fun P => j P ≠ 0) = C.erase x),
      (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        * (colReMomentPow ρ μG C j u u'
          - ∏ P ∈ C, realMoment ρ μG (j P)) := by
  classical
  -- a piece's support is exactly the erased support
  have hsupp_of_piece : ∀ (j : LayerColumn N → ℕ)
      (x : LayerColumn N), j x = 0 →
      (C.erase x).filter (fun P => j P ≠ 0) = C.erase x →
      C.filter (fun P => j P ≠ 0) = C.erase x := by
    intro j x hjx0 hfx
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_filter] at hy
      exact Finset.mem_erase.mpr
        ⟨fun hyx => (hyx ▸ hy.2) hjx0, hy.1⟩
    · intro y hy
      have hy2 : y ∈ (C.erase x).filter (fun P => j P ≠ 0) := by
        rw [hfx]; exact hy
      rw [Finset.mem_filter] at hy2
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_erase.mp hy2.1).2, hy2.2⟩
  have hdisjBx : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      Disjoint ((Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => j x = 0
          ∧ (C.erase x).filter (fun P => j P ≠ 0) = C.erase x))
        ((Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => j y = 0
          ∧ (C.erase y).filter (fun P => j P ≠ 0) = C.erase y)) := by
    intro x hxC y hyC hxy
    rw [Finset.disjoint_left]
    intro j hjx hjy
    rw [Finset.mem_filter] at hjx hjy
    have hEq : C.erase x = C.erase y :=
      (hsupp_of_piece j x hjx.2.1 hjx.2.2).symm.trans
        (hsupp_of_piece j y hjy.2.1 hjy.2.2)
    have hxmem : x ∈ C.erase y :=
      Finset.mem_erase.mpr ⟨hxy, hxC⟩
    rw [← hEq] at hxmem
    exact (Finset.mem_erase.mp hxmem).1 rfl
  have hdisjB : Disjoint ((Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => (C.filter (fun P => j P ≠ 0)) = C))
      (C.biUnion (fun x => (Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => j x = 0
          ∧ (C.erase x).filter (fun P => j P ≠ 0)
            = C.erase x))) := by
    rw [Finset.disjoint_left]
    intro j hjB hjU
    rw [Finset.mem_filter] at hjB
    rw [Finset.mem_biUnion] at hjU
    obtain ⟨x, hxC, hjx⟩ := hjU
    rw [Finset.mem_filter] at hjx
    have hxmem : x ∈ C.filter (fun P => j P ≠ 0) := by
      rw [hjB.2]; exact hxC
    rw [Finset.mem_filter] at hxmem
    exact hxmem.2 hjx.2.1
  have hEq : (Fintype.piFinset
        (fun P => Finset.range (k P + 1))).filter
        (fun j => 4 ≤ (C.filter (fun P => j P ≠ 0)).card)
      = ((Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => (C.filter (fun P => j P ≠ 0)) = C))
        ∪ (C.biUnion (fun x => (Fintype.piFinset
          (fun P => Finset.range (k P + 1))).filter
        (fun j => j x = 0
          ∧ (C.erase x).filter (fun P => j P ≠ 0)
            = C.erase x))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_union,
      Finset.mem_biUnion]
    constructor
    · intro hj
      obtain ⟨hjS, hjcard⟩ := hj
      by_cases hfull : (C.filter (fun P => j P ≠ 0)) = C
      · exact Or.inl ⟨hjS, hfull⟩
      · right
        have hsub : C.filter (fun P => j P ≠ 0) ⊆ C :=
          Finset.filter_subset _ _
        have hcardle : (C.filter (fun P => j P ≠ 0)).card ≤ 5 := by
          rw [← hC]; exact Finset.card_le_card hsub
        have hcard4 : (C.filter (fun P => j P ≠ 0)).card = 4 := by
          by_contra hne
          have h5 : (C.filter (fun P => j P ≠ 0)).card = 5 := by
            omega
          exact hfull (Finset.eq_of_subset_of_card_le hsub
            (by omega))
        have hneC : ¬ C ⊆ C.filter (fun P => j P ≠ 0) := by
          intro hsubC
          exact hfull (Finset.Subset.antisymm hsub hsubC)
        obtain ⟨x, hxC, hxnot⟩ := Finset.not_subset.mp hneC
        have hjx0 : j x = 0 := by
          by_contra hne
          exact hxnot (Finset.mem_filter.mpr ⟨hxC, hne⟩)
        have hce : (C.erase x).card = 4 := by
          rw [Finset.card_erase_of_mem hxC, hC]
        have hsupp : C.filter (fun P => j P ≠ 0) = C.erase x := by
          apply Finset.eq_of_subset_of_card_le _ _
          · intro y hy
            rw [Finset.mem_filter] at hy
            exact Finset.mem_erase.mpr
              ⟨fun hyx => (hyx ▸ hy.2) hjx0, hy.1⟩
          · omega
        have hfx : (C.erase x).filter (fun P => j P ≠ 0)
            = C.erase x := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · intro hy; exact ⟨hy.1.1, hy.1.2⟩
          · intro hy
            have hymem : y ∈ C.filter (fun P => j P ≠ 0) := by
              rw [hsupp]; exact Finset.mem_erase.mpr ⟨hy.1, hy.2⟩
            exact ⟨⟨hy.1, hy.2⟩,
              (Finset.mem_filter.mp hymem).2⟩
        exact ⟨x, hxC, hjS, hjx0, hfx⟩
    · intro hj
      rcases hj with ⟨hjS, hfull⟩ | ⟨x, hxC, hjS, hjx0, hfx⟩
      · refine ⟨hjS, ?_⟩
        have hfc : (C.filter (fun P => j P ≠ 0)).card = 5 := by
          rw [hfull, hC]
        omega
      · refine ⟨hjS, ?_⟩
        have hsupp := hsupp_of_piece j x hjx0 hfx
        have hce : (C.erase x).card = 4 := by
          rw [Finset.card_erase_of_mem hxC, hC]
        rw [hsupp]; omega
  rw [hEq, Finset.sum_union hdisjB, Finset.sum_biUnion hdisjBx]

/-- **Piece-to-erased conversion.** A split piece at `x`
is the generic top sum over the erased support for the
pattern zeroed at `x`: same sum, summand rewritten over
`C.erase x` (the `x` factors are `1`, and the moment
reduces by support). -/
theorem pieceSum_eq_topSum_erase (k : LayerColumn N → ℕ)
    (C : Finset (LayerColumn N)) (hC : C.card = 5)
    {x : LayerColumn N} (hx : x ∈ C) (u u' : LayerLink N → G) :
    (∑ j ∈ (Fintype.piFinset
        (fun P => Finset.range (k P + 1))).filter
        (fun j => j x = 0
          ∧ (C.erase x).filter (fun P => j P ≠ 0) = C.erase x),
      (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        * (colReMomentPow ρ μG C j u u'
          - ∏ P ∈ C, realMoment ρ μG (j P)))
    = ∑ j ∈ (Fintype.piFinset (fun P => Finset.range
          ((fun Q => if Q = x then 0 else k Q) P + 1))).filter
        (fun j => 4 ≤ ((C.erase x).filter
          (fun P => j P ≠ 0)).card),
      (∏ P ∈ C.erase x, (((fun Q => if Q = x then 0 else k Q) P).choose
            (j P) : ℝ) * (-(d : ℝ)⁻¹) ^ (j P))
        * (colReMomentPow ρ μG (C.erase x) j u u'
          - ∏ P ∈ C.erase x, realMoment ρ μG (j P)) := by
  classical
  have hCx : (C.erase x).card = 4 := by
    rw [Finset.card_erase_of_mem hx, hC]
  have hsupp : ∀ j : LayerColumn N → ℕ, j x = 0 →
      (C.erase x).filter (fun P => j P ≠ 0) = C.erase x →
      C.filter (fun P => j P ≠ 0) = C.erase x := by
    intro j hjx0 hfx
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_filter] at hy
      exact Finset.mem_erase.mpr
        ⟨fun hyx => (hyx ▸ hy.2) hjx0, hy.1⟩
    · intro y hy
      have hy2 : y ∈ (C.erase x).filter (fun P => j P ≠ 0) := by
        rw [hfx]; exact hy
      rw [Finset.mem_filter] at hy2
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_erase.mp hy2.1).2, hy2.2⟩
  refine Finset.sum_bij (fun j _ => j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hj ⊢
    obtain ⟨hjpi, hjx0, hfx⟩ := hj
    constructor
    · intro P
      have hlt := hjpi P
      rw [Finset.mem_range] at hlt ⊢
      by_cases hPx : P = x
      · subst hPx; rw [hjx0]; simp
      · have hkx : (fun Q => if Q = x then 0 else k Q) P = k P := by
          simp only [if_neg hPx]
        rw [hkx]; exact hlt
    · rw [hfx, hCx]
  · intro j₁ _ j₂ _ h; exact h
  · intro j hj
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hj
    obtain ⟨hjpi, hjcard⟩ := hj
    have hjx0 : j x = 0 := by
      have hmem := hjpi x
      rw [Finset.mem_range] at hmem
      have hx0 : (fun Q => if Q = x then 0 else k Q) x = 0 := by
        simp
      rw [hx0] at hmem; omega
    have hfx : (C.erase x).filter (fun P => j P ≠ 0)
        = C.erase x := by
      apply Finset.eq_of_subset_of_card_le _ _
      · exact Finset.filter_subset _ _
      · rw [hCx]; exact hjcard
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, hjx0, hfx⟩
    intro P
    have hlt := hjpi P
    rw [Finset.mem_range] at hlt ⊢
    have hle : (fun Q => if Q = x then 0 else k Q) P ≤ k P := by
      by_cases hPx : P = x <;> simp [hPx]
    omega
  · intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjpi, hjx0, hfx⟩ := hj
    have hsuppj := hsupp j hjx0 hfx
    have hkP : ∀ P ∈ C.erase x,
        (fun Q => if Q = x then 0 else k Q) P = k P := by
      intro P hP
      simp only [if_neg (Finset.mem_erase.mp hP).1]
    have hcoef : (∏ P ∈ C, ((k P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P))
        = ∏ P ∈ C.erase x, (((fun Q => if Q = x then 0
              else k Q) P).choose (j P) : ℝ)
          * (-(d : ℝ)⁻¹) ^ (j P) := by
      rw [← Finset.mul_prod_erase C _ hx]
      have hfx0 : ((k x).choose (j x) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (j x) = 1 := by
        rw [hjx0]; simp
      rw [hfx0, one_mul]
      exact Finset.prod_congr rfl fun P hP => by rw [hkP P hP]
    have hF : (∏ P ∈ C, realMoment ρ μG (j P))
        = ∏ P ∈ C.erase x, realMoment ρ μG (j P) := by
      rw [← Finset.mul_prod_erase C _ hx, hjx0,
        realMoment_zero, one_mul]
    have hM : colReMomentPow ρ μG C j u u'
        = colReMomentPow ρ μG (C.erase x) j u u' := by
      rw [colReMomentPow_support_reduce, hsuppj]
    rw [hcoef, hF, hM]

/-- On a 4-support, the generic top filter (support
card at least `4`) is the full-support filter. -/
theorem topFilter_card4_eq (k : LayerColumn N → ℕ)
    (C : Finset (LayerColumn N)) (hC : C.card = 4) :
    (Fintype.piFinset (fun P => Finset.range (k P + 1))).filter
        (fun j => 4 ≤ (C.filter (fun P => j P ≠ 0)).card)
    = (Fintype.piFinset (fun P => Finset.range (k P + 1))).filter
        (fun j => (C.filter (fun P => j P ≠ 0)) = C) := by
  ext j
  simp only [Finset.mem_filter]
  constructor
  · intro hj
    refine ⟨hj.1, Finset.eq_of_subset_of_card_le
      (Finset.filter_subset _ _) ?_⟩
    rw [hC]; exact hj.2
  · intro hj
    refine ⟨hj.1, ?_⟩
    have hfc : (C.filter (fun P => j P ≠ 0)).card = 4 := by
      rw [hj.2, hC]
    omega

/-- **The `(3,2,1,1)` pattern value on a 4-support.**
Baseline `A₃A₂B²` plus the six full-support excesses:
quad at `6·d⁻⁴`, doubled at `P` at `−6·d⁻⁵`, doubled
at `Q` at `−3·d⁻⁵`, tripled at `P` at `2·d⁻⁶`,
doubled-doubled at `3·d⁻⁶`, tripled-doubled at
`−d⁻⁷`. -/
theorem patternValue3211_card4 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P Q : LayerColumn N) (hP : P ∈ C)
    (hQ : Q ∈ C) (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G,
        ∏ R ∈ C, (colDensC ρ u u' R α)
          ^ (tripledDoubledQuadPattern7 C P Q R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2) := by
  classical
  have hk0 : ∀ R ∉ C, tripledDoubledQuadPattern7 C P Q R = 0 := by
    intro R hR
    have hRP : R ≠ P := fun h => hR (h ▸ hP)
    have hRQ : R ≠ Q := fun h => hR (h ▸ hQ)
    simp [tripledDoubledQuadPattern7, hRP, hRQ, hR]
  have hQ' : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨Ne.symm hPQ, hQ⟩
  have hbase : ∏ R ∈ C, densMomentValue ρ μG
        (tripledDoubledQuadPattern7 C P Q R)
      = densMomentValue ρ μG 3 * (densMomentValue ρ μG 2
        * (1 - e1 ρ μG / (d : ℝ)) ^ 2) := by
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ']
    have hPP : densMomentValue ρ μG
          (tripledDoubledQuadPattern7 C P Q P)
        = densMomentValue ρ μG 3 := by
      congr 1; simp [tripledDoubledQuadPattern7]
    have hQQ : densMomentValue ρ μG
          (tripledDoubledQuadPattern7 C P Q Q)
        = densMomentValue ρ μG 2 := by
      congr 1; simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
    have hrest : ∀ R ∈ (C.erase P).erase Q,
        densMomentValue ρ μG (tripledDoubledQuadPattern7 C P Q R)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro R hR
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
        simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
      rw [hpat, densMomentValue_one]
    rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 : ℕ) = 2 from rfl]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' C _
    hk0, hbase, topFilter_card4_eq _ C hC]
  -- the full-support top sum, bijected to `Icc 1 3 ×ˢ Icc 1 2`
  set g : ℕ → ℕ → LayerColumn N → ℕ := fun a b R =>
    if R = P then a else if R = Q then b
    else if R ∈ C then 1 else 0 with hg
  have hmem : ∀ p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      g p.1 p.2 ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨ha1, ha3⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    show g p.1 p.2 ∈ _
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro R
      rw [Finset.mem_range]
      by_cases hRP : R = P
      · rw [hRP]
        have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
          simp [tripledDoubledQuadPattern7]
        rw [hpat]
        show g p.1 p.2 P < 3 + 1
        simp only [hg, if_true]
        omega
      · by_cases hRQ : R = Q
        · rw [hRQ]
          have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
            simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
          rw [hpat]
          show g p.1 p.2 Q < 2 + 1
          simp only [hg, Ne.symm hPQ, if_false, if_true]
          omega
        · by_cases hRC : R ∈ C
          · have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
              simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
            rw [hpat]
            show g p.1 p.2 R < 1 + 1
            simp only [hg, hRP, hRQ, hRC, if_false, if_true]
            omega
          · have hpat : tripledDoubledQuadPattern7 C P Q R = 0 :=
              hk0 R hRC
            rw [hpat]
            show g p.1 p.2 R < 0 + 1
            simp only [hg, hRP, hRQ, hRC, if_false]
            omega
    · have hfilt : C.filter (fun R => g p.1 p.2 R ≠ 0) = C := by
        refine Finset.filter_true_of_mem fun R hRC => ?_
        by_cases hRP : R = P
        · rw [hRP]; simp only [hg, if_true]; omega
        · by_cases hRQ : R = Q
          · rw [hRQ]
            simp only [hg, Ne.symm hPQ, if_false, if_true]; omega
          · simp only [hg, hRP, hRQ, hRC, if_false, if_true]
            norm_num
      rw [hfilt]
  have hinj : ∀ p₁ ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      ∀ p₂ ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      g p₁.1 p₁.2 = g p₂.1 p₂.2 → p₁ = p₂ := by
    intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    have ha : a₁ = a₂ := by
      have hP := congrFun h P
      simp only [hg, if_true] at hP
      exact hP
    have hb : b₁ = b₂ := by
      have hQ := congrFun h Q
      simp only [hg, Ne.symm hPQ, if_false, if_true] at hQ
      exact hQ
    rw [ha, hb]
  have hsurj : ∀ j ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C),
      ∃ p, ∃ _ : p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
        g p.1 p.2 = j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjpi, hjfilt⟩ := hj
    have hjpi' := Fintype.mem_piFinset.mp hjpi
    have hjne : ∀ R ∈ C, j R ≠ 0 := by
      intro R hRC
      have hmem : R ∈ C.filter (fun R => j R ≠ 0) := by
        rw [hjfilt]; exact hRC
      exact (Finset.mem_filter.mp hmem).2
    have hbound : ∀ R, j R ≤ tripledDoubledQuadPattern7 C P Q R := by
      intro R
      have hlt := hjpi' R
      rw [Finset.mem_range] at hlt; omega
    have hP3 : j P ≤ 3 := by
      have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
        simp [tripledDoubledQuadPattern7]
      have h := hbound P; rwa [hpat] at h
    have hQ2 : j Q ≤ 2 := by
      have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
        simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
      have h := hbound Q; rwa [hpat] at h
    refine ⟨(j P, j Q), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hjne P hP), hP3⟩,
       Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hjne Q hQ), hQ2⟩⟩,
      ?_⟩
    show g (j P) (j Q) = j
    funext R
    by_cases hRP : R = P
    · rw [hRP]; simp only [hg, if_true]
    · by_cases hRQ : R = Q
      · rw [hRQ]
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      · by_cases hRC : R ∈ C
        · have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
            simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
          have hjR : j R = 1 := by
            have hb := hbound R; rw [hpat] at hb
            have hne := hjne R hRC; omega
          simp only [hg, hRP, hRQ, hRC, if_false, if_true]
          exact hjR.symm
        · have hpat : tripledDoubledQuadPattern7 C P Q R = 0 :=
            hk0 R hRC
          have hjR : j R = 0 := by
            have hb := hbound R; rw [hpat] at hb; omega
          simp only [hg, hRP, hRQ, hRC, if_false]
          exact hjR.symm
  have htop : (∑ j ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C),
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (j R) : ℝ) * (-(d : ℝ)⁻¹) ^ (j R))
        * (colReMomentPow ρ μG C j u u'
          - ∏ R ∈ C, realMoment ρ μG (j R)))
    = ∑ p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (g p.1 p.2 R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p.1 p.2 R))
        * (colReMomentPow ρ μG C (g p.1 p.2) u u'
          - ∏ R ∈ C, realMoment ρ μG (g p.1 p.2 R)) :=
    (Finset.sum_bij (fun p _ => g p.1 p.2) hmem hinj hsurj
      (fun p _ => rfl)).symm
  rw [htop]
  simp only [Finset.sum_product, sum_Icc_one_three, sum_Icc_one_two]
  -- evaluate the six terms
  have hcoeff : ∀ a b : ℕ,
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (g a b R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b R))
        = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a
          * (((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b
            * (-(d : ℝ)⁻¹) ^ 2) := by
    intro a b
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ']
    have hPP : ((tripledDoubledQuadPattern7 C P Q P).choose
          (g a b P) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b P)
        = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a := by
      have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
        simp [tripledDoubledQuadPattern7]
      have hgP : g a b P = a := by simp only [hg, if_true]
      rw [hpat, hgP]
    have hQQ : ((tripledDoubledQuadPattern7 C P Q Q).choose
          (g a b Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b Q)
        = ((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b := by
      have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
        simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
      have hgQ : g a b Q = b := by
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      rw [hpat, hgQ]
    have hrest : ∀ R ∈ (C.erase P).erase Q,
        ((tripledDoubledQuadPattern7 C P Q R).choose
          (g a b R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b R)
          = (-(d : ℝ)⁻¹) := by
      intro R hR
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
        simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
      have hgR : g a b R = 1 := by
        simp only [hg, hRP, hRQ, hRC, if_false, if_true]
      rw [hpat, hgR]; norm_num
    rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 : ℕ) = 2 from rfl]
  have hF : ∀ a b : ℕ,
      (∏ R ∈ C, realMoment ρ μG (g a b R))
        = realMoment ρ μG a
          * (realMoment ρ μG b * (e1 ρ μG) ^ 2) := by
    intro a b
    have hgP : g a b P = a := by simp only [hg, if_true]
    have hgQ : g a b Q = b := by
      simp only [hg, Ne.symm hPQ, if_false, if_true]
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ', hgP, hgQ]
    have hrest : ∀ R ∈ (C.erase P).erase Q,
        realMoment ρ μG (g a b R) = e1 ρ μG := by
      intro R hR
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      have hgR : g a b R = 1 := by
        simp only [hg, hRP, hRQ, hRC, if_false, if_true]
      rw [hgR, realMoment_one]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 : ℕ) = 2 from rfl]
  -- the six moment identifications
  have hgeval : ∀ (a b : ℕ) (R : LayerColumn N), R ∈ C →
      g a b R = if R = P then a else if R = Q then b else 1 := by
    intro a b R hRC
    by_cases hRP : R = P
    · rw [hRP]; simp only [hg, if_true]
    · by_cases hRQ : R = Q
      · rw [hRQ]
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      · simp only [hg, hRP, hRQ, hRC, if_false, if_true]
  have hM11 : colReMomentPow ρ μG C (g 1 1) u u'
      = quadReMoment ρ μG C u u' := by
    have hcong : ∀ R ∈ C, g 1 1 R
        = (fun _ => 1) R := by
      intro R hRC
      rw [hgeval 1 1 R hRC]
      by_cases hRP : R = P
      · simp only [hRP, hPQ, if_false, if_true]
      · by_cases hRQ : R = Q
        · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
        · simp only [hRP, hRQ, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_one]
  have hM21 : colReMomentPow ρ μG C (g 2 1) u u'
      = doubledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ R ∈ C, g 2 1 R
        = (fun R => if R = P then 2 else 1) R := by
      intro R hRC
      rw [hgeval 2 1 R hRC]
      by_cases hRP : R = P
      · simp only [hRP, hPQ, if_false, if_true]
      · by_cases hRQ : R = Q
        · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
        · simp only [hRP, hRQ, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
  have hM12 : colReMomentPow ρ μG C (g 1 2) u u'
      = doubledQuadReMoment ρ μG C Q u u' := by
    have hcong : ∀ R ∈ C, g 1 2 R
        = (fun R => if R = Q then 2 else 1) R := by
      intro R hRC
      rw [hgeval 1 2 R hRC]
      by_cases hRP : R = P
      · simp only [hRP, hPQ, if_false, if_true]
      · by_cases hRQ : R = Q
        · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
        · simp only [hRP, hRQ, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hQ u u']
  have hM31 : colReMomentPow ρ μG C (g 3 1) u u'
      = tripledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ R ∈ C, g 3 1 R
        = (fun R => if R = P then 3 else 1) R := by
      intro R hRC
      rw [hgeval 3 1 R hRC]
      by_cases hRP : R = P
      · simp only [hRP, hPQ, if_false, if_true]
      · by_cases hRQ : R = Q
        · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
        · simp only [hRP, hRQ, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_tripledQuadReMoment ρ μG C hP u u']
  have hM22 : colReMomentPow ρ μG C (g 2 2) u u'
      = doubledDoubledQuadReMoment ρ μG C P Q u u' := by
    have hcong : ∀ R ∈ C, g 2 2 R
        = (fun R => if R = P then 2 else if R = Q then 2 else 1) R := by
      intro R hRC
      rw [hgeval 2 2 R hRC]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C hP hQ
        (Ne.symm hPQ) u u']
  have hM32 : colReMomentPow ρ μG C (g 3 2) u u'
      = tripledDoubledQuadReMoment ρ μG C P Q u u' := by
    have hcong : ∀ R ∈ C, g 3 2 R
        = tripledDoubledQuadPattern7 C P Q R := by
      intro R hRC
      rw [hgeval 3 2 R hRC]
      by_cases hRP : R = P
      · rw [hRP]; simp [tripledDoubledQuadPattern7]
      · by_cases hRQ : R = Q
        · rw [hRQ]
          simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
        · simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_tripledDoubledQuadPattern7 ρ μG C hP hQ
        (Ne.symm hPQ) u u']
  rw [hcoeff 1 1, hcoeff 2 1, hcoeff 1 2, hcoeff 3 1,
    hcoeff 2 2, hcoeff 3 2,
    hF 1 1, hF 2 1, hF 1 2, hF 3 1, hF 2 2, hF 3 2,
    hM11, hM21, hM12, hM31, hM22, hM32]
  norm_num [Nat.choose, realMoment_one]
  ring

/-- **The `(3,2,1,1,1)` pattern value on a 5-support.**
Baseline `A₃A₂B³`, the six full-support excesses (at
weights `d⁻⁵` through `d⁻⁸`), and the erasure parts:
at `P` the `(2,1,1,1)` value on `C.erase P`, at `Q`
the `(3,1,1,1)` value on `C.erase Q`, and at each
light column `R` the `(3,2,1,1)` value on
`C.erase R` (each minus its own baseline). -/
theorem patternValue3211 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) (P Q : LayerColumn N) (hP : P ∈ C)
    (hQ : Q ∈ C) (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G,
        ∏ R ∈ C, (colDensC ρ u u' R α)
          ^ (tripledDoubledQuadPattern7 C P Q R)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 6 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 8
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (3 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - 3 * ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((d : ℝ)⁻¹) ^ 6
            * (tripledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (6 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 6 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
            + 3 * ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - realMoment ρ μG 2 * realMoment ρ μG 2
                  * (e1 ρ μG) ^ 2)
            - ((d : ℝ)⁻¹) ^ 7
              * (tripledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - realMoment ρ μG 3 * realMoment ρ μG 2
                  * (e1 ρ μG) ^ 2)) := by
  classical
  have hk0 : ∀ R ∉ C, tripledDoubledQuadPattern7 C P Q R = 0 := by
    intro R hR
    have hRP : R ≠ P := fun h => hR (h ▸ hP)
    have hRQ : R ≠ Q := fun h => hR (h ▸ hQ)
    simp [tripledDoubledQuadPattern7, hRP, hRQ, hR]
  have hQ' : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨Ne.symm hPQ, hQ⟩
  have hbase : ∏ R ∈ C, densMomentValue ρ μG
        (tripledDoubledQuadPattern7 C P Q R)
      = densMomentValue ρ μG 3 * (densMomentValue ρ μG 2
        * (1 - e1 ρ μG / (d : ℝ)) ^ 3) := by
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ']
    have hPP : densMomentValue ρ μG
          (tripledDoubledQuadPattern7 C P Q P)
        = densMomentValue ρ μG 3 := by
      congr 1; simp [tripledDoubledQuadPattern7]
    have hQQ : densMomentValue ρ μG
          (tripledDoubledQuadPattern7 C P Q Q)
        = densMomentValue ρ μG 2 := by
      congr 1; simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
    have hrest : ∀ R ∈ (C.erase P).erase Q,
        densMomentValue ρ μG (tripledDoubledQuadPattern7 C P Q R)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro R hR
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRP : R ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
      have hRC : R ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
      have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
        simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
      rw [hpat, densMomentValue_one]
    rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((5 - 1) - 1 : ℕ) = 3 from rfl]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' C _
    hk0, hbase, topSum_card5_split ρ μG (tripledDoubledQuadPattern7 C P Q)
    C hC u u']
  -- full-support part: bijection to `Icc 1 3 ×ˢ Icc 1 2`
  set g : ℕ → ℕ → LayerColumn N → ℕ := fun a b R =>
    if R = P then a else if R = Q then b
    else if R ∈ C then 1 else 0 with hg
  have hmem : ∀ p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      g p.1 p.2 ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨ha1, ha3⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    show g p.1 p.2 ∈ _
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro R
      rw [Finset.mem_range]
      by_cases hRP : R = P
      · rw [hRP]
        have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
          simp [tripledDoubledQuadPattern7]
        rw [hpat]
        show g p.1 p.2 P < 3 + 1
        simp only [hg, if_true]
        omega
      · by_cases hRQ : R = Q
        · rw [hRQ]
          have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
            simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
          rw [hpat]
          show g p.1 p.2 Q < 2 + 1
          simp only [hg, Ne.symm hPQ, if_false, if_true]
          omega
        · by_cases hRC : R ∈ C
          · have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
              simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
            rw [hpat]
            show g p.1 p.2 R < 1 + 1
            simp only [hg, hRP, hRQ, hRC, if_false, if_true]
            omega
          · have hpat : tripledDoubledQuadPattern7 C P Q R = 0 :=
              hk0 R hRC
            rw [hpat]
            show g p.1 p.2 R < 0 + 1
            simp only [hg, hRP, hRQ, hRC, if_false]
            omega
    · have hfilt : C.filter (fun R => g p.1 p.2 R ≠ 0) = C := by
        refine Finset.filter_true_of_mem fun R hRC => ?_
        by_cases hRP : R = P
        · rw [hRP]; simp only [hg, if_true]; omega
        · by_cases hRQ : R = Q
          · rw [hRQ]
            simp only [hg, Ne.symm hPQ, if_false, if_true]; omega
          · simp only [hg, hRP, hRQ, hRC, if_false, if_true]
            norm_num
      rw [hfilt]
  have hinj : ∀ p₁ ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      ∀ p₂ ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
      g p₁.1 p₁.2 = g p₂.1 p₂.2 → p₁ = p₂ := by
    intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    have ha : a₁ = a₂ := by
      have hP := congrFun h P
      simp only [hg, if_true] at hP
      exact hP
    have hb : b₁ = b₂ := by
      have hQ := congrFun h Q
      simp only [hg, Ne.symm hPQ, if_false, if_true] at hQ
      exact hQ
    rw [ha, hb]
  have hsurj : ∀ j ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C),
      ∃ p, ∃ _ : p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
        g p.1 p.2 = j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjpi, hjfilt⟩ := hj
    have hjpi' := Fintype.mem_piFinset.mp hjpi
    have hjne : ∀ R ∈ C, j R ≠ 0 := by
      intro R hRC
      have hmem : R ∈ C.filter (fun R => j R ≠ 0) := by
        rw [hjfilt]; exact hRC
      exact (Finset.mem_filter.mp hmem).2
    have hbound : ∀ R, j R ≤ tripledDoubledQuadPattern7 C P Q R := by
      intro R
      have hlt := hjpi' R
      rw [Finset.mem_range] at hlt; omega
    have hP3 : j P ≤ 3 := by
      have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
        simp [tripledDoubledQuadPattern7]
      have h := hbound P; rwa [hpat] at h
    have hQ2 : j Q ≤ 2 := by
      have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
        simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
      have h := hbound Q; rwa [hpat] at h
    refine ⟨(j P, j Q), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hjne P hP), hP3⟩,
       Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hjne Q hQ), hQ2⟩⟩,
      ?_⟩
    show g (j P) (j Q) = j
    funext R
    by_cases hRP : R = P
    · rw [hRP]; simp only [hg, if_true]
    · by_cases hRQ : R = Q
      · rw [hRQ]
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      · by_cases hRC : R ∈ C
        · have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
            simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
          have hjR : j R = 1 := by
            have hb := hbound R; rw [hpat] at hb
            have hne := hjne R hRC; omega
          simp only [hg, hRP, hRQ, hRC, if_false, if_true]
          exact hjR.symm
        · have hpat : tripledDoubledQuadPattern7 C P Q R = 0 :=
            hk0 R hRC
          have hjR : j R = 0 := by
            have hb := hbound R; rw [hpat] at hb; omega
          simp only [hg, hRP, hRQ, hRC, if_false]
          exact hjR.symm
  have hfull : (∑ j ∈ (Fintype.piFinset (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => (C.filter (fun R => j R ≠ 0)) = C),
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (j R) : ℝ) * (-(d : ℝ)⁻¹) ^ (j R))
        * (colReMomentPow ρ μG C j u u'
          - ∏ R ∈ C, realMoment ρ μG (j R)))
    = - 6 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 6 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - 2 * ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        - 3 * ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 3)
        + ((d : ℝ)⁻¹) ^ 8
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 3) := by
    have htop : (∑ j ∈ (Fintype.piFinset (fun R => Finset.range
            (tripledDoubledQuadPattern7 C P Q R + 1))).filter
          (fun j => (C.filter (fun R => j R ≠ 0)) = C),
        (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
            (j R) : ℝ) * (-(d : ℝ)⁻¹) ^ (j R))
          * (colReMomentPow ρ μG C j u u'
            - ∏ R ∈ C, realMoment ρ μG (j R)))
      = ∑ p ∈ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2,
        (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
            (g p.1 p.2 R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p.1 p.2 R))
          * (colReMomentPow ρ μG C (g p.1 p.2) u u'
            - ∏ R ∈ C, realMoment ρ μG (g p.1 p.2 R)) :=
      (Finset.sum_bij (fun p _ => g p.1 p.2) hmem hinj hsurj
        (fun p _ => rfl)).symm
    rw [htop]
    simp only [Finset.sum_product, sum_Icc_one_three, sum_Icc_one_two]
    have hcoeff : ∀ a b : ℕ,
        (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
            (g a b R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b R))
          = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a
            * (((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b
              * (-(d : ℝ)⁻¹) ^ 3) := by
      intro a b
      rw [← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _ hQ']
      have hPP : ((tripledDoubledQuadPattern7 C P Q P).choose
            (g a b P) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b P)
          = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a := by
        have hpat : tripledDoubledQuadPattern7 C P Q P = 3 := by
          simp [tripledDoubledQuadPattern7]
        have hgP : g a b P = a := by simp only [hg, if_true]
        rw [hpat, hgP]
      have hQQ : ((tripledDoubledQuadPattern7 C P Q Q).choose
            (g a b Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b Q)
          = ((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b := by
        have hpat : tripledDoubledQuadPattern7 C P Q Q = 2 := by
          simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
        have hgQ : g a b Q = b := by
          simp only [hg, Ne.symm hPQ, if_false, if_true]
        rw [hpat, hgQ]
      have hrest : ∀ R ∈ (C.erase P).erase Q,
          ((tripledDoubledQuadPattern7 C P Q R).choose
            (g a b R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b R)
            = (-(d : ℝ)⁻¹) := by
        intro R hR
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
        have hpat : tripledDoubledQuadPattern7 C P Q R = 1 := by
          simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
        have hgR : g a b R = 1 := by
          simp only [hg, hRP, hRQ, hRC, if_false, if_true]
        rw [hpat, hgR]; norm_num
      rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
        show ((5 - 1) - 1 : ℕ) = 3 from rfl]
    have hF : ∀ a b : ℕ,
        (∏ R ∈ C, realMoment ρ μG (g a b R))
          = realMoment ρ μG a
            * (realMoment ρ μG b * (e1 ρ μG) ^ 3) := by
      intro a b
      have hgP : g a b P = a := by simp only [hg, if_true]
      have hgQ : g a b Q = b := by
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      rw [← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _ hQ', hgP, hgQ]
      have hrest : ∀ R ∈ (C.erase P).erase Q,
          realMoment ρ μG (g a b R) = e1 ρ μG := by
        intro R hR
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
        have hgR : g a b R = 1 := by
          simp only [hg, hRP, hRQ, hRC, if_false, if_true]
        rw [hgR, realMoment_one]
      rw [Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
        show ((5 - 1) - 1 : ℕ) = 3 from rfl]
    have hgeval : ∀ (a b : ℕ) (R : LayerColumn N), R ∈ C →
        g a b R = if R = P then a else if R = Q then b else 1 := by
      intro a b R hRC
      by_cases hRP : R = P
      · rw [hRP]; simp only [hg, if_true]
      · by_cases hRQ : R = Q
        · rw [hRQ]
          simp only [hg, Ne.symm hPQ, if_false, if_true]
        · simp only [hg, hRP, hRQ, hRC, if_false, if_true]
    have hM11 : colReMomentPow ρ μG C (g 1 1) u u'
        = quadReMoment ρ μG C u u' := by
      have hcong : ∀ R ∈ C, g 1 1 R = (fun _ => 1) R := by
        intro R hRC
        rw [hgeval 1 1 R hRC]
        by_cases hRP : R = P
        · simp only [hRP, hPQ, if_false, if_true]
        · by_cases hRQ : R = Q
          · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
          · simp only [hRP, hRQ, if_false, if_true]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_one]
    have hM21 : colReMomentPow ρ μG C (g 2 1) u u'
        = doubledQuadReMoment ρ μG C P u u' := by
      have hcong : ∀ R ∈ C, g 2 1 R
          = (fun R => if R = P then 2 else 1) R := by
        intro R hRC
        rw [hgeval 2 1 R hRC]
        by_cases hRP : R = P
        · simp only [hRP, hPQ, if_false, if_true]
        · by_cases hRQ : R = Q
          · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
          · simp only [hRP, hRQ, if_false, if_true]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
    have hM12 : colReMomentPow ρ μG C (g 1 2) u u'
        = doubledQuadReMoment ρ μG C Q u u' := by
      have hcong : ∀ R ∈ C, g 1 2 R
          = (fun R => if R = Q then 2 else 1) R := by
        intro R hRC
        rw [hgeval 1 2 R hRC]
        by_cases hRP : R = P
        · simp only [hRP, hPQ, if_false, if_true]
        · by_cases hRQ : R = Q
          · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
          · simp only [hRP, hRQ, if_false, if_true]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledQuadReMoment ρ μG C hQ u u']
    have hM31 : colReMomentPow ρ μG C (g 3 1) u u'
        = tripledQuadReMoment ρ μG C P u u' := by
      have hcong : ∀ R ∈ C, g 3 1 R
          = (fun R => if R = P then 3 else 1) R := by
        intro R hRC
        rw [hgeval 3 1 R hRC]
        by_cases hRP : R = P
        · simp only [hRP, hPQ, if_false, if_true]
        · by_cases hRQ : R = Q
          · simp only [hRQ, hRP, hPQ, Ne.symm hPQ, if_false, if_true]
          · simp only [hRP, hRQ, if_false, if_true]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_tripledQuadReMoment ρ μG C hP u u']
    have hM22 : colReMomentPow ρ μG C (g 2 2) u u'
        = doubledDoubledQuadReMoment ρ μG C P Q u u' := by
      have hcong : ∀ R ∈ C, g 2 2 R
          = (fun R => if R = P then 2 else if R = Q then 2
              else 1) R := by
        intro R hRC
        rw [hgeval 2 2 R hRC]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C hP hQ
          (Ne.symm hPQ) u u']
    have hM32 : colReMomentPow ρ μG C (g 3 2) u u'
        = tripledDoubledQuadReMoment ρ μG C P Q u u' := by
      have hcong : ∀ R ∈ C, g 3 2 R
          = tripledDoubledQuadPattern7 C P Q R := by
        intro R hRC
        rw [hgeval 3 2 R hRC]
        by_cases hRP : R = P
        · rw [hRP]; simp [tripledDoubledQuadPattern7]
        · by_cases hRQ : R = Q
          · rw [hRQ]
            simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
          · simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_tripledDoubledQuadPattern7 ρ μG C hP hQ
          (Ne.symm hPQ) u u']
    rw [hcoeff 1 1, hcoeff 2 1, hcoeff 1 2, hcoeff 3 1,
      hcoeff 2 2, hcoeff 3 2,
      hF 1 1, hF 2 1, hF 1 2, hF 3 1, hF 2 2, hF 3 2,
      hM11, hM21, hM12, hM31, hM22, hM32]
    norm_num [Nat.choose, realMoment_one]
    ring
  rw [hfull, ← Finset.sum_erase_add _ _ hP]
  -- the piece at `P` is split off; `Q` and the lights remain
  -- piece at `P`: the `(2,1,1,1)` value on `C.erase P`
  have hpieceP : (∑ j ∈ (Fintype.piFinset
        (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => j P = 0 ∧ (C.erase P).filter
          (fun R => j R ≠ 0) = C.erase P),
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (j R) : ℝ) * (-(d : ℝ)⁻¹) ^ (j R))
        * (colReMomentPow ρ μG C j u u'
          - ∏ R ∈ C, realMoment ρ μG (j R)))
    = 2 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
      - ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [pieceSum_eq_topSum_erase ρ μG (tripledDoubledQuadPattern7 C P Q)
      C hC hP u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase P)
      (fun R => if R = P then 0
        else tripledDoubledQuadPattern7 C P Q R)
      (by intro R hR
          by_cases hRP : R = P
          · rw [hRP]; simp
          · rw [if_neg hRP]
            exact hk0 R (fun h => hR
              (Finset.mem_erase.mpr ⟨hRP, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ R ∈ C.erase P, (colDensC ρ u u' R α)
            ^ ((fun R => if R = P then 0
              else tripledDoubledQuadPattern7 C P Q R) R)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ R ∈ C.erase P, (colDensC ρ u u' R α)
            ^ (if R = Q then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun R hR => ?_
      have hRP : R ≠ P := (Finset.mem_erase.mp hR).1
      have hRC : R ∈ C := (Finset.mem_erase.mp hR).2
      congr 1
      by_cases hRQ : R = Q
      · rw [hRQ]
        simp [tripledDoubledQuadPattern7, hRP, Ne.symm hPQ]
      · simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
    have hbaseE : (∏ R ∈ C.erase P, densMomentValue ρ μG
          ((fun R => if R = P then 0
            else tripledDoubledQuadPattern7 C P Q R) R))
        = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
      rw [← Finset.mul_prod_erase (C.erase P) _ hQ']
      have hQQ : densMomentValue ρ μG
            ((fun R => if R = P then 0
              else tripledDoubledQuadPattern7 C P Q R) Q)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
      have hrest : ∀ R ∈ (C.erase P).erase Q,
          densMomentValue ρ μG
            ((fun R => if R = P then 0
              else tripledDoubledQuadPattern7 C P Q R) R)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro R hR
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
        have hval : (fun R => if R = P then 0
              else tripledDoubledQuadPattern7 C P Q R) R = 1 := by
          simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
        rw [hval, densMomentValue_one]
      have hcardP : (C.erase P).card = 4 := by
        rw [Finset.card_erase_of_mem hP, hC]
      rw [hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hQ', hcardP,
        show (4 - 1 : ℕ) = 3 from rfl]
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_doubled ρ μG hN hN3 hρcont u u'
        (C.erase P) (by rw [Finset.card_erase_of_mem hP, hC]) Q hQ']
      at hgen
    linarith
  rw [hpieceP, ← Finset.sum_erase_add _ _ hQ']
  -- piece at `Q`: the `(3,1,1,1)` value on `C.erase Q`
  have hpieceQ : (∑ j ∈ (Fintype.piFinset
        (fun R => Finset.range
          (tripledDoubledQuadPattern7 C P Q R + 1))).filter
        (fun j => j Q = 0 ∧ (C.erase Q).filter
          (fun R => j R ≠ 0) = C.erase Q),
      (∏ R ∈ C, ((tripledDoubledQuadPattern7 C P Q R).choose
          (j R) : ℝ) * (-(d : ℝ)⁻¹) ^ (j R))
        * (colReMomentPow ρ μG C j u u'
          - ∏ R ∈ C, realMoment ρ μG (j R)))
    = 3 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase Q) u u' - (e1 ρ μG) ^ 4)
      - 3 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      + ((d : ℝ)⁻¹) ^ 6
        * (tripledQuadReMoment ρ μG (C.erase Q) P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    have hP' : P ∈ C.erase Q :=
      Finset.mem_erase.mpr ⟨hPQ, hP⟩
    rw [pieceSum_eq_topSum_erase ρ μG (tripledDoubledQuadPattern7 C P Q)
      C hC hQ u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase Q)
      (fun R => if R = Q then 0
        else tripledDoubledQuadPattern7 C P Q R)
      (by intro R hR
          by_cases hRQ : R = Q
          · rw [hRQ]; simp
          · rw [if_neg hRQ]
            exact hk0 R (fun h => hR
              (Finset.mem_erase.mpr ⟨hRQ, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ R ∈ C.erase Q, (colDensC ρ u u' R α)
            ^ ((fun R => if R = Q then 0
              else tripledDoubledQuadPattern7 C P Q R) R)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ R ∈ C.erase Q, (colDensC ρ u u' R α)
            ^ (if R = P then 3 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun R hR => ?_
      have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
      have hRC : R ∈ C := (Finset.mem_erase.mp hR).2
      congr 1
      by_cases hRP : R = P
      · rw [hRP]
        simp [tripledDoubledQuadPattern7, hPQ]
      · simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
    have hbaseE : (∏ R ∈ C.erase Q, densMomentValue ρ μG
          ((fun R => if R = Q then 0
            else tripledDoubledQuadPattern7 C P Q R) R))
        = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
      rw [← Finset.mul_prod_erase (C.erase Q) _ hP']
      have hPP : densMomentValue ρ μG
            ((fun R => if R = Q then 0
              else tripledDoubledQuadPattern7 C P Q R) P)
          = densMomentValue ρ μG 3 := by
        congr 1
        simp [tripledDoubledQuadPattern7, hPQ]
      have hrest : ∀ R ∈ (C.erase Q).erase P,
          densMomentValue ρ μG
            ((fun R => if R = Q then 0
              else tripledDoubledQuadPattern7 C P Q R) R)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro R hR
        have hRP : R ≠ P := (Finset.mem_erase.mp hR).1
        have hRQ : R ≠ Q :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRC : R ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
        have hval : (fun R => if R = Q then 0
              else tripledDoubledQuadPattern7 C P Q R) R = 1 := by
          simp [tripledDoubledQuadPattern7, hRP, hRQ, hRC]
        rw [hval, densMomentValue_one]
      have hcardQ : (C.erase Q).card = 4 := by
        rw [Finset.card_erase_of_mem hQ, hC]
      rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hP', hcardQ,
        show (4 - 1 : ℕ) = 3 from rfl]
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_tripled ρ μG hN hN3 hρcont u u'
        (C.erase Q) (by rw [Finset.card_erase_of_mem hQ, hC]) P hP']
      at hgen
    linarith
  rw [hpieceQ]
  -- pieces at light columns: the `(3,2,1,1)` value on `C.erase R`
  have hpieceR : ∀ R ∈ (C.erase P).erase Q,
      (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (tripledDoubledQuadPattern7 C P Q S + 1))).filter
        (fun j => j R = 0 ∧ (C.erase R).filter
          (fun S => j S ≠ 0) = C.erase R),
      (∏ S ∈ C, ((tripledDoubledQuadPattern7 C P Q S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = 6 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4)
      - 6 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      - 3 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      + 2 * ((d : ℝ)⁻¹) ^ 6
        * (tripledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      + 3 * ((d : ℝ)⁻¹) ^ 6
        * (doubledDoubledQuadReMoment ρ μG (C.erase R) P Q u u'
          - realMoment ρ μG 2 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2)
      - ((d : ℝ)⁻¹) ^ 7
        * (tripledDoubledQuadReMoment ρ μG (C.erase R) P Q u u'
          - realMoment ρ μG 3 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2) := by
    intro R hR
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRC : R ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    have hP' : P ∈ C.erase R :=
      Finset.mem_erase.mpr ⟨Ne.symm hRP, hP⟩
    have hQ'R : Q ∈ C.erase R :=
      Finset.mem_erase.mpr ⟨Ne.symm hRQ, hQ⟩
    have hQ'' : Q ∈ (C.erase R).erase P :=
      Finset.mem_erase.mpr ⟨Ne.symm hPQ, hQ'R⟩
    have hcardR : (C.erase R).card = 4 := by
      rw [Finset.card_erase_of_mem hRC, hC]
    rw [pieceSum_eq_topSum_erase ρ μG (tripledDoubledQuadPattern7 C P Q)
      C hC hRC u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase R)
      (fun S => if S = R then 0
        else tripledDoubledQuadPattern7 C P Q S)
      (by intro S hS
          by_cases hSR : S = R
          · rw [hSR]; simp
          · rw [if_neg hSR]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSR, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ ((fun S => if S = R then 0
              else tripledDoubledQuadPattern7 C P Q S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ (tripledDoubledQuadPattern7 (C.erase R) P Q S)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun S hS => ?_
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      congr 1
      by_cases hSP : S = P
      · rw [hSP]
        simp [tripledDoubledQuadPattern7, Ne.symm hRP]
      · by_cases hSQ : S = Q
        · rw [hSQ]
          simp [tripledDoubledQuadPattern7, Ne.symm hRQ,
            Ne.symm hPQ]
        · have hSmem : S ∈ C.erase R :=
            Finset.mem_erase.mpr ⟨hSR, hSC⟩
          simp [tripledDoubledQuadPattern7, hSR, hSP, hSQ, hSC,
            hSmem]
    have hbaseE : (∏ S ∈ C.erase R, densMomentValue ρ μG
          ((fun S => if S = R then 0
            else tripledDoubledQuadPattern7 C P Q S) S))
        = densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2 := by
      have hval0 : ∀ S ∈ C.erase R,
          (fun S => if S = R then 0
            else tripledDoubledQuadPattern7 C P Q S) S
            = tripledDoubledQuadPattern7 (C.erase R) P Q S := by
        intro S hS
        have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
        have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
        by_cases hSP : S = P
        · rw [hSP]
          simp [tripledDoubledQuadPattern7, Ne.symm hRP]
        · by_cases hSQ : S = Q
          · rw [hSQ]
            simp [tripledDoubledQuadPattern7, Ne.symm hRQ,
              Ne.symm hPQ]
          · have hSmem : S ∈ C.erase R :=
              Finset.mem_erase.mpr ⟨hSR, hSC⟩
            simp [tripledDoubledQuadPattern7, hSR, hSP, hSQ, hSC,
              hSmem]
      have hval : ∀ S ∈ C.erase R,
          densMomentValue ρ μG
            ((fun S => if S = R then 0
              else tripledDoubledQuadPattern7 C P Q S) S)
            = densMomentValue ρ μG
              (tripledDoubledQuadPattern7 (C.erase R) P Q S) :=
        fun S hS => by rw [hval0 S hS]
      rw [Finset.prod_congr rfl hval]
      rw [← Finset.mul_prod_erase (C.erase R) _ hP',
        ← Finset.mul_prod_erase ((C.erase R).erase P) _ hQ'']
      have hPP : densMomentValue ρ μG
            (tripledDoubledQuadPattern7 (C.erase R) P Q P)
          = densMomentValue ρ μG 3 := by
        congr 1; simp [tripledDoubledQuadPattern7]
      have hQQ : densMomentValue ρ μG
            (tripledDoubledQuadPattern7 (C.erase R) P Q Q)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [tripledDoubledQuadPattern7, Ne.symm hPQ]
      have hrest : ∀ S ∈ ((C.erase R).erase P).erase Q,
          densMomentValue ρ μG
            (tripledDoubledQuadPattern7 (C.erase R) P Q S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C.erase R :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hpat : tripledDoubledQuadPattern7 (C.erase R) P Q S
            = 1 := by
          simp [tripledDoubledQuadPattern7, hSP, hSQ, hSC]
        rw [hpat, densMomentValue_one]
      rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hQ'',
        Finset.card_erase_of_mem hP', hcardR,
        show ((4 - 1) - 1 : ℕ) = 2 from rfl]
      ring
    rw [hint, hbaseE,
      patternValue3211_card4 ρ μG hN hN3 hρcont u u' (C.erase R)
        hcardR P Q hP' hQ'R hPQ] at hgen
    linarith
  rw [Finset.sum_congr rfl hpieceR]
  ring

/-- **The `(2,2,2,1)` pattern value on a 4-support.**
Baseline `A₂³B` plus the eight full-support excesses:
quad at `8·d⁻⁴`, each doubled at `−4·d⁻⁵`, each
doubled-doubled pair at `2·d⁻⁶`, the
doubled-doubled-doubled at `−d⁻⁷`. -/
theorem patternValue2221_card4 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P Q R : LayerColumn N) (hP : P ∈ C)
    (hQ : Q ∈ C) (hR : R ∈ C) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G,
        ∏ S ∈ C, (colDensC ρ u u' S α)
          ^ (doubledDoubledDoubledQuadPattern7 C P Q R S)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG) := by
  classical
  have hk0 : ∀ S ∉ C,
      doubledDoubledDoubledQuadPattern7 C P Q R S = 0 := by
    intro S hS
    have hSP : S ≠ P := fun h => hS (h ▸ hP)
    have hSQ : S ≠ Q := fun h => hS (h ▸ hQ)
    have hSR : S ≠ R := fun h => hS (h ▸ hR)
    simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ, hSR, hS]
  have hQ' : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨Ne.symm hPQ, hQ⟩
  have hR' : R ∈ (C.erase P).erase Q :=
    Finset.mem_erase.mpr ⟨Ne.symm hQR,
      Finset.mem_erase.mpr ⟨Ne.symm hPR, hR⟩⟩
  have hbase : ∏ S ∈ C, densMomentValue ρ μG
        (doubledDoubledDoubledQuadPattern7 C P Q R S)
      = densMomentValue ρ μG 2 * (densMomentValue ρ μG 2
        * (densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 1)) := by
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ',
      ← Finset.mul_prod_erase ((C.erase P).erase Q) _ hR']
    have hPP : densMomentValue ρ μG
          (doubledDoubledDoubledQuadPattern7 C P Q R P)
        = densMomentValue ρ μG 2 := by
      congr 1; simp [doubledDoubledDoubledQuadPattern7]
    have hQQ : densMomentValue ρ μG
          (doubledDoubledDoubledQuadPattern7 C P Q R Q)
        = densMomentValue ρ μG 2 := by
      congr 1
      simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPQ]
    have hRR : densMomentValue ρ μG
          (doubledDoubledDoubledQuadPattern7 C P Q R R)
        = densMomentValue ρ μG 2 := by
      congr 1
      simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPR,
        Ne.symm hQR]
    have hrest : ∀ S ∈ ((C.erase P).erase Q).erase R,
        densMomentValue ρ μG
          (doubledDoubledDoubledQuadPattern7 C P Q R S)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro S hS
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSQ : S ≠ Q :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
      have hSP : S ≠ P :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).1
      have hSC : S ∈ C :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).2
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R S
          = 1 := by
        simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ, hSR,
          hSC]
      rw [hpat, densMomentValue_one]
    rw [hPP, hQQ, hRR, Finset.prod_congr rfl hrest,
      Finset.prod_const, Finset.card_erase_of_mem hR',
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 - 1 : ℕ) = 1 from rfl]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' C _
    hk0, hbase, topFilter_card4_eq _ C hC]
  -- bijection to `(Icc 1 2 ×ˢ Icc 1 2) ×ˢ Icc 1 2`
  set g : ℕ → ℕ → ℕ → LayerColumn N → ℕ := fun a b c S =>
    if S = P then a else if S = Q then b else if S = R then c
    else if S ∈ C then 1 else 0 with hg
  have hgeval : ∀ (a b c : ℕ) (S : LayerColumn N), S ∈ C →
      g a b c S = if S = P then a else if S = Q then b
        else if S = R then c else 1 := by
    intro a b c S hSC
    by_cases hSP : S = P
    · rw [hSP]; simp only [hg, if_true]
    · by_cases hSQ : S = Q
      · rw [hSQ]
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      · by_cases hSR : S = R
        · rw [hSR]
          simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false,
            if_true]
        · simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
  have hmem : ∀ p ∈ (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2)
        ×ˢ Finset.Icc 1 2,
      g p.1.1 p.1.2 p.2 ∈ (Fintype.piFinset (fun S => Finset.range
          (doubledDoubledDoubledQuadPattern7 C P Q R S + 1))).filter
        (fun j => (C.filter (fun S => j S ≠ 0)) = C) := by
    intro p hp
    obtain ⟨hp12, hc⟩ := Finset.mem_product.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp12
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.mp hc
    show g p.1.1 p.1.2 p.2 ∈ _
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro S
      rw [Finset.mem_range]
      by_cases hSP : S = P
      · rw [hSP]
        have hpat : doubledDoubledDoubledQuadPattern7 C P Q R P
            = 2 := by
          simp [doubledDoubledDoubledQuadPattern7]
        rw [hpat]
        show g p.1.1 p.1.2 p.2 P < 2 + 1
        simp only [hg, if_true]
        omega
      · by_cases hSQ : S = Q
        · rw [hSQ]
          have hpat : doubledDoubledDoubledQuadPattern7 C P Q R Q
              = 2 := by
            simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPQ]
          rw [hpat]
          show g p.1.1 p.1.2 p.2 Q < 2 + 1
          simp only [hg, Ne.symm hPQ, if_false, if_true]
          omega
        · by_cases hSR : S = R
          · rw [hSR]
            have hpat : doubledDoubledDoubledQuadPattern7 C P Q R R
                = 2 := by
              simp [doubledDoubledDoubledQuadPattern7,
                Ne.symm hPR, Ne.symm hQR]
            rw [hpat]
            show g p.1.1 p.1.2 p.2 R < 2 + 1
            simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false,
              if_true]
            omega
          · by_cases hSC : S ∈ C
            · have hpat : doubledDoubledDoubledQuadPattern7
                  C P Q R S = 1 := by
                simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ,
                  hSR, hSC]
              rw [hpat]
              show g p.1.1 p.1.2 p.2 S < 1 + 1
              simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
              omega
            · have hpat : doubledDoubledDoubledQuadPattern7
                  C P Q R S = 0 := hk0 S hSC
              rw [hpat]
              show g p.1.1 p.1.2 p.2 S < 0 + 1
              simp only [hg, hSP, hSQ, hSR, hSC, if_false]
              omega
    · have hfilt : C.filter (fun S => g p.1.1 p.1.2 p.2 S ≠ 0)
          = C := by
        refine Finset.filter_true_of_mem fun S hSC => ?_
        by_cases hSP : S = P
        · rw [hSP]; simp only [hg, if_true]; omega
        · by_cases hSQ : S = Q
          · rw [hSQ]
            simp only [hg, Ne.symm hPQ, if_false, if_true]; omega
          · by_cases hSR : S = R
            · rw [hSR]
              simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false,
                if_true]
              omega
            · simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
              norm_num
      rw [hfilt]
  have hinj : ∀ p₁ ∈ (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2)
        ×ˢ Finset.Icc 1 2,
      ∀ p₂ ∈ (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2)
        ×ˢ Finset.Icc 1 2,
      g p₁.1.1 p₁.1.2 p₁.2 = g p₂.1.1 p₂.1.2 p₂.2 → p₁ = p₂ := by
    intro ⟨⟨a₁, b₁⟩, c₁⟩ _ ⟨⟨a₂, b₂⟩, c₂⟩ _ h
    have ha : a₁ = a₂ := by
      have hP := congrFun h P
      simp only [hg, if_true] at hP
      exact hP
    have hb : b₁ = b₂ := by
      have hQ := congrFun h Q
      simp only [hg, Ne.symm hPQ, if_false, if_true] at hQ
      exact hQ
    have hc : c₁ = c₂ := by
      have hR := congrFun h R
      simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false, if_true]
        at hR
      exact hR
    rw [ha, hb, hc]
  have hsurj : ∀ j ∈ (Fintype.piFinset (fun S => Finset.range
          (doubledDoubledDoubledQuadPattern7 C P Q R S + 1))).filter
        (fun j => (C.filter (fun S => j S ≠ 0)) = C),
      ∃ p, ∃ _ : p ∈ (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2)
        ×ˢ Finset.Icc 1 2, g p.1.1 p.1.2 p.2 = j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjpi, hjfilt⟩ := hj
    have hjpi' := Fintype.mem_piFinset.mp hjpi
    have hjne : ∀ S ∈ C, j S ≠ 0 := by
      intro S hSC
      have hmem : S ∈ C.filter (fun S => j S ≠ 0) := by
        rw [hjfilt]; exact hSC
      exact (Finset.mem_filter.mp hmem).2
    have hbound : ∀ S, j S
        ≤ doubledDoubledDoubledQuadPattern7 C P Q R S := by
      intro S
      have hlt := hjpi' S
      rw [Finset.mem_range] at hlt; omega
    have hP2 : j P ≤ 2 := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R P
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7]
      have h := hbound P; rwa [hpat] at h
    have hQ2 : j Q ≤ 2 := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R Q
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPQ]
      have h := hbound Q; rwa [hpat] at h
    have hR2 : j R ≤ 2 := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R R
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPR,
          Ne.symm hQR]
      have h := hbound R; rwa [hpat] at h
    refine ⟨((j P, j Q), j R), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (hjne P hP), hP2⟩,
         Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (hjne Q hQ), hQ2⟩⟩,
       Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (hjne R hR), hR2⟩⟩, ?_⟩
    show g (j P) (j Q) (j R) = j
    funext S
    by_cases hSP : S = P
    · rw [hSP]; simp only [hg, if_true]
    · by_cases hSQ : S = Q
      · rw [hSQ]
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      · by_cases hSR : S = R
        · rw [hSR]
          simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false,
            if_true]
        · by_cases hSC : S ∈ C
          · have hpat : doubledDoubledDoubledQuadPattern7
                C P Q R S = 1 := by
              simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ,
                hSR, hSC]
            have hjS : j S = 1 := by
              have hb := hbound S; rw [hpat] at hb
              have hne := hjne S hSC; omega
            simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
            exact hjS.symm
          · have hpat : doubledDoubledDoubledQuadPattern7
                C P Q R S = 0 := hk0 S hSC
            have hjS : j S = 0 := by
              have hb := hbound S; rw [hpat] at hb; omega
            simp only [hg, hSP, hSQ, hSR, hSC, if_false]
            exact hjS.symm
  have htop : (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (doubledDoubledDoubledQuadPattern7 C P Q R S + 1))).filter
        (fun j => (C.filter (fun S => j S ≠ 0)) = C),
      (∏ S ∈ C, ((doubledDoubledDoubledQuadPattern7 C P Q R S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = ∑ p ∈ (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2) ×ˢ Finset.Icc 1 2,
      (∏ S ∈ C, ((doubledDoubledDoubledQuadPattern7 C P Q R S).choose
          (g p.1.1 p.1.2 p.2 S) : ℝ)
        * (-(d : ℝ)⁻¹) ^ (g p.1.1 p.1.2 p.2 S))
        * (colReMomentPow ρ μG C (g p.1.1 p.1.2 p.2) u u'
          - ∏ S ∈ C, realMoment ρ μG (g p.1.1 p.1.2 p.2 S)) :=
    (Finset.sum_bij (fun p _ => g p.1.1 p.1.2 p.2) hmem hinj hsurj
      (fun p _ => rfl)).symm
  rw [htop]
  simp only [Finset.sum_product, sum_Icc_one_two]
  -- evaluate the eight terms
  have hcoeff : ∀ a b c : ℕ,
      (∏ S ∈ C, ((doubledDoubledDoubledQuadPattern7 C P Q R S).choose
          (g a b c S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b c S))
        = ((Nat.choose 2 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a
          * (((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b
            * (((Nat.choose 2 c : ℝ)) * (-(d : ℝ)⁻¹) ^ c
              * (-(d : ℝ)⁻¹) ^ 1)) := by
    intro a b c
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ',
      ← Finset.mul_prod_erase ((C.erase P).erase Q) _ hR']
    have hPP : ((doubledDoubledDoubledQuadPattern7 C P Q R P).choose
          (g a b c P) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b c P)
        = ((Nat.choose 2 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R P
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7]
      have hgP : g a b c P = a := by simp only [hg, if_true]
      rw [hpat, hgP]
    have hQQ : ((doubledDoubledDoubledQuadPattern7 C P Q R Q).choose
          (g a b c Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b c Q)
        = ((Nat.choose 2 b : ℝ)) * (-(d : ℝ)⁻¹) ^ b := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R Q
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPQ]
      have hgQ : g a b c Q = b := by
        simp only [hg, Ne.symm hPQ, if_false, if_true]
      rw [hpat, hgQ]
    have hRR : ((doubledDoubledDoubledQuadPattern7 C P Q R R).choose
          (g a b c R) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b c R)
        = ((Nat.choose 2 c : ℝ)) * (-(d : ℝ)⁻¹) ^ c := by
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R R
          = 2 := by
        simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPR,
          Ne.symm hQR]
      have hgR : g a b c R = c := by
        simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false, if_true]
      rw [hpat, hgR]
    have hrest : ∀ S ∈ ((C.erase P).erase Q).erase R,
        ((doubledDoubledDoubledQuadPattern7 C P Q R S).choose
          (g a b c S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a b c S)
          = (-(d : ℝ)⁻¹) := by
      intro S hS
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSQ : S ≠ Q :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
      have hSP : S ≠ P :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).1
      have hSC : S ∈ C :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).2
      have hpat : doubledDoubledDoubledQuadPattern7 C P Q R S
          = 1 := by
        simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ, hSR,
          hSC]
      have hgS : g a b c S = 1 := by
        simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
      rw [hpat, hgS]; norm_num
    rw [hPP, hQQ, hRR, Finset.prod_congr rfl hrest,
      Finset.prod_const, Finset.card_erase_of_mem hR',
      Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 - 1 : ℕ) = 1 from rfl]
  have hF : ∀ a b c : ℕ,
      (∏ S ∈ C, realMoment ρ μG (g a b c S))
        = realMoment ρ μG a
          * (realMoment ρ μG b
            * (realMoment ρ μG c * e1 ρ μG)) := by
    intro a b c
    have hgP : g a b c P = a := by simp only [hg, if_true]
    have hgQ : g a b c Q = b := by
      simp only [hg, Ne.symm hPQ, if_false, if_true]
    have hgR : g a b c R = c := by
      simp only [hg, Ne.symm hPR, Ne.symm hQR, if_false, if_true]
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQ',
      ← Finset.mul_prod_erase ((C.erase P).erase Q) _ hR',
      hgP, hgQ, hgR]
    have hrest : ∀ S ∈ ((C.erase P).erase Q).erase R,
        realMoment ρ μG (g a b c S) = e1 ρ μG := by
      intro S hS
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSQ : S ≠ Q :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
      have hSP : S ≠ P :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).1
      have hSC : S ∈ C :=
        (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2).2
      have hgS : g a b c S = 1 := by
        simp only [hg, hSP, hSQ, hSR, hSC, if_false, if_true]
      rw [hgS, realMoment_one]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hR', Finset.card_erase_of_mem hQ',
      Finset.card_erase_of_mem hP, hC,
      show ((4 - 1) - 1 - 1 : ℕ) = 1 from rfl, pow_one]
  -- the eight moment identifications
  have hM111 : colReMomentPow ρ μG C (g 1 1 1) u u'
      = quadReMoment ρ μG C u u' := by
    have hcong : ∀ S ∈ C, g 1 1 1 S = (fun _ => 1) S := by
      intro S hSC
      rw [hgeval 1 1 1 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_one]
  have hM211 : colReMomentPow ρ μG C (g 2 1 1) u u'
      = doubledQuadReMoment ρ μG C P u u' := by
    have hcong : ∀ S ∈ C, g 2 1 1 S
        = (fun S => if S = P then 2 else 1) S := by
      intro S hSC
      rw [hgeval 2 1 1 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
  have hM121 : colReMomentPow ρ μG C (g 1 2 1) u u'
      = doubledQuadReMoment ρ μG C Q u u' := by
    have hcong : ∀ S ∈ C, g 1 2 1 S
        = (fun S => if S = Q then 2 else 1) S := by
      intro S hSC
      rw [hgeval 1 2 1 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hQ u u']
  have hM112 : colReMomentPow ρ μG C (g 1 1 2) u u'
      = doubledQuadReMoment ρ μG C R u u' := by
    have hcong : ∀ S ∈ C, g 1 1 2 S
        = (fun S => if S = R then 2 else 1) S := by
      intro S hSC
      rw [hgeval 1 1 2 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledQuadReMoment ρ μG C hR u u']
  have hM221 : colReMomentPow ρ μG C (g 2 2 1) u u'
      = doubledDoubledQuadReMoment ρ μG C P Q u u' := by
    have hcong : ∀ S ∈ C, g 2 2 1 S
        = (fun S => if S = P then 2 else if S = Q then 2
            else 1) S := by
      intro S hSC
      rw [hgeval 2 2 1 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C hP hQ
        (Ne.symm hPQ) u u']
  have hM212 : colReMomentPow ρ μG C (g 2 1 2) u u'
      = doubledDoubledQuadReMoment ρ μG C P R u u' := by
    have hcong : ∀ S ∈ C, g 2 1 2 S
        = (fun S => if S = P then 2 else if S = R then 2
            else 1) S := by
      intro S hSC
      rw [hgeval 2 1 2 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C hP hR
        (Ne.symm hPR) u u']
  have hM122 : colReMomentPow ρ μG C (g 1 2 2) u u'
      = doubledDoubledQuadReMoment ρ μG C Q R u u' := by
    have hcong : ∀ S ∈ C, g 1 2 2 S
        = (fun S => if S = Q then 2 else if S = R then 2
            else 1) S := by
      intro S hSC
      rw [hgeval 1 2 2 S hSC]
      by_cases hSP : S = P
      · simp only [hSP, hPQ, hPR, if_false, if_true]
      · by_cases hSQ : S = Q
        · simp only [hSQ, hSP, hPQ, hQR, Ne.symm hPQ, if_false,
            if_true]
        · by_cases hSR : S = R
          · simp only [hSR, hSP, hSQ, hPR, hQR, Ne.symm hPR,
              Ne.symm hQR, if_false, if_true]
          · simp only [hSP, hSQ, hSR, if_false, if_true]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C hQ hR
        (Ne.symm hQR) u u']
  have hM222 : colReMomentPow ρ μG C (g 2 2 2) u u'
      = doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u' := by
    have hcong : ∀ S ∈ C, g 2 2 2 S
        = doubledDoubledDoubledQuadPattern7 C P Q R S := by
      intro S hSC
      rw [hgeval 2 2 2 S hSC]
      by_cases hSP : S = P
      · rw [hSP]; simp [doubledDoubledDoubledQuadPattern7]
      · by_cases hSQ : S = Q
        · rw [hSQ]
          simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPQ]
        · by_cases hSR : S = R
          · rw [hSR]
            simp [doubledDoubledDoubledQuadPattern7, Ne.symm hPR,
              Ne.symm hQR]
          · simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ,
              hSR, hSC]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_doubledDoubledDoubledQuadPattern7 ρ μG C hP
        hQ hR (Ne.symm hPQ) (Ne.symm hPR) (Ne.symm hQR) u u']
  rw [hcoeff 1 1 1, hcoeff 2 1 1, hcoeff 1 2 1, hcoeff 1 1 2,
    hcoeff 2 2 1, hcoeff 2 1 2, hcoeff 1 2 2, hcoeff 2 2 2,
    hF 1 1 1, hF 2 1 1, hF 1 2 1, hF 1 1 2,
    hF 2 2 1, hF 2 1 2, hF 1 2 2, hF 2 2 2,
    hM111, hM211, hM121, hM112, hM221, hM212, hM122, hM222]
  norm_num [Nat.choose, realMoment_one]
  ring
/-- **The all-ones pattern value on a 4-support**:
`B⁴ + d⁻⁴` times the order-4 excess. The top sum is
the single fully-supported exponent choice. -/
theorem patternValue1111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 4) :
    ∫ α : LayerSite N → G,
        ∏ S ∈ D, (colDensC ρ u u' S α)
          ^ (fun S => if S ∈ D then 1 else 0) S
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 4) := by
  classical
  have hk0 : ∀ S ∉ D, (fun S => if S ∈ D then 1 else 0) S = 0 := by
    intro S hS; simp [hS]
  have hbase : ∏ S ∈ D, densMomentValue ρ μG
        ((fun S => if S ∈ D then 1 else 0) S)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    have hrest : ∀ S ∈ D, densMomentValue ρ μG
          ((fun S => if S ∈ D then 1 else 0) S)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro S hS
      have hval : (fun S => if S ∈ D then 1 else 0) S = 1 := by
        simp [hS]
      rw [hval, densMomentValue_one]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, hD]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' D _
    hk0, hbase]
  have hfilter : (Fintype.piFinset (fun S => Finset.range
        ((fun S => if S ∈ D then 1 else 0) S + 1))).filter
      (fun j => 4 ≤ (D.filter (fun S => j S ≠ 0)).card)
    = {(fun S => if S ∈ D then 1 else 0)} := by
    ext j
    simp only [Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_singleton]
    constructor
    · intro hj
      obtain ⟨hjpi, hjcard⟩ := hj
      have hsupp : D.filter (fun S => j S ≠ 0) = D := by
        apply Finset.eq_of_subset_of_card_le _ _
        · exact Finset.filter_subset _ _
        · rw [hD]; exact hjcard
      funext S
      by_cases hSD : S ∈ D
      · have hjne : j S ≠ 0 := by
          have hmem : S ∈ D.filter (fun S => j S ≠ 0) := by
            rw [hsupp]; exact hSD
          exact (Finset.mem_filter.mp hmem).2
        have hle : j S ≤ 1 := by
          have hlt := hjpi S
          rw [Finset.mem_range] at hlt
          simp only [hSD, if_true] at hlt
          omega
        show j S = (if S ∈ D then 1 else 0)
        rw [if_pos hSD]
        omega
      · have hle : j S ≤ 0 := by
          have hlt := hjpi S
          rw [Finset.mem_range] at hlt
          simp only [hSD, if_false] at hlt
          omega
        show j S = (if S ∈ D then 1 else 0)
        rw [if_neg hSD]
        omega
    · intro hj
      rw [hj]
      constructor
      · intro S
        rw [Finset.mem_range]
        show (if S ∈ D then 1 else 0)
          < (if S ∈ D then 1 else 0) + 1
        by_cases hSD : S ∈ D
        · rw [if_pos hSD]; norm_num
        · rw [if_neg hSD]; norm_num
      · have hsupp : D.filter (fun S =>
            (fun S => if S ∈ D then 1 else 0) S ≠ 0) = D := by
          refine Finset.filter_true_of_mem fun S hS => ?_
          show (if S ∈ D then 1 else 0) ≠ 0
          rw [if_pos hS]; norm_num
        simp [hsupp, hD]
  rw [hfilter, Finset.sum_singleton]
  have hcoeff : (∏ S ∈ D, (((fun S => if S ∈ D then 1 else 0) S).choose
        ((fun S => if S ∈ D then 1 else 0) S) : ℝ)
      * (-(d : ℝ)⁻¹) ^ ((fun S => if S ∈ D then 1 else 0) S))
    = (-(d : ℝ)⁻¹) ^ 4 := by
    have hrest : ∀ S ∈ D,
        (((fun S => if S ∈ D then 1 else 0) S).choose
          ((fun S => if S ∈ D then 1 else 0) S) : ℝ)
          * (-(d : ℝ)⁻¹) ^ ((fun S => if S ∈ D then 1 else 0) S)
          = (-(d : ℝ)⁻¹) := by
      intro S hS
      have hval : (fun S => if S ∈ D then 1 else 0) S = 1 := by
        simp [hS]
      rw [hval]; norm_num
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, hD]
  have hF : (∏ S ∈ D, realMoment ρ μG
      ((fun S => if S ∈ D then 1 else 0) S)) = (e1 ρ μG) ^ 4 := by
    have hrest : ∀ S ∈ D, realMoment ρ μG
          ((fun S => if S ∈ D then 1 else 0) S) = e1 ρ μG := by
      intro S hS
      have hval : (fun S => if S ∈ D then 1 else 0) S = 1 := by
        simp [hS]
      rw [hval, realMoment_one]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const, hD]
  have hM : colReMomentPow ρ μG D
        (fun S => if S ∈ D then 1 else 0) u u'
      = quadReMoment ρ μG D u u' := by
    have hcong : ∀ S ∈ D,
        (fun S => if S ∈ D then 1 else 0) S = (fun _ => 1) S := by
      intro S hS
      have hval : (fun S => if S ∈ D then 1 else 0) S = 1 := by
        simp [hS]
      rw [hval]
    rw [colReMomentPow_congr_on ρ μG hcong u u',
      colReMomentPow_one]
  rw [hcoeff, hF, hM]
  ring

/-- **The `(3,1,1,1,1)` pattern value on a 5-support.**
Baseline `A₃B⁴`, the three full-support excesses, the
all-ones erasure at `P`, and at each light column
the `(3,1,1,1)` erasure. -/
theorem patternValue31111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ S ∈ C, (colDensC ρ u u' S α)
          ^ (tripledQuintuplePattern C P S)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)) := by
  classical
  have hk0 : ∀ S ∉ C, tripledQuintuplePattern C P S = 0 := by
    intro S hS
    have hSP : S ≠ P := fun h => hS (h ▸ hP)
    simp [tripledQuintuplePattern, hSP, hS]
  have hbase : ∏ S ∈ C, densMomentValue ρ μG
        (tripledQuintuplePattern C P S)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
    rw [← Finset.mul_prod_erase C _ hP]
    have hPP : densMomentValue ρ μG (tripledQuintuplePattern C P P)
        = densMomentValue ρ μG 3 := by
      congr 1; simp [tripledQuintuplePattern]
    have hrest : ∀ S ∈ C.erase P,
        densMomentValue ρ μG (tripledQuintuplePattern C P S)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro S hS
      have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      have hpat : tripledQuintuplePattern C P S = 1 := by
        simp [tripledQuintuplePattern, hSP, hSC]
      rw [hpat, densMomentValue_one]
    rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
      Finset.card_erase_of_mem hP, hC, show (5 - 1 : ℕ) = 4 from rfl]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' C _
    hk0, hbase, topSum_card5_split ρ μG
    (tripledQuintuplePattern C P) C hC u u']
  -- full-support part: bijection to `Icc 1 3`
  set g : ℕ → LayerColumn N → ℕ := fun a S =>
    if S = P then a else if S ∈ C then 1 else 0 with hg
  have hfull : (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (tripledQuintuplePattern C P S + 1))).filter
        (fun j => (C.filter (fun S => j S ≠ 0)) = C),
      (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4) := by
    have hmem : ∀ a ∈ Finset.Icc 1 3,
        g a ∈ (Fintype.piFinset (fun S => Finset.range
            (tripledQuintuplePattern C P S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C) := by
      intro a ha
      obtain ⟨ha1, ha3⟩ := Finset.mem_Icc.mp ha
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · intro S
        rw [Finset.mem_range]
        by_cases hSP : S = P
        · rw [hSP]
          have hpat : tripledQuintuplePattern C P P = 3 := by
            simp [tripledQuintuplePattern]
          rw [hpat]
          show g a P < 3 + 1
          simp only [hg, if_true]
          omega
        · by_cases hSC : S ∈ C
          · have hpat : tripledQuintuplePattern C P S = 1 := by
              simp [tripledQuintuplePattern, hSP, hSC]
            rw [hpat]
            show g a S < 1 + 1
            simp only [hg, hSP, hSC, if_false, if_true]
            omega
          · have hpat : tripledQuintuplePattern C P S = 0 :=
              hk0 S hSC
            rw [hpat]
            show g a S < 0 + 1
            simp only [hg, hSP, hSC, if_false]
            omega
      · have hfilt : C.filter (fun S => g a S ≠ 0) = C := by
          refine Finset.filter_true_of_mem fun S hSC => ?_
          by_cases hSP : S = P
          · rw [hSP]; simp only [hg, if_true]; omega
          · simp only [hg, hSP, hSC, if_false, if_true]
            norm_num
        rw [hfilt]
    have hinj : ∀ a₁ ∈ Finset.Icc 1 3, ∀ a₂ ∈ Finset.Icc 1 3,
        g a₁ = g a₂ → a₁ = a₂ := by
      intro a₁ _ a₂ _ h
      have h1 : g a₁ P = a₁ := by simp only [hg, if_true]
      have h2 : g a₂ P = a₂ := by simp only [hg, if_true]
      rw [← h1, ← h2, h]
    have hsurj : ∀ j ∈ (Fintype.piFinset (fun S => Finset.range
            (tripledQuintuplePattern C P S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C),
        ∃ a, ∃ _ : a ∈ Finset.Icc 1 3, g a = j := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjpi, hjfilt⟩ := hj
      have hjpi' := Fintype.mem_piFinset.mp hjpi
      have hjne : ∀ S ∈ C, j S ≠ 0 := by
        intro S hSC
        have hmem : S ∈ C.filter (fun S => j S ≠ 0) := by
          rw [hjfilt]; exact hSC
        exact (Finset.mem_filter.mp hmem).2
      have hbound : ∀ S, j S ≤ tripledQuintuplePattern C P S := by
        intro S
        have hlt := hjpi' S
        rw [Finset.mem_range] at hlt; omega
      have hP3 : j P ≤ 3 := by
        have hpat : tripledQuintuplePattern C P P = 3 := by
          simp [tripledQuintuplePattern]
        have h := hbound P; rwa [hpat] at h
      refine ⟨j P, Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (hjne P hP), hP3⟩, ?_⟩
      show g (j P) = j
      funext S
      by_cases hSP : S = P
      · rw [hSP]; simp only [hg, if_true]
      · by_cases hSC : S ∈ C
        · have hpat : tripledQuintuplePattern C P S = 1 := by
            simp [tripledQuintuplePattern, hSP, hSC]
          have hjS : j S = 1 := by
            have hb := hbound S; rw [hpat] at hb
            have hne := hjne S hSC; omega
          simp only [hg, hSP, hSC, if_false, if_true]
          exact hjS.symm
        · have hpat : tripledQuintuplePattern C P S = 0 :=
            hk0 S hSC
          have hjS : j S = 0 := by
            have hb := hbound S; rw [hpat] at hb; omega
          simp only [hg, hSP, hSC, if_false]
          exact hjS.symm
    have htop : (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
            (tripledQuintuplePattern C P S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C),
        (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
            (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
          * (colReMomentPow ρ μG C j u u'
            - ∏ S ∈ C, realMoment ρ μG (j S)))
      = ∑ a ∈ Finset.Icc 1 3,
        (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
            (g a S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a S))
          * (colReMomentPow ρ μG C (g a) u u'
            - ∏ S ∈ C, realMoment ρ μG (g a S)) :=
      (Finset.sum_bij (fun a _ => g a) hmem hinj hsurj
        (fun a _ => rfl)).symm
    rw [htop, sum_Icc_one_three]
    have hcoeff : ∀ a : ℕ,
        (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
            (g a S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a S))
          = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a
            * (-(d : ℝ)⁻¹) ^ 4 := by
      intro a
      rw [← Finset.mul_prod_erase C _ hP]
      have hPP : ((tripledQuintuplePattern C P P).choose
            (g a P) : ℝ) * (-(d : ℝ)⁻¹) ^ (g a P)
          = ((Nat.choose 3 a : ℝ)) * (-(d : ℝ)⁻¹) ^ a := by
        have hpat : tripledQuintuplePattern C P P = 3 := by
          simp [tripledQuintuplePattern]
        have hgP : g a P = a := by simp only [hg, if_true]
        rw [hpat, hgP]
      have hrest : ∀ S ∈ C.erase P,
          ((tripledQuintuplePattern C P S).choose (g a S) : ℝ)
            * (-(d : ℝ)⁻¹) ^ (g a S) = (-(d : ℝ)⁻¹) := by
        intro S hS
        have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
        have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
        have hpat : tripledQuintuplePattern C P S = 1 := by
          simp [tripledQuintuplePattern, hSP, hSC]
        have hgS : g a S = 1 := by
          simp only [hg, hSP, hSC, if_false, if_true]
        rw [hpat, hgS]; norm_num
      rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hP, hC,
        show (5 - 1 : ℕ) = 4 from rfl]
    have hF : ∀ a : ℕ,
        (∏ S ∈ C, realMoment ρ μG (g a S))
          = realMoment ρ μG a * (e1 ρ μG) ^ 4 := by
      intro a
      have hgP : g a P = a := by simp only [hg, if_true]
      rw [← Finset.mul_prod_erase C _ hP, hgP]
      have hrest : ∀ S ∈ C.erase P,
          realMoment ρ μG (g a S) = e1 ρ μG := by
        intro S hS
        have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
        have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
        have hgS : g a S = 1 := by
          simp only [hg, hSP, hSC, if_false, if_true]
        rw [hgS, realMoment_one]
      rw [Finset.prod_congr rfl hrest, Finset.prod_const,
        Finset.card_erase_of_mem hP, hC,
        show (5 - 1 : ℕ) = 4 from rfl]
    have hgeval : ∀ (a : ℕ) (S : LayerColumn N), S ∈ C →
        g a S = if S = P then a else 1 := by
      intro a S hSC
      by_cases hSP : S = P
      · rw [hSP]; simp only [hg, if_true]
      · simp only [hg, hSP, hSC, if_false, if_true]
    have hM1 : colReMomentPow ρ μG C (g 1) u u'
        = quadReMoment ρ μG C u u' := by
      have hcong : ∀ S ∈ C, g 1 S = (fun _ => 1) S := by
        intro S hSC
        rw [hgeval 1 S hSC]
        by_cases hSP : S = P
        · simp only [hSP, if_true]
        · simp only [hSP, if_false]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_one]
    have hM2 : colReMomentPow ρ μG C (g 2) u u'
        = doubledQuadReMoment ρ μG C P u u' := by
      have hcong : ∀ S ∈ C, g 2 S
          = (fun S => if S = P then 2 else 1) S := by
        intro S hSC
        rw [hgeval 2 S hSC]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
    have hM3 : colReMomentPow ρ μG C (g 3) u u'
        = tripledQuadReMoment ρ μG C P u u' := by
      have hcong : ∀ S ∈ C, g 3 S
          = (fun S => if S = P then 3 else 1) S := by
        intro S hSC
        rw [hgeval 3 S hSC]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_tripledQuadReMoment ρ μG C hP u u']
    rw [hcoeff 1, hcoeff 2, hcoeff 3, hF 1, hF 2, hF 3,
      hM1, hM2, hM3]
    norm_num [Nat.choose, realMoment_one]
    ring
  rw [hfull, ← Finset.sum_erase_add _ _ hP]
  -- the piece at `P` is split off; the lights remain
  -- piece at `P`: the all-ones value on `C.erase P`
  have hpieceP : (∑ j ∈ (Fintype.piFinset
        (fun S => Finset.range
          (tripledQuintuplePattern C P S + 1))).filter
        (fun j => j P = 0 ∧ (C.erase P).filter
          (fun S => j S ≠ 0) = C.erase P),
      (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase P) u u'
          - (e1 ρ μG) ^ 4) := by
    have hcardD : (C.erase P).card = 4 := by
      rw [Finset.card_erase_of_mem hP, hC]
    rw [pieceSum_eq_topSum_erase ρ μG
      (tripledQuintuplePattern C P) C hC hP u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase P)
      (fun S => if S = P then 0 else tripledQuintuplePattern C P S)
      (by intro S hS
          by_cases hSP : S = P
          · rw [hSP]; simp
          · rw [if_neg hSP]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSP, h⟩)))
    have hval : ∀ S ∈ C.erase P,
        (fun S => if S = P then 0
          else tripledQuintuplePattern C P S) S
          = (fun S => if S ∈ C.erase P then 1 else 0) S := by
      intro S hS
      have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      simp [tripledQuintuplePattern, hSP, hSC, hS]
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase P, (colDensC ρ u u' S α)
            ^ ((fun S => if S = P then 0
              else tripledQuintuplePattern C P S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase P, (colDensC ρ u u' S α)
            ^ (fun S => if S ∈ C.erase P then 1 else 0) S
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      exact Finset.prod_congr rfl fun S hS => by rw [hval S hS]
    have hbaseE : (∏ S ∈ C.erase P, densMomentValue ρ μG
          ((fun S => if S = P then 0
            else tripledQuintuplePattern C P S) S))
        = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
      have hvalD : ∀ S ∈ C.erase P,
          densMomentValue ρ μG
            ((fun S => if S = P then 0
              else tripledQuintuplePattern C P S) S)
            = densMomentValue ρ μG
              ((fun S => if S ∈ C.erase P then 1 else 0) S) :=
        fun S hS => by rw [hval S hS]
      rw [Finset.prod_congr rfl hvalD]
      have hrest : ∀ S ∈ C.erase P, densMomentValue ρ μG
            ((fun S => if S ∈ C.erase P then 1 else 0) S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hval2 : (fun S => if S ∈ C.erase P then 1 else 0) S
            = 1 := by
          simp [hS]
        rw [hval2, densMomentValue_one]
      rw [Finset.prod_congr rfl hrest, Finset.prod_const, hcardD]
    rw [hint, hbaseE,
      patternValue1111 ρ μG hN hN3 hρcont u u' (C.erase P) hcardD]
      at hgen
    linarith
  rw [hpieceP]
  -- pieces at light columns: the `(3,1,1,1)` value on `C.erase R`
  have hpieceR : ∀ R ∈ C.erase P,
      (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (tripledQuintuplePattern C P S + 1))).filter
        (fun j => j R = 0 ∧ (C.erase R).filter
          (fun S => j S ≠ 0) = C.erase R),
      (∏ S ∈ C, ((tripledQuintuplePattern C P S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = 3 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4)
      - 3 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      + ((d : ℝ)⁻¹) ^ 6
        * (tripledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    intro R hR
    have hRP : R ≠ P := (Finset.mem_erase.mp hR).1
    have hRC : R ∈ C := (Finset.mem_erase.mp hR).2
    have hP' : P ∈ C.erase R :=
      Finset.mem_erase.mpr ⟨Ne.symm hRP, hP⟩
    have hcardR : (C.erase R).card = 4 := by
      rw [Finset.card_erase_of_mem hRC, hC]
    rw [pieceSum_eq_topSum_erase ρ μG
      (tripledQuintuplePattern C P) C hC hRC u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase R)
      (fun S => if S = R then 0 else tripledQuintuplePattern C P S)
      (by intro S hS
          by_cases hSR : S = R
          · rw [hSR]; simp
          · rw [if_neg hSR]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSR, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ ((fun S => if S = R then 0
              else tripledQuintuplePattern C P S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ (if S = P then 3 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun S hS => ?_
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      congr 1
      by_cases hSP : S = P
      · rw [hSP]
        simp [tripledQuintuplePattern, Ne.symm hRP]
      · simp [tripledQuintuplePattern, hSR, hSP, hSC]
    have hbaseE : (∏ S ∈ C.erase R, densMomentValue ρ μG
          ((fun S => if S = R then 0
            else tripledQuintuplePattern C P S) S))
        = densMomentValue ρ μG 3
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
      rw [← Finset.mul_prod_erase (C.erase R) _ hP']
      have hPP : densMomentValue ρ μG
            ((fun S => if S = R then 0
              else tripledQuintuplePattern C P S) P)
          = densMomentValue ρ μG 3 := by
        congr 1
        simp [tripledQuintuplePattern, Ne.symm hRP]
      have hrest : ∀ S ∈ (C.erase R).erase P,
          densMomentValue ρ μG
            ((fun S => if S = R then 0
              else tripledQuintuplePattern C P S) S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
        have hSR : S ≠ R :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hval : (fun S => if S = R then 0
              else tripledQuintuplePattern C P S) S = 1 := by
          simp [tripledQuintuplePattern, hSR, hSP, hSC]
        rw [hval, densMomentValue_one]
      have hcardRP : ((C.erase R).erase P).card = 3 := by
        rw [Finset.card_erase_of_mem hP', hcardR]
      rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
        hcardRP]
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_tripled ρ μG hN hN3 hρcont u u'
        (C.erase R) hcardR P hP'] at hgen
    linarith
  rw [Finset.sum_congr rfl hpieceR]
  ring
/-- **The `(2,2,1,1,1)` pattern value on a 5-support.**
Baseline `A₂²B³`, the four full-support excesses, the
doubled erasures at `P` and `Q`, and at each light
column the `(2,2,1,1)` erasure. -/
theorem patternValue22111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) (P Q : LayerColumn N)
    (hP : P ∈ C) (hQ : Q ∈ C) (hQP : Q ≠ P) :
    ∫ α : LayerSite N → G,
        ∏ S ∈ C, (colDensC ρ u u' S α)
          ^ (doubledDoubledQuintuplePattern C P Q S)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
  classical
  have hk0 : ∀ S ∉ C, doubledDoubledQuintuplePattern C P Q S
      = 0 := by
    intro S hS
    have hSP : S ≠ P := fun h => hS (h ▸ hP)
    have hSQ : S ≠ Q := fun h => hS (h ▸ hQ)
    simp [doubledDoubledQuintuplePattern, hSP, hSQ, hS]
  have hQeP : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQ⟩
  have hbase : ∏ S ∈ C, densMomentValue ρ μG
        (doubledDoubledQuintuplePattern C P Q S)
      = densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3) := by
    rw [← Finset.mul_prod_erase C _ hP,
      ← Finset.mul_prod_erase (C.erase P) _ hQeP]
    have hPP : densMomentValue ρ μG
          (doubledDoubledQuintuplePattern C P Q P)
        = densMomentValue ρ μG 2 := by
      congr 1; simp [doubledDoubledQuintuplePattern]
    have hQQ : densMomentValue ρ μG
          (doubledDoubledQuintuplePattern C P Q Q)
        = densMomentValue ρ μG 2 := by
      congr 1; simp [doubledDoubledQuintuplePattern, hQP]
    have hrest : ∀ S ∈ (C.erase P).erase Q,
        densMomentValue ρ μG
          (doubledDoubledQuintuplePattern C P Q S)
          = 1 - e1 ρ μG / (d : ℝ) := by
      intro S hS
      have hSP : S ≠ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
      have hSC : S ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
      have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
      have hpat : doubledDoubledQuintuplePattern C P Q S = 1 := by
        simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
      rw [hpat, densMomentValue_one]
    have hcardPP : ((C.erase P).erase Q).card = 3 := by
      rw [Finset.card_erase_of_mem hQeP,
        Finset.card_erase_of_mem hP, hC,
        show (5 - 1 : ℕ) = 4 from rfl,
        show (4 - 1 : ℕ) = 3 from rfl]
    rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
      hcardPP]
  rw [patternValue_eq_baseline_add_top ρ μG hN hN3 hρcont u u' C _
    hk0, hbase, topSum_card5_split ρ μG
    (doubledDoubledQuintuplePattern C P Q) C hC u u']
  -- full-support part: bijection to `(Icc 1 2) ×ˢ (Icc 1 2)`
  set g : ℕ × ℕ → LayerColumn N → ℕ := fun p S =>
    if S = P then p.1 else if S = Q then p.2
    else if S ∈ C then 1 else 0 with hg
  have hfull : (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (doubledDoubledQuintuplePattern C P Q S + 1))).filter
        (fun j => (C.filter (fun S => j S ≠ 0)) = C),
      (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3) := by
    have hmem : ∀ p ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2,
        g p ∈ (Fintype.piFinset (fun S => Finset.range
            (doubledDoubledQuintuplePattern C P Q S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hp11, hp12⟩ := Finset.mem_Icc.mp hp1
      obtain ⟨hp21, hp22⟩ := Finset.mem_Icc.mp hp2
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · intro S
        rw [Finset.mem_range]
        by_cases hSP : S = P
        · rw [hSP]
          have hpat : doubledDoubledQuintuplePattern C P Q P
              = 2 := by
            simp [doubledDoubledQuintuplePattern]
          rw [hpat]
          show g p P < 2 + 1
          simp only [hg, if_true]
          omega
        · by_cases hSQ : S = Q
          · rw [hSQ]
            have hpat : doubledDoubledQuintuplePattern C P Q Q
                = 2 := by
              simp [doubledDoubledQuintuplePattern, hQP]
            rw [hpat]
            show g p Q < 2 + 1
            simp only [hg, hQP, if_false, if_true]
            omega
          · by_cases hSC : S ∈ C
            · have hpat : doubledDoubledQuintuplePattern C P Q S
                  = 1 := by
                simp [doubledDoubledQuintuplePattern, hSP, hSQ,
                  hSC]
              rw [hpat]
              show g p S < 1 + 1
              simp only [hg, hSP, hSQ, hSC, if_false, if_true]
              omega
            · have hpat : doubledDoubledQuintuplePattern C P Q S
                  = 0 := hk0 S hSC
              rw [hpat]
              show g p S < 0 + 1
              simp only [hg, hSP, hSQ, hSC, if_false]
              omega
      · have hfilt : C.filter (fun S => g p S ≠ 0) = C := by
          refine Finset.filter_true_of_mem fun S hSC => ?_
          by_cases hSP : S = P
          · rw [hSP]; simp only [hg, if_true]; omega
          · by_cases hSQ : S = Q
            · rw [hSQ]
              simp only [hg, hQP, if_false, if_true]; omega
            · simp only [hg, hSP, hSQ, hSC, if_false, if_true]
              norm_num
        rw [hfilt]
    have hinj : ∀ p₁ ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2,
        ∀ p₂ ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2,
        g p₁ = g p₂ → p₁ = p₂ := by
      intro p₁ _ p₂ _ h
      have h1 : g p₁ P = p₁.1 := by simp only [hg, if_true]
      have h2 : g p₂ P = p₂.1 := by simp only [hg, if_true]
      have h3 : g p₁ Q = p₁.2 := by
        simp only [hg, hQP, if_false, if_true]
      have h4 : g p₂ Q = p₂.2 := by
        simp only [hg, hQP, if_false, if_true]
      have e1 : p₁.1 = p₂.1 := by rw [← h1, ← h2, h]
      have e2 : p₁.2 = p₂.2 := by rw [← h3, ← h4, h]
      exact Prod.ext e1 e2
    have hsurj : ∀ j ∈ (Fintype.piFinset (fun S => Finset.range
            (doubledDoubledQuintuplePattern C P Q S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C),
        ∃ p, ∃ _ : p ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2,
          g p = j := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjpi, hjfilt⟩ := hj
      have hjpi' := Fintype.mem_piFinset.mp hjpi
      have hjne : ∀ S ∈ C, j S ≠ 0 := by
        intro S hSC
        have hmem : S ∈ C.filter (fun S => j S ≠ 0) := by
          rw [hjfilt]; exact hSC
        exact (Finset.mem_filter.mp hmem).2
      have hbound : ∀ S, j S
          ≤ doubledDoubledQuintuplePattern C P Q S := by
        intro S
        have hlt := hjpi' S
        rw [Finset.mem_range] at hlt; omega
      have hP2 : j P ≤ 2 := by
        have hpat : doubledDoubledQuintuplePattern C P Q P = 2 := by
          simp [doubledDoubledQuintuplePattern]
        have h := hbound P; rwa [hpat] at h
      have hQ2 : j Q ≤ 2 := by
        have hpat : doubledDoubledQuintuplePattern C P Q Q = 2 := by
          simp [doubledDoubledQuintuplePattern, hQP]
        have h := hbound Q; rwa [hpat] at h
      refine ⟨(j P, j Q), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (hjne P hP), hP2⟩,
         Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (hjne Q hQ), hQ2⟩⟩, ?_⟩
      show g (j P, j Q) = j
      funext S
      by_cases hSP : S = P
      · rw [hSP]; simp only [hg, if_true]
      · by_cases hSQ : S = Q
        · rw [hSQ]; simp only [hg, hQP, if_false, if_true]
        · by_cases hSC : S ∈ C
          · have hpat : doubledDoubledQuintuplePattern C P Q S
                = 1 := by
              simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
            have hjS : j S = 1 := by
              have hb := hbound S; rw [hpat] at hb
              have hne := hjne S hSC; omega
            simp only [hg, hSP, hSQ, hSC, if_false, if_true]
            exact hjS.symm
          · have hpat : doubledDoubledQuintuplePattern C P Q S
                = 0 := hk0 S hSC
            have hjS : j S = 0 := by
              have hb := hbound S; rw [hpat] at hb; omega
            simp only [hg, hSP, hSQ, hSC, if_false]
            exact hjS.symm
    have htop : (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
            (doubledDoubledQuintuplePattern C P Q S + 1))).filter
          (fun j => (C.filter (fun S => j S ≠ 0)) = C),
        (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
            (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
          * (colReMomentPow ρ μG C j u u'
            - ∏ S ∈ C, realMoment ρ μG (j S)))
      = ∑ p ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2,
        (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
            (g p S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p S))
          * (colReMomentPow ρ μG C (g p) u u'
            - ∏ S ∈ C, realMoment ρ μG (g p S)) :=
      (Finset.sum_bij (fun p _ => g p) hmem hinj hsurj
        (fun p _ => rfl)).symm
    rw [htop, Finset.sum_product]
    simp only [sum_Icc_one_two]
    have hcoeff : ∀ p : ℕ × ℕ,
        (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
            (g p S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p S))
          = ((Nat.choose 2 p.1 : ℝ)) * (-(d : ℝ)⁻¹) ^ p.1
            * (((Nat.choose 2 p.2 : ℝ)) * (-(d : ℝ)⁻¹) ^ p.2
              * (-(d : ℝ)⁻¹) ^ 3) := by
      intro p
      rw [← Finset.mul_prod_erase C _ hP,
        ← Finset.mul_prod_erase (C.erase P) _ hQeP]
      have hPP : ((doubledDoubledQuintuplePattern C P Q P).choose
            (g p P) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p P)
          = ((Nat.choose 2 p.1 : ℝ)) * (-(d : ℝ)⁻¹) ^ p.1 := by
        have hpat : doubledDoubledQuintuplePattern C P Q P
            = 2 := by
          simp [doubledDoubledQuintuplePattern]
        have hgP : g p P = p.1 := by simp only [hg, if_true]
        rw [hpat, hgP]
      have hQQ : ((doubledDoubledQuintuplePattern C P Q Q).choose
            (g p Q) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p Q)
          = ((Nat.choose 2 p.2 : ℝ)) * (-(d : ℝ)⁻¹) ^ p.2 := by
        have hpat : doubledDoubledQuintuplePattern C P Q Q
            = 2 := by
          simp [doubledDoubledQuintuplePattern, hQP]
        have hgQ : g p Q = p.2 := by
          simp only [hg, hQP, if_false, if_true]
        rw [hpat, hgQ]
      have hrest : ∀ S ∈ (C.erase P).erase Q,
          ((doubledDoubledQuintuplePattern C P Q S).choose
              (g p S) : ℝ) * (-(d : ℝ)⁻¹) ^ (g p S)
            = (-(d : ℝ)⁻¹) := by
        intro S hS
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
        have hpat : doubledDoubledQuintuplePattern C P Q S
            = 1 := by
          simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
        have hgS : g p S = 1 := by
          simp only [hg, hSP, hSQ, hSC, if_false, if_true]
        rw [hpat, hgS]; norm_num
      have hcardPP : ((C.erase P).erase Q).card = 3 := by
        rw [Finset.card_erase_of_mem hQeP,
          Finset.card_erase_of_mem hP, hC,
          show (5 - 1 : ℕ) = 4 from rfl,
          show (4 - 1 : ℕ) = 3 from rfl]
      rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        hcardPP]
    have hF : ∀ p : ℕ × ℕ,
        (∏ S ∈ C, realMoment ρ μG (g p S))
          = realMoment ρ μG p.1
            * (realMoment ρ μG p.2 * (e1 ρ μG) ^ 3) := by
      intro p
      have hgP : g p P = p.1 := by simp only [hg, if_true]
      have hgQ : g p Q = p.2 := by
        simp only [hg, hQP, if_false, if_true]
      rw [← Finset.mul_prod_erase C _ hP, hgP,
        ← Finset.mul_prod_erase (C.erase P) _ hQeP, hgQ]
      have hrest : ∀ S ∈ (C.erase P).erase Q,
          realMoment ρ μG (g p S) = e1 ρ μG := by
        intro S hS
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
        have hgS : g p S = 1 := by
          simp only [hg, hSP, hSQ, hSC, if_false, if_true]
        rw [hgS, realMoment_one]
      have hcardPP : ((C.erase P).erase Q).card = 3 := by
        rw [Finset.card_erase_of_mem hQeP,
          Finset.card_erase_of_mem hP, hC,
          show (5 - 1 : ℕ) = 4 from rfl,
          show (4 - 1 : ℕ) = 3 from rfl]
      rw [Finset.prod_congr rfl hrest, Finset.prod_const, hcardPP]
    have hgeval : ∀ (p : ℕ × ℕ) (S : LayerColumn N), S ∈ C →
        g p S = if S = P then p.1 else if S = Q then p.2 else 1 := by
      intro p S hSC
      by_cases hSP : S = P
      · rw [hSP]; simp only [hg, if_true]
      · by_cases hSQ : S = Q
        · rw [hSQ]; simp only [hg, hQP, if_false, if_true]
        · simp only [hg, hSP, hSQ, hSC, if_false, if_true]
    have hM11 : colReMomentPow ρ μG C (g (1, 1)) u u'
        = quadReMoment ρ μG C u u' := by
      have hcong : ∀ S ∈ C, g (1, 1) S = (fun _ => 1) S := by
        intro S hSC
        rw [hgeval (1, 1) S hSC]
        by_cases hSP : S = P
        · simp only [hSP, if_true]
        · by_cases hSQ : S = Q
          · simp only [hSP, hSQ, hQP, if_false, if_true]
          · simp only [hSP, hSQ, if_false]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_one]
    have hM21 : colReMomentPow ρ μG C (g (2, 1)) u u'
        = doubledQuadReMoment ρ μG C P u u' := by
      have hcong : ∀ S ∈ C, g (2, 1) S
          = (fun S => if S = P then 2 else 1) S := by
        intro S hSC
        rw [hgeval (2, 1) S hSC]
        by_cases hSP : S = P
        · simp only [hSP, if_true]
        · by_cases hSQ : S = Q
          · simp only [hSP, hSQ, if_false, if_true]
          · simp only [hSP, hSQ, if_false]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledQuadReMoment ρ μG C hP u u']
    have hM12 : colReMomentPow ρ μG C (g (1, 2)) u u'
        = doubledQuadReMoment ρ μG C Q u u' := by
      have hcong : ∀ S ∈ C, g (1, 2) S
          = (fun S => if S = Q then 2 else 1) S := by
        intro S hSC
        rw [hgeval (1, 2) S hSC]
        by_cases hSP : S = P
        · rw [hSP]
          have hPQ : ¬ (P = Q) := Ne.symm hQP
          simp only [if_true, hPQ, if_false]
        · simp only [hSP, if_false]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledQuadReMoment ρ μG C hQ u u']
    have hM22 : colReMomentPow ρ μG C (g (2, 2)) u u'
        = doubledDoubledQuadReMoment ρ μG C P Q u u' := by
      have hcong : ∀ S ∈ C, g (2, 2) S
          = (fun S => if S = P then 2 else if S = Q then 2
              else 1) S := by
        intro S hSC
        rw [hgeval (2, 2) S hSC]
      rw [colReMomentPow_congr_on ρ μG hcong u u',
        colReMomentPow_eq_doubledDoubledQuadReMoment ρ μG C
          hP hQ hQP u u']
    rw [hcoeff (1, 1), hcoeff (1, 2), hcoeff (2, 1), hcoeff (2, 2),
      hF (1, 1), hF (1, 2), hF (2, 1), hF (2, 2),
      hM11, hM12, hM21, hM22]
    norm_num [Nat.choose, realMoment_one]
    ring
  rw [hfull, ← Finset.sum_erase_add _ _ hP]
  -- the piece at `P` is split off; `Q` and the lights remain
  -- piece at `P`: the doubled value at `Q` on `C.erase P`
  have hpieceP : (∑ j ∈ (Fintype.piFinset
        (fun S => Finset.range
          (doubledDoubledQuintuplePattern C P Q S + 1))).filter
        (fun j => j P = 0 ∧ (C.erase P).filter
          (fun S => j S ≠ 0) = C.erase P),
      (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = 2 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
      - ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    have hcardP : (C.erase P).card = 4 := by
      rw [Finset.card_erase_of_mem hP, hC]
    rw [pieceSum_eq_topSum_erase ρ μG
      (doubledDoubledQuintuplePattern C P Q) C hC hP u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase P)
      (fun S => if S = P then 0
        else doubledDoubledQuintuplePattern C P Q S)
      (by intro S hS
          by_cases hSP : S = P
          · rw [hSP]; simp
          · rw [if_neg hSP]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSP, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase P, (colDensC ρ u u' S α)
            ^ ((fun S => if S = P then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase P, (colDensC ρ u u' S α)
            ^ (if S = Q then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun S hS => ?_
      have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      congr 1
      by_cases hSQ : S = Q
      · rw [hSQ]
        simp [doubledDoubledQuintuplePattern, hQP, hSP]
      · simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
    have hbaseE : (∏ S ∈ C.erase P, densMomentValue ρ μG
          ((fun S => if S = P then 0
            else doubledDoubledQuintuplePattern C P Q S) S))
        = densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
      rw [← Finset.mul_prod_erase (C.erase P) _ hQeP]
      have hQQ : densMomentValue ρ μG
            ((fun S => if S = P then 0
              else doubledDoubledQuintuplePattern C P Q S) Q)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [doubledDoubledQuintuplePattern, hQP]
      have hrest : ∀ S ∈ (C.erase P).erase Q,
          densMomentValue ρ μG
            ((fun S => if S = P then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
        have hval : (fun S => if S = P then 0
              else doubledDoubledQuintuplePattern C P Q S) S
            = 1 := by
          simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
        rw [hval, densMomentValue_one]
      have hcardPQ : ((C.erase P).erase Q).card = 3 := by
        rw [Finset.card_erase_of_mem hQeP, hcardP,
          show (4 - 1 : ℕ) = 3 from rfl]
      rw [hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        hcardPQ]
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_doubled ρ μG hN hN3 hρcont
        u u' (C.erase P) hcardP Q hQeP] at hgen
    linarith
  rw [hpieceP, ← Finset.sum_erase_add _ _ hQeP]
  -- piece at `Q`: the doubled value at `P` on `C.erase Q`
  have hPeQ : P ∈ C.erase Q :=
    Finset.mem_erase.mpr ⟨Ne.symm hQP, hP⟩
  have hpieceQ : (∑ j ∈ (Fintype.piFinset
        (fun S => Finset.range
          (doubledDoubledQuintuplePattern C P Q S + 1))).filter
        (fun j => j Q = 0 ∧ (C.erase Q).filter
          (fun S => j S ≠ 0) = C.erase Q),
      (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = 2 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase Q) u u' - (e1 ρ μG) ^ 4)
      - ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    have hcardQ : (C.erase Q).card = 4 := by
      rw [Finset.card_erase_of_mem hQ, hC]
    rw [pieceSum_eq_topSum_erase ρ μG
      (doubledDoubledQuintuplePattern C P Q) C hC hQ u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase Q)
      (fun S => if S = Q then 0
        else doubledDoubledQuintuplePattern C P Q S)
      (by intro S hS
          by_cases hSQ : S = Q
          · rw [hSQ]; simp
          · rw [if_neg hSQ]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSQ, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase Q, (colDensC ρ u u' S α)
            ^ ((fun S => if S = Q then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase Q, (colDensC ρ u u' S α)
            ^ (if S = P then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun S hS => ?_
      have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      congr 1
      by_cases hSP : S = P
      · rw [hSP]
        simp [doubledDoubledQuintuplePattern, Ne.symm hQP]
      · simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
    have hbaseE : (∏ S ∈ C.erase Q, densMomentValue ρ μG
          ((fun S => if S = Q then 0
            else doubledDoubledQuintuplePattern C P Q S) S))
        = densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
      rw [← Finset.mul_prod_erase (C.erase Q) _ hPeQ]
      have hPP : densMomentValue ρ μG
            ((fun S => if S = Q then 0
              else doubledDoubledQuintuplePattern C P Q S) P)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [doubledDoubledQuintuplePattern, Ne.symm hQP]
      have hrest : ∀ S ∈ (C.erase Q).erase P,
          densMomentValue ρ μG
            ((fun S => if S = Q then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hSQ : S ≠ Q :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hSP : S ≠ P := (Finset.mem_erase.mp hS).1
        have hval : (fun S => if S = Q then 0
              else doubledDoubledQuintuplePattern C P Q S) S
            = 1 := by
          simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC]
        rw [hval, densMomentValue_one]
      have hcardQP : ((C.erase Q).erase P).card = 3 := by
        rw [Finset.card_erase_of_mem hPeQ, hcardQ,
          show (4 - 1 : ℕ) = 3 from rfl]
      rw [hPP, Finset.prod_congr rfl hrest, Finset.prod_const,
        hcardQP]
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_doubled ρ μG hN hN3 hρcont
        u u' (C.erase Q) hcardQ P hPeQ] at hgen
    linarith
  rw [hpieceQ]
  -- pieces at light columns: the `(2,2,1,1)` value on `C.erase R`
  have hpieceR : ∀ R ∈ (C.erase P).erase Q,
      (∑ j ∈ (Fintype.piFinset (fun S => Finset.range
          (doubledDoubledQuintuplePattern C P Q S + 1))).filter
        (fun j => j R = 0 ∧ (C.erase R).filter
          (fun S => j S ≠ 0) = C.erase R),
      (∏ S ∈ C, ((doubledDoubledQuintuplePattern C P Q S).choose
          (j S) : ℝ) * (-(d : ℝ)⁻¹) ^ (j S))
        * (colReMomentPow ρ μG C j u u'
          - ∏ S ∈ C, realMoment ρ μG (j S)))
    = 4 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4)
      - 2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      - 2 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      + ((d : ℝ)⁻¹) ^ 6
        * (doubledDoubledQuadReMoment ρ μG (C.erase R) P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    intro R hR
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRC : R ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    have hP' : P ∈ C.erase R :=
      Finset.mem_erase.mpr ⟨Ne.symm hRP, hP⟩
    have hQ' : Q ∈ C.erase R :=
      Finset.mem_erase.mpr ⟨Ne.symm hRQ, hQ⟩
    have hcardR : (C.erase R).card = 4 := by
      rw [Finset.card_erase_of_mem hRC, hC]
    rw [pieceSum_eq_topSum_erase ρ μG
      (doubledDoubledQuintuplePattern C P Q) C hC hRC u u']
    have hgen := patternValue_eq_baseline_add_top ρ μG hN hN3
      hρcont u u' (C.erase R)
      (fun S => if S = R then 0
        else doubledDoubledQuintuplePattern C P Q S)
      (by intro S hS
          by_cases hSR : S = R
          · rw [hSR]; simp
          · rw [if_neg hSR]
            exact hk0 S (fun h => hS
              (Finset.mem_erase.mpr ⟨hSR, h⟩)))
    have hint : (∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ ((fun S => if S = R then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          ∏ S ∈ C.erase R, (colDensC ρ u u' S α)
            ^ (if S = P then 2 else if S = Q then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      refine integral_congr_ae
        (Filter.Eventually.of_forall fun α => ?_)
      refine Finset.prod_congr rfl fun S hS => ?_
      have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
      have hSC : S ∈ C := (Finset.mem_erase.mp hS).2
      congr 1
      by_cases hSP : S = P
      · rw [hSP]
        simp [doubledDoubledQuintuplePattern, Ne.symm hRP]
      · by_cases hSQ : S = Q
        · rw [hSQ]
          simp [doubledDoubledQuintuplePattern, Ne.symm hRQ, hQP]
        · simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC,
            hSR]
    have hbaseE : (∏ S ∈ C.erase R, densMomentValue ρ μG
          ((fun S => if S = R then 0
            else doubledDoubledQuintuplePattern C P Q S) S))
        = (densMomentValue ρ μG 2) ^ 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2 := by
      have hQeRP : Q ∈ (C.erase R).erase P :=
        Finset.mem_erase.mpr ⟨hQP, hQ'⟩
      rw [← Finset.mul_prod_erase (C.erase R) _ hP',
        ← Finset.mul_prod_erase ((C.erase R).erase P) _ hQeRP]
      have hPP : densMomentValue ρ μG
            ((fun S => if S = R then 0
              else doubledDoubledQuintuplePattern C P Q S) P)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [doubledDoubledQuintuplePattern, Ne.symm hRP]
      have hQQ : densMomentValue ρ μG
            ((fun S => if S = R then 0
              else doubledDoubledQuintuplePattern C P Q S) Q)
          = densMomentValue ρ μG 2 := by
        congr 1
        simp [doubledDoubledQuintuplePattern, Ne.symm hRQ, hQP]
      have hrest : ∀ S ∈ ((C.erase R).erase P).erase Q,
          densMomentValue ρ μG
            ((fun S => if S = R then 0
              else doubledDoubledQuintuplePattern C P Q S) S)
            = 1 - e1 ρ μG / (d : ℝ) := by
        intro S hS
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp hS).2).1
        have hSR : S ≠ R :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hS).2).2).1
        have hSC : S ∈ C :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp hS).2).2).2
        have hSQ : S ≠ Q := (Finset.mem_erase.mp hS).1
        have hval : (fun S => if S = R then 0
              else doubledDoubledQuintuplePattern C P Q S) S
            = 1 := by
          simp [doubledDoubledQuintuplePattern, hSP, hSQ, hSC,
            hSR]
        rw [hval, densMomentValue_one]
      have hcardRPQ : (((C.erase R).erase P).erase Q).card = 2 := by
        rw [Finset.card_erase_of_mem hQeRP,
          Finset.card_erase_of_mem hP', hcardR,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl]
      rw [hPP, hQQ, Finset.prod_congr rfl hrest, Finset.prod_const,
        hcardRPQ, pow_two]
      ring
    rw [hint, hbaseE,
      integral_colDens_prod_quadruple_doubled_doubled ρ μG hN hN3
        hρcont u u' (C.erase R) hcardR P Q hP' hQ' hQP] at hgen
    linarith
  rw [Finset.sum_congr rfl hpieceR]
  ring
theorem sum_powerset_eq_sum_cards7 (F : Finset (LayerColumn N) → ℝ)
    (hF : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 8 ≤ C.card → F C = 0) :
    ∑ C ∈ Finset.univ.powerset, F C
      = ∑ j ∈ Finset.range 8,
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
  by_cases hM : Fintype.card (LayerColumn N) + 1 ≤ 8
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
      (fun j _ hj8 => ?_)).symm
    simp only [Finset.mem_range, not_lt] at hj8
    refine Finset.sum_eq_zero fun C hC => ?_
    exact hF C (Or.inr (by
      have hCj := (Finset.mem_powersetCard.mp hC).2
      omega))

/-- **The card-4 fiber, aggregated**: the multinomial
fiber over a 4-support is the weighted sum of the three
pattern values `(4,1,1,1)`, `(3,2,1,1)`, `(2,2,2,1)`
at weights `210`, `420`, `105`. -/
theorem fiber_card_four7_agg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)) := by
  classical
  have hk4111 : ∀ P ∈ C, ∀ Q ∉ C,
      quadrupledQuadPattern7 C P Q = 0 := by
    intro P hP Q hQ
    have hQP : Q ≠ P := fun h => hQ (h ▸ hP)
    simp [quadrupledQuadPattern7, hQP, hQ]
  have hk3211 : ∀ P ∈ C, ∀ Q ∈ C, ∀ R ∉ C,
      tripledDoubledQuadPattern7 C P Q R = 0 := by
    intro P hP Q hQ R hR
    have hRP : R ≠ P := fun h => hR (h ▸ hP)
    have hRQ : R ≠ Q := fun h => hR (h ▸ hQ)
    simp [tripledDoubledQuadPattern7, hRP, hRQ, hR]
  have hk2221 : ∀ P ∈ C, ∀ Q ∈ C, ∀ R ∈ C, ∀ S ∉ C,
      doubledDoubledDoubledQuadPattern7 C P Q R S = 0 := by
    intro P hP Q hQ R hR S hS
    have hSP : S ≠ P := fun h => hS (h ▸ hP)
    have hSQ : S ≠ Q := fun h => hS (h ▸ hQ)
    have hSR : S ≠ R := fun h => hS (h ▸ hR)
    simp [doubledDoubledDoubledQuadPattern7, hSP, hSQ, hSR, hS]
  have e4111 : ∀ P ∈ C, (210 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (quadrupledQuadPattern7 C P Q + 1)),
            (∏ Q ∈ C,
              ((quadrupledQuadPattern7 C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u')
      = (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)) := by
    intro P hP
    congr 1
    rw [← integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
      (quadrupledQuadPattern7 C P) (hk4111 P hP),
      patternValue4111 ρ μG hN hN3 hρcont u u' C hC P hP]
  have e3211 : ∀ P ∈ C, ∀ Q ∈ C.erase P, (420 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (tripledDoubledQuadPattern7 C P Q R + 1)),
            (∏ R ∈ C,
              ((tripledDoubledQuadPattern7 C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u')
      = (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)) := by
    intro P hP Q hQ
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    congr 1
    rw [← integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
      (tripledDoubledQuadPattern7 C P Q) (hk3211 P hP Q
        (Finset.mem_erase.mp hQ).2),
      patternValue3211_card4 ρ μG hN hN3 hρcont u u' C hC P Q hP
        (Finset.mem_erase.mp hQ).2 (Ne.symm hQP)]
  have e2221 : ∀ P ∈ C, ∀ Q ∈ C.erase P,
      ∀ R ∈ (C.erase P).erase Q, (105 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun S => Finset.range
                (doubledDoubledDoubledQuadPattern7 C P Q R S
                  + 1)),
            (∏ S ∈ C,
              ((doubledDoubledDoubledQuadPattern7 C P Q R
                  S).choose (j S) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j S))
              * colReMomentPow ρ μG C j u u')
      = (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)) := by
    intro P hP Q hQ R hR
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    have hRP : R ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
    have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
    congr 1
    rw [← integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
      (doubledDoubledDoubledQuadPattern7 C P Q R)
      (hk2221 P hP Q (Finset.mem_erase.mp hQ).2 R
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2),
      patternValue2221_card4 ρ μG hN hN3 hρcont u u' C hC P Q R hP
        (Finset.mem_erase.mp hQ).2
        (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
        (Ne.symm hQP) (Ne.symm hRP) (Ne.symm hRQ)]
  rw [fiber_card_four7 ρ μG hN hN3 hρcont u u' C hC,
    Finset.sum_congr rfl (fun P hP => e4111 P hP),
    Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
      (fun Q hQ => e3211 P hP Q hQ)),
    Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
      (fun Q hQ => Finset.sum_congr rfl
        (fun R hR => e2221 P hP Q hQ R hR)))]

/-- **The card-5 fiber, aggregated**: the multinomial
fiber over a 5-support is the weighted sum of the two
pattern values `(3,1,1,1,1)` and `(2,2,1,1,1)` at
weights `840` and `630`. -/
theorem fiber_card_five7_agg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))) := by
  classical
  have hk31111 : ∀ P ∈ C, ∀ Q ∉ C,
      tripledQuintuplePattern C P Q = 0 := by
    intro P hP Q hQ
    have hQP : Q ≠ P := fun h => hQ (h ▸ hP)
    simp [tripledQuintuplePattern, hQP, hQ]
  have hk22111 : ∀ P ∈ C, ∀ Q ∈ C, ∀ R ∉ C,
      doubledDoubledQuintuplePattern C P Q R = 0 := by
    intro P hP Q hQ R hR
    have hRP : R ≠ P := fun h => hR (h ▸ hP)
    have hRQ : R ≠ Q := fun h => hR (h ▸ hQ)
    simp [doubledDoubledQuintuplePattern, hRP, hRQ, hR]
  have e31111 : ∀ P ∈ C, (840 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun Q => Finset.range
                (tripledQuintuplePattern C P Q + 1)),
            (∏ Q ∈ C,
              ((tripledQuintuplePattern C P Q).choose
                  (j Q) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j Q))
              * colReMomentPow ρ μG C j u u')
      = (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))) := by
    intro P hP
    congr 1
    rw [← integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
      (tripledQuintuplePattern C P) (hk31111 P hP),
      patternValue31111 ρ μG hN hN3 hρcont u u' C hC P hP]
  have e22111 : ∀ P ∈ C, ∀ Q ∈ C.erase P, (630 : ℝ)
          * (∑ j ∈ Fintype.piFinset
              (fun R => Finset.range
                (doubledDoubledQuintuplePattern C P Q R
                  + 1)),
            (∏ R ∈ C,
              ((doubledDoubledQuintuplePattern C P Q R).choose
                  (j R) : ℝ)
                * (-(d : ℝ)⁻¹) ^ (j R))
              * colReMomentPow ρ μG C j u u')
      = (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))) := by
    intro P hP Q hQ
    have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
    congr 1
    rw [← integral_colDens_prod_pow_eq_sum ρ μG hρcont u u' C
      (doubledDoubledQuintuplePattern C P Q) (hk22111 P hP Q
        (Finset.mem_erase.mp hQ).2),
      patternValue22111 ρ μG hN hN3 hρcont u u' C hC P Q hP
        (Finset.mem_erase.mp hQ).2 hQP]
  rw [fiber_card_five7 ρ μG hN hN3 hρcont u u' C hC,
    Finset.sum_congr rfl (fun P hP => e31111 P hP),
    Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
      (fun Q hQ => e22111 P hP Q hQ))]
set_option maxHeartbeats 1600000 in
/-- **The total expansion at order 7.** The raw
seventh coefficient is the closed constant
`kappa7Const` plus the four dependent excess groups
(cards 4–7), in the native forms read off the landed
fiber accounting. -/
theorem betaCoeff7_total (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 7
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = kappa7Const (N := N) ρ μG
        + ∑ C ∈ Finset.univ.powersetCard 4, (∑ P ∈ C, (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))
        + ∑ C ∈ Finset.univ.powersetCard 5, (∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))
        + ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
            (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
        + ∑ C ∈ Finset.univ.powersetCard 7,
            (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)) := by
  classical
  have hch1 : ((Nat.choose (Fintype.card (LayerColumn N)) 1 : ℝ))
      = colCount N := by
    have h := cast_factorial_mul_choose6 (N := N) 1
    have hprod : (∏ i ∈ Finset.range 1, (colCount N - (i : ℝ)))
        = colCount N := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by
      norm_num [Nat.factorial]
    rw [hfact, one_mul] at h
    exact h
  have hch2 : ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ))
      = colCount N * (colCount N - 1) / 2 := by
    have h := cast_factorial_mul_choose6 (N := N) 2
    have hprod : (∏ i ∈ Finset.range 2, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
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
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch4 : ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) / 24 := by
    have h := cast_factorial_mul_choose6 (N := N) 4
    have hprod : (∏ i ∈ Finset.range 4, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (24 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch5 : ((Nat.choose (Fintype.card (LayerColumn N)) 5 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) / 120 := by
    have h := cast_factorial_mul_choose6 (N := N) 5
    have hprod : (∏ i ∈ Finset.range 5, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (120 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch6 : ((Nat.choose (Fintype.card (LayerColumn N)) 6 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) * (colCount N - 5) / 720 := by
    have h := cast_factorial_mul_choose6 (N := N) 6
    have hprod : (∏ i ∈ Finset.range 6, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) * (colCount N - 5) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (720 : ℝ) ≠ 0), mul_comm]
    exact h
  have hch7 : ((Nat.choose (Fintype.card (LayerColumn N)) 7 : ℝ))
      = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) * (colCount N - 5) * (colCount N - 6) / 5040 := by
    have h := cast_factorial_mul_choose6 (N := N) 7
    have hprod : (∏ i ∈ Finset.range 7, (colCount N - (i : ℝ)))
        = colCount N * (colCount N - 1) * (colCount N - 2) * (colCount N - 3) * (colCount N - 4) * (colCount N - 5) * (colCount N - 6) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
      ring
    rw [hprod] at h
    have hfact : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by
      norm_num [Nat.factorial]
    rw [hfact] at h
    rw [eq_div_iff (by norm_num : (5040 : ℝ) ≠ 0), mul_comm]
    exact h
  have hFibVanish : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 8 ≤ C.card → ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG) = 0 := by
    intro C hC
    rw [fiber7_eq_empty_of_card_ne C hC, Finset.sum_empty]
  have hG0 : ∑ C ∈ Finset.univ.powersetCard 0, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG) = 0 :=
    Finset.sum_eq_zero fun C hC => hFibVanish C
      (Or.inl (Finset.mem_powersetCard.mp hC).2)
  have hG1 : ∑ C ∈ Finset.univ.powersetCard 1, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 1 : ℝ)) * (densMomentValue ρ μG 7) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_one7 ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hG2 : ∑ C ∈ Finset.univ.powersetCard 2, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ)) * (7 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 6)
        + 21 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 5)
        + 35 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 4)
        + 35 * (densMomentValue ρ μG 4 * densMomentValue ρ μG 3)
        + 21 * (densMomentValue ρ μG 5 * densMomentValue ρ μG 2)
        + 7 * (densMomentValue ρ μG 6 * densMomentValue ρ μG 1)) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_two7 ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hG3 : ∑ C ∈ Finset.univ.powersetCard 3, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 3 : ℝ)) * (42 * (densMomentValue ρ μG 5
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
        + 42 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 5 * densMomentValue ρ μG 1))
        + 42 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 5))
        + 105 * (densMomentValue ρ μG 4
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
        + 105 * (densMomentValue ρ μG 4
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
        + 105 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 4 * densMomentValue ρ μG 1))
        + 105 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4))
        + 105 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 4 * densMomentValue ρ μG 2))
        + 105 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 4))
        + 140 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
        + 140 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
        + 140 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 3))
        + 210 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 2))
        + 210 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2))
        + 210 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_three7 ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hsplit4111 : ∀ (C : Finset (LayerColumn N))
      (P : LayerColumn N), (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
      = (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3) + (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)) :=
    fun C P => by ring
  have hsplit3211 : ∀ (C : Finset (LayerColumn N))
      (P Q : LayerColumn N), (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
      = (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2) + (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)) :=
    fun C P Q => by ring
  have hsplit2221 : ∀ (C : Finset (LayerColumn N))
      (P Q R : LayerColumn N), (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))) + (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)) :=
    fun C P Q R => by ring
  have hbase4111 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      ∑ P ∈ C, (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        = 840 * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3) := by
    intro C hcard
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hbase3211 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
        = 5040 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP, hcard,
        show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul]),
      Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hbase2221 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ)))
        = 2520 * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul])),
      Finset.sum_congr rfl (fun P hP => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul]),
      Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hfam4111 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      (∑ P ∈ C, (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)))
        = 840 * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3) + ∑ P ∈ C, (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => hsplit4111 C P),
      Finset.sum_add_distrib, hbase4111 C hcard]
  have hfam3211 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      (∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)))
        = 5040 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
          + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
        (fun Q hQ => hsplit3211 C P Q)),
      Finset.sum_congr rfl (fun P _ => Finset.sum_add_distrib),
      Finset.sum_add_distrib, hbase3211 C hcard]
  have hfam2221 : ∀ (C : Finset (LayerColumn N)), C.card = 4 →
      (∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))
        = 2520 * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ)))
          + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
        (fun Q hQ => Finset.sum_congr rfl
          (fun R hR => hsplit2221 C P Q R))),
      Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
        (fun Q _ => Finset.sum_add_distrib)),
      Finset.sum_congr rfl (fun P _ => Finset.sum_add_distrib),
      Finset.sum_add_distrib, hbase2221 C hcard]
  have hCsplit4 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, (210 : ℝ) * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + 6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
        + 8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))
        = (840 * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3) + 5040 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
            + 2520 * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))))
          + (∑ P ∈ C, (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))  := by
    intro C hC
    have hcard : C.card = 4 := (Finset.mem_powersetCard.mp hC).2
    rw [hfam4111 C hcard, hfam3211 C hcard, hfam2221 C hcard]
    ring
  have hG4 : ∑ C ∈ Finset.univ.powersetCard 4, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ)) * (840 * (densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3) + 5040 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
          + 2520 * ((densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))))
        + ∑ C ∈ Finset.univ.powersetCard 4, (∑ P ∈ C, (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_four7_agg ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_congr rfl (fun C hC => hCsplit4 C hC),
      Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hsplit31111 : ∀ (C : Finset (LayerColumn N))
      (P : LayerColumn N), (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
      = (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4) + (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))) :=
    fun C P => by ring
  have hsplit22111 : ∀ (C : Finset (LayerColumn N))
      (P Q : LayerColumn N), (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)))
      = (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)) + (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))) :=
    fun C P Q => by ring
  have hbase31111 : ∀ (C : Finset (LayerColumn N)), C.card = 5 →
      ∑ P ∈ C, (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4)
        = 4200 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4) := by
    intro C hcard
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hbase22111 : ∀ (C : Finset (LayerColumn N)), C.card = 5 →
      ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
        = 12600 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP, hcard,
        show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul]),
      Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hfam31111 : ∀ (C : Finset (LayerColumn N)), C.card = 5 →
      (∑ P ∈ C, (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))))
        = 4200 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4) + ∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => hsplit31111 C P),
      Finset.sum_add_distrib, hbase31111 C hcard]
  have hfam22111 : ∀ (C : Finset (LayerColumn N)), C.card = 5 →
      (∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))
        = 12600 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
          + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))) := by
    intro C hcard
    rw [Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl
        (fun Q hQ => hsplit22111 C P Q)),
      Finset.sum_congr rfl (fun P _ => Finset.sum_add_distrib),
      Finset.sum_add_distrib, hbase22111 C hcard]
  have hCsplit5 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, (840 : ℝ) * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))
        = (4200 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4) + 12600 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)))
          + (∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))  := by
    intro C hC
    have hcard : C.card = 5 := (Finset.mem_powersetCard.mp hC).2
    rw [hfam31111 C hcard, hfam22111 C hcard]
    ring
  have hG5 : ∑ C ∈ Finset.univ.powersetCard 5, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 5 : ℝ)) * (4200 * (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4) + 12600 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3)))
        + ∑ C ∈ Finset.univ.powersetCard 5, (∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_five7_agg ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_congr rfl (fun C hC => hCsplit5 C hC),
      Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hsplit6 : ∀ (C : Finset (LayerColumn N))
      (P : LayerColumn N), (2520 : ℝ) * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            + ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = (2520 : ℝ) * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5) + (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) :=
    fun C P => by ring
  have hCsplit6 : ∀ C ∈ Finset.univ.powersetCard 6,
      ∑ P ∈ C, (2520 : ℝ) * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
            + ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
        = 15120 * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5)
          + ∑ P ∈ C, (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
    intro C hC
    have hcard : C.card = 6 := (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP => hsplit6 C P),
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hG6 : ∑ C ∈ Finset.univ.powersetCard 6, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 6 : ℝ)) * (15120 * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5))
        + ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
            (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_six7 ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_congr rfl (fun C hC => hCsplit6 C hC),
      Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hsplit7 : ∀ (C : Finset (LayerColumn N)),
      (5040 * ((1 - e1 ρ μG / (d : ℝ)) ^ 7
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)))
      = 5040 * ((1 - e1 ρ μG / (d : ℝ)) ^ 7) + (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)) :=
    fun C => by ring
  have hG7 : ∑ C ∈ Finset.univ.powersetCard 7, ∑ k ∈ (Finset.piAntidiag Finset.univ 7).filter
          (fun k => multSupport k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 7 : ℝ)) * (5040 * ((1 - e1 ρ μG / (d : ℝ)) ^ 7))
        + ∑ C ∈ Finset.univ.powersetCard 7,
            (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)) := by
    rw [Finset.sum_congr rfl (fun C hC =>
      fiber_card_seven7 ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_congr rfl (fun C hC => hsplit7 C),
      Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  rw [integral_layerDensSum_pow_seven ρ μG hN hρcont u u',
    sum_piAntidiag7_fiberwise,
    sum_powerset_eq_sum_cards7 _ hFibVanish]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hG0, hG1, hG2, hG3, hG4, hG5, hG6, hG7]
  unfold kappa7Const
  rw [hch1, hch2, hch3, hch4, hch5, hch6, hch7, densMomentValue_one]
  ring
/-- **Card-3 factorization, plain moment**: on a
3-support the all-distinct moment is `e₁³`. -/
theorem quadReMoment_eq_of_card_three (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) :
    quadReMoment ρ μG D u u' = (e1 ρ μG) ^ 3 := by
  classical
  unfold quadReMoment
  rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3
    hρcont u u' D (le_of_eq hD), hD]

/-- **Card-3 factorization, doubled moment**: on a
3-support the doubled moment at any seat is `μ₂e₁²`
(the two remaining columns are distinct and split). -/
theorem doubledQuadReMoment_eq_of_card_three (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {R : LayerColumn N} (hR : R ∈ D) :
    doubledQuadReMoment ρ μG D R u u'
      = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
  classical
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

/-- **Card-3 factorization, tripled moment**: on a
3-support the tripled moment at any seat is `μ₃e₁²`. -/
theorem tripledQuadReMoment_eq_of_card_three (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {R : LayerColumn N} (hR : R ∈ D) :
    tripledQuadReMoment ρ μG D R u u'
      = realMoment ρ μG 3 * (e1 ρ μG) ^ 2 := by
  classical
  have hcong : ∀ α : LayerSite N → G,
      (colRe ρ u u' R α) ^ 3
          * ∏ Z ∈ D.erase R, colRe ρ u u' Z α
        = ∏ Z ∈ D,
            (colRe ρ u u' Z α) ^ (if Z = R then 3 else 1) := by
    intro α
    rw [← Finset.mul_prod_erase D
      (fun Z => (colRe ρ u u' Z α) ^ (if Z = R then 3 else 1))
      hR, if_pos rfl]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun Z hZ => by
      rw [if_neg (Finset.mem_erase.mp hZ).1, pow_one]
  calc tripledQuadReMoment ρ μG D R u u'
      = ∫ α : LayerSite N → G,
          ∏ Z ∈ D,
            (colRe ρ u u' Z α) ^ (if Z = R then 3 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∏ Z ∈ D, realMoment ρ μG (if Z = R then 3 else 1) :=
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' D (le_of_eq hD)
          (fun Z => if Z = R then 3 else 1)
    _ = realMoment ρ μG 3 * (e1 ρ μG) ^ 2 := by
        rw [← Finset.mul_prod_erase D
          (fun Z => realMoment ρ μG (if Z = R then 3 else 1))
          hR, if_pos rfl]
        have h2 : ∀ Z ∈ D.erase R,
            realMoment ρ μG (if Z = R then 3 else 1)
              = e1 ρ μG := by
          intro Z hZ
          rw [if_neg (Finset.mem_erase.mp hZ).1, realMoment_one]
        rw [Finset.prod_congr rfl h2, Finset.prod_const]
        have h3 : (D.erase R).card = 2 := by
          rw [Finset.card_erase_of_mem hR, hD]
        rw [h3]

/-- **Card-3 factorization, quadrupled moment**: on a
3-support the quadrupled moment at any seat is
`μ₄e₁²`. -/
theorem quadrupledQuadReMoment_eq_of_card_three (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {R : LayerColumn N} (hR : R ∈ D) :
    quadrupledQuadReMoment ρ μG D R u u'
      = realMoment ρ μG 4 * (e1 ρ μG) ^ 2 := by
  classical
  have hcong : ∀ α : LayerSite N → G,
      (colRe ρ u u' R α) ^ 4
          * ∏ Z ∈ D.erase R, colRe ρ u u' Z α
        = ∏ Z ∈ D,
            (colRe ρ u u' Z α) ^ (if Z = R then 4 else 1) := by
    intro α
    rw [← Finset.mul_prod_erase D
      (fun Z => (colRe ρ u u' Z α) ^ (if Z = R then 4 else 1))
      hR, if_pos rfl]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun Z hZ => by
      rw [if_neg (Finset.mem_erase.mp hZ).1, pow_one]
  calc quadrupledQuadReMoment ρ μG D R u u'
      = ∫ α : LayerSite N → G,
          ∏ Z ∈ D,
            (colRe ρ u u' Z α) ^ (if Z = R then 4 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∏ Z ∈ D, realMoment ρ μG (if Z = R then 4 else 1) :=
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' D (le_of_eq hD)
          (fun Z => if Z = R then 4 else 1)
    _ = realMoment ρ μG 4 * (e1 ρ μG) ^ 2 := by
        rw [← Finset.mul_prod_erase D
          (fun Z => realMoment ρ μG (if Z = R then 4 else 1))
          hR, if_pos rfl]
        have h2 : ∀ Z ∈ D.erase R,
            realMoment ρ μG (if Z = R then 4 else 1)
              = e1 ρ μG := by
          intro Z hZ
          rw [if_neg (Finset.mem_erase.mp hZ).1, realMoment_one]
        rw [Finset.prod_congr rfl h2, Finset.prod_const]
        have h3 : (D.erase R).card = 2 := by
          rw [Finset.card_erase_of_mem hR, hD]
        rw [h3]

/-- **Card-3 factorization, doubled-doubled moment**:
on a 3-support the `(2,2,1)` moment at an ordered pair
of distinct seats is `μ₂²e₁`. -/
theorem doubledDoubledQuadReMoment_eq_of_card_three
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {P Q : LayerColumn N} (hP : P ∈ D)
    (hQ : Q ∈ D.erase P) :
    doubledDoubledQuadReMoment ρ μG D P Q u u'
      = (realMoment ρ μG 2) ^ 2 * e1 ρ μG := by
  classical
  have hQC : Q ∈ D := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hcong : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (D.erase P).erase Q, colRe ρ u u' R α
        = ∏ R ∈ D, (colRe ρ u u' R α)
            ^ (if R = P then 2 else if R = Q then 2 else 1) := by
    intro α
    have hrest : ∏ R ∈ (D.erase P).erase Q, colRe ρ u u' R α
        = ∏ R ∈ (D.erase P).erase Q, (colRe ρ u u' R α)
            ^ (if R = P then 2 else if R = Q then 2 else 1) :=
      Finset.prod_congr rfl fun R hR => by
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        rw [if_neg hRP, if_neg hRQ, pow_one]
    rw [hrest,
      ← Finset.mul_prod_erase D
        (fun R => (colRe ρ u u' R α)
          ^ (if R = P then 2 else if R = Q then 2 else 1)) hP,
      ← Finset.mul_prod_erase (D.erase P)
        (fun R => (colRe ρ u u' R α)
          ^ (if R = P then 2 else if R = Q then 2 else 1)) hQ,
      if_pos rfl, if_neg hQP, if_pos rfl]
    ring
  calc doubledDoubledQuadReMoment ρ μG D P Q u u'
      = ∫ α : LayerSite N → G,
          ∏ R ∈ D, (colRe ρ u u' R α)
            ^ (if R = P then 2 else if R = Q then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∏ R ∈ D, realMoment ρ μG
          (if R = P then 2 else if R = Q then 2 else 1) :=
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' D (le_of_eq hD)
          (fun R => if R = P then 2 else if R = Q then 2 else 1)
    _ = (realMoment ρ μG 2) ^ 2 * e1 ρ μG := by
        rw [← Finset.mul_prod_erase D
          (fun R => realMoment ρ μG
            (if R = P then 2 else if R = Q then 2 else 1)) hP,
          if_pos rfl,
          ← Finset.mul_prod_erase (D.erase P)
          (fun R => realMoment ρ μG
            (if R = P then 2 else if R = Q then 2 else 1)) hQ,
          if_neg hQP, if_pos rfl]
        have h2 : ∀ Z ∈ (D.erase P).erase Q, realMoment ρ μG
            (if Z = P then 2 else if Z = Q then 2 else 1)
              = e1 ρ μG := by
          intro Z hZ
          rw [if_neg (Finset.mem_erase.mp
              (Finset.mem_erase.mp hZ).2).1,
            if_neg (Finset.mem_erase.mp hZ).1, realMoment_one]
        rw [Finset.prod_congr rfl h2, Finset.prod_const]
        have hcard : ((D.erase P).erase Q).card = 1 := by
          rw [Finset.card_erase_of_mem hQ,
            Finset.card_erase_of_mem hP, hD]
        rw [hcard, pow_one]
        ring

/-- **Card-3 factorization, tripled-doubled moment**:
on a 3-support the `(3,2,1)` moment at an ordered pair
of distinct seats is `μ₃μ₂e₁`. -/
theorem tripledDoubledQuadReMoment_eq_of_card_three
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {P Q : LayerColumn N} (hP : P ∈ D)
    (hQ : Q ∈ D.erase P) :
    tripledDoubledQuadReMoment ρ μG D P Q u u'
      = realMoment ρ μG 3 * realMoment ρ μG 2 * e1 ρ μG := by
  classical
  have hQC : Q ∈ D := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hcong : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (D.erase P).erase Q, colRe ρ u u' R α
        = ∏ R ∈ D, (colRe ρ u u' R α)
            ^ (if R = P then 3 else if R = Q then 2 else 1) := by
    intro α
    have hrest : ∏ R ∈ (D.erase P).erase Q, colRe ρ u u' R α
        = ∏ R ∈ (D.erase P).erase Q, (colRe ρ u u' R α)
            ^ (if R = P then 3 else if R = Q then 2 else 1) :=
      Finset.prod_congr rfl fun R hR => by
        have hRP : R ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).1
        have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
        rw [if_neg hRP, if_neg hRQ, pow_one]
    rw [hrest,
      ← Finset.mul_prod_erase D
        (fun R => (colRe ρ u u' R α)
          ^ (if R = P then 3 else if R = Q then 2 else 1)) hP,
      ← Finset.mul_prod_erase (D.erase P)
        (fun R => (colRe ρ u u' R α)
          ^ (if R = P then 3 else if R = Q then 2 else 1)) hQ,
      if_pos rfl, if_neg hQP, if_pos rfl]
    ring
  calc tripledDoubledQuadReMoment ρ μG D P Q u u'
      = ∫ α : LayerSite N → G,
          ∏ R ∈ D, (colRe ρ u u' R α)
            ^ (if R = P then 3 else if R = Q then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∏ R ∈ D, realMoment ρ μG
          (if R = P then 3 else if R = Q then 2 else 1) :=
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' D (le_of_eq hD)
          (fun R => if R = P then 3 else if R = Q then 2 else 1)
    _ = realMoment ρ μG 3 * realMoment ρ μG 2 * e1 ρ μG := by
        rw [← Finset.mul_prod_erase D
          (fun R => realMoment ρ μG
            (if R = P then 3 else if R = Q then 2 else 1)) hP,
          if_pos rfl,
          ← Finset.mul_prod_erase (D.erase P)
          (fun R => realMoment ρ μG
            (if R = P then 3 else if R = Q then 2 else 1)) hQ,
          if_neg hQP, if_pos rfl]
        have h2 : ∀ Z ∈ (D.erase P).erase Q, realMoment ρ μG
            (if Z = P then 3 else if Z = Q then 2 else 1)
              = e1 ρ μG := by
          intro Z hZ
          rw [if_neg (Finset.mem_erase.mp
              (Finset.mem_erase.mp hZ).2).1,
            if_neg (Finset.mem_erase.mp hZ).1, realMoment_one]
        rw [Finset.prod_congr rfl h2, Finset.prod_const]
        have hcard : ((D.erase P).erase Q).card = 1 := by
          rw [Finset.card_erase_of_mem hQ,
            Finset.card_erase_of_mem hP, hD]
        rw [hcard, pow_one]
        ring

/-- **Card-3 factorization, triple-doubled moment**:
on a 3-support the `(2,2,2)` moment at an ordered
triple of distinct seats (filling the support) is
`μ₂³`. -/
theorem doubledDoubledDoubledQuadReMoment_eq_of_card_three
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (D : Finset (LayerColumn N))
    (hD : D.card = 3) {P Q R : LayerColumn N} (hP : P ∈ D)
    (hQ : Q ∈ D.erase P) (hR : R ∈ (D.erase P).erase Q) :
    doubledDoubledDoubledQuadReMoment ρ μG D P Q R u u'
      = (realMoment ρ μG 2) ^ 3 := by
  classical
  have hQC : Q ∈ D := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hRC : R ∈ D.erase P := (Finset.mem_erase.mp hR).2
  have hRD : R ∈ D := (Finset.mem_erase.mp hRC).2
  have hRP : R ≠ P := (Finset.mem_erase.mp hRC).1
  have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
  have hcong : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ S ∈ ((D.erase P).erase Q).erase R,
              colRe ρ u u' S α
        = ∏ S ∈ D, (colRe ρ u u' S α)
            ^ (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1) := by
    intro α
    have hrest : ∏ S ∈ ((D.erase P).erase Q).erase R,
          colRe ρ u u' S α
        = ∏ S ∈ ((D.erase P).erase Q).erase R,
            (colRe ρ u u' S α)
            ^ (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1) :=
      Finset.prod_congr rfl fun S hS => by
        have hSP : S ≠ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp
            (Finset.mem_erase.mp hS).2).2).1
        have hSQ : S ≠ Q :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1
        have hSR : S ≠ R := (Finset.mem_erase.mp hS).1
        rw [if_neg hSP, if_neg hSQ, if_neg hSR, pow_one]
    rw [hrest,
      ← Finset.mul_prod_erase D
        (fun S => (colRe ρ u u' S α)
          ^ (if S = P then 2 else if S = Q then 2
            else if S = R then 2 else 1)) hP,
      ← Finset.mul_prod_erase (D.erase P)
        (fun S => (colRe ρ u u' S α)
          ^ (if S = P then 2 else if S = Q then 2
            else if S = R then 2 else 1)) hQ,
      ← Finset.mul_prod_erase ((D.erase P).erase Q)
        (fun S => (colRe ρ u u' S α)
          ^ (if S = P then 2 else if S = Q then 2
            else if S = R then 2 else 1)) hR,
      if_pos rfl, if_neg hQP, if_pos rfl, if_neg hRP,
      if_neg hRQ, if_pos rfl]
    ring
  calc doubledDoubledDoubledQuadReMoment ρ μG D P Q R u u'
      = ∫ α : LayerSite N → G,
          ∏ S ∈ D, (colRe ρ u u' S α)
            ^ (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∏ S ∈ D, realMoment ρ μG
          (if S = P then 2 else if S = Q then 2
            else if S = R then 2 else 1) :=
        integral_colRe_prod_pow_card_le_three6 ρ μG hN hN3
          hρcont u u' D (le_of_eq hD)
          (fun S => if S = P then 2 else if S = Q then 2
            else if S = R then 2 else 1)
    _ = (realMoment ρ μG 2) ^ 3 := by
        rw [← Finset.mul_prod_erase D
          (fun S => realMoment ρ μG
            (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1)) hP,
          if_pos rfl,
          ← Finset.mul_prod_erase (D.erase P)
          (fun S => realMoment ρ μG
            (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1)) hQ,
          if_neg hQP, if_pos rfl,
          ← Finset.mul_prod_erase ((D.erase P).erase Q)
          (fun S => realMoment ρ μG
            (if S = P then 2 else if S = Q then 2
              else if S = R then 2 else 1)) hR,
          if_neg hRP, if_neg hRQ, if_pos rfl]
        have hempty : ((D.erase P).erase Q).erase R
            = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [Finset.card_erase_of_mem hR,
            Finset.card_erase_of_mem hQ,
            Finset.card_erase_of_mem hP, hD]
        rw [hempty, Finset.prod_empty]
        ring
/-- **Quadrupled excess vanishes off primitive
quads.** At a non-primitive 4-support, a private
column either is the quadrupled seat (strip it:
`μ₄` times a card-3 plain moment, which is `e₁³`)
or is a single (strip it: `e₁` times a card-3
quadrupled moment, which is `μ₄e₁²`). -/
theorem quadrupledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P : LayerColumn N} (hP : P ∈ C) :
    quadrupledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 4 * (e1 ρ μG) ^ 3 = 0 := by
  classical
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  have hcard3 : (C.erase X).card = 3 := by
    rw [Finset.card_erase_of_mem hXC, hC]
  by_cases hXP : X = P
  · subst hXP
    rw [quadrupledQuadReMoment_strip_quadrupled ρ μG hN hN3
      hρcont u u' hsX hpriv,
      quadReMoment_eq_of_card_three ρ μG hN hN3 hρcont u u'
        (C.erase X) hcard3]
    ring
  · have hPX : P ∈ C.erase X :=
      Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
    rw [quadrupledQuadReMoment_strip_single ρ μG hN hN3
      hρcont u u' hP hXC hXP hsX hpriv,
      quadrupledQuadReMoment_eq_of_card_three ρ μG hN hN3
        hρcont u u' (C.erase X) hcard3 hPX]
    ring

/-- **Tripled-doubled excess vanishes off primitive
quads.** At a non-primitive 4-support, a private
column is the tripled seat, the doubled seat, or a
single; each strip leaves a card-3 moment that
factors at the baseline `μ₃μ₂e₁²`. -/
theorem tripledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P Q : LayerColumn N} (hP : P ∈ C) (hQ : Q ∈ C.erase P) :
    tripledDoubledQuadReMoment ρ μG C P Q u u'
      - realMoment ρ μG 3 * realMoment ρ μG 2
        * (e1 ρ μG) ^ 2 = 0 := by
  classical
  have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  have hcard3 : (C.erase X).card = 3 := by
    rw [Finset.card_erase_of_mem hXC, hC]
  by_cases hXP : X = P
  · subst hXP
    have hQX : Q ∈ (C.erase X) :=
      Finset.mem_erase.mpr ⟨hQP, hQC⟩
    rw [tripledDoubledQuadReMoment_strip_tripled ρ μG hN
      hN3 hρcont u u' hQC hQP hsX hpriv,
      doubledQuadReMoment_eq_of_card_three ρ μG hN hN3
        hρcont u u' (C.erase X) hcard3 hQX]
    ring
  · by_cases hXQ : X = Q
    · subst hXQ
      have hPX : P ∈ (C.erase X) :=
        Finset.mem_erase.mpr ⟨Ne.symm hQP, hP⟩
      rw [tripledDoubledQuadReMoment_strip_doubled ρ μG hN
        hN3 hρcont u u' hP hQP hsX hpriv,
        tripledQuadReMoment_eq_of_card_three ρ μG hN hN3
          hρcont u u' (C.erase X) hcard3 hPX]
      ring
    · have hPX : P ∈ C.erase X :=
        Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
      have hQX : Q ∈ (C.erase X).erase P :=
        Finset.mem_erase.mpr ⟨hQP,
          Finset.mem_erase.mpr ⟨Ne.symm hXQ, hQC⟩⟩
      rw [tripledDoubledQuadReMoment_strip_single ρ μG hN
        hN3 hρcont u u' hP hQC hXC hXP hXQ hQP hsX hpriv,
        tripledDoubledQuadReMoment_eq_of_card_three ρ μG
          hN hN3 hρcont u u' (C.erase X) hcard3 hPX hQX]
      ring

/-- **Triple-doubled excess vanishes off primitive
quads.** At a non-primitive 4-support, a private
column is one of the three doubled seats or a
single; each strip leaves a card-3 moment that
factors at the baseline `μ₂³e₁`. -/
theorem doubledDoubledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P Q R : LayerColumn N} (hP : P ∈ C)
    (hQ : Q ∈ C.erase P) (hR : R ∈ (C.erase P).erase Q) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      - (realMoment ρ μG 2) ^ 3 * e1 ρ μG = 0 := by
  classical
  have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
  have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
  have hRP' : R ∈ C.erase P := (Finset.mem_erase.mp hR).2
  have hRC : R ∈ C := (Finset.mem_erase.mp hRP').2
  have hRP : R ≠ P := (Finset.mem_erase.mp hRP').1
  have hRQ : R ≠ Q := (Finset.mem_erase.mp hR).1
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  have hcard3 : (C.erase X).card = 3 := by
    rw [Finset.card_erase_of_mem hXC, hC]
  by_cases hXP : X = P
  · subst hXP
    have hQX : Q ∈ (C.erase X) :=
      Finset.mem_erase.mpr ⟨hQP, hQC⟩
    have hRX : R ∈ (C.erase X).erase Q :=
      Finset.mem_erase.mpr ⟨hRQ, hRP'⟩
    rw [doubledDoubledDoubledQuadReMoment_strip_first ρ μG
      hN hN3 hρcont u u' hQC hRC hQP hRP hRQ hsX hpriv,
      doubledDoubledQuadReMoment_eq_of_card_three ρ μG hN
        hN3 hρcont u u' (C.erase X) hcard3 hQX hRX]
    ring
  · by_cases hXQ : X = Q
    · subst hXQ
      have hPX : P ∈ (C.erase X) :=
        Finset.mem_erase.mpr ⟨Ne.symm hQP, hP⟩
      have hRX : R ∈ (C.erase X).erase P :=
        Finset.mem_erase.mpr ⟨hRP,
          Finset.mem_erase.mpr ⟨hRQ, hRC⟩⟩
      rw [doubledDoubledDoubledQuadReMoment_strip_second
        ρ μG hN hN3 hρcont u u' hP hRC hQP hRP hRQ hsX
        hpriv,
        doubledDoubledQuadReMoment_eq_of_card_three ρ μG
          hN hN3 hρcont u u' (C.erase X) hcard3 hPX hRX]
      ring
    · by_cases hXR : X = R
      · subst hXR
        have hPX : P ∈ (C.erase X) :=
          Finset.mem_erase.mpr ⟨Ne.symm hRP, hP⟩
        have hQX : Q ∈ (C.erase X).erase P :=
          Finset.mem_erase.mpr ⟨hQP,
            Finset.mem_erase.mpr ⟨Ne.symm hRQ, hQC⟩⟩
        rw [doubledDoubledDoubledQuadReMoment_strip_third
          ρ μG hN hN3 hρcont u u' hP hQC hQP hRP hRQ hsX
          hpriv,
          doubledDoubledQuadReMoment_eq_of_card_three ρ μG
            hN hN3 hρcont u u' (C.erase X) hcard3 hPX hQX]
        ring
      · have hPX : P ∈ C.erase X :=
          Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
        have hQX : Q ∈ (C.erase X).erase P :=
          Finset.mem_erase.mpr ⟨hQP,
            Finset.mem_erase.mpr ⟨Ne.symm hXQ, hQC⟩⟩
        have hRX : R ∈ ((C.erase X).erase P).erase Q :=
          Finset.mem_erase.mpr ⟨hRQ,
            Finset.mem_erase.mpr ⟨hRP,
              Finset.mem_erase.mpr ⟨Ne.symm hXR, hRC⟩⟩⟩
        rw [doubledDoubledDoubledQuadReMoment_strip_single
          ρ μG hN hN3 hρcont u u' hP hQC hRC hXC hXP hXQ
          hXR hQP hRP hRQ hsX hpriv,
          doubledDoubledDoubledQuadReMoment_eq_of_card_three
            ρ μG hN hN3 hρcont u u' (C.erase X) hcard3 hPX
            hQX hRX]
        ring

/-- **The `(4,1,1,1)` excess sum, converted**: the
`powersetCard 4` quadrupled excess sum is the B7-2a
channel excess (the summand vanishes off primitive
quads). -/
theorem sum_powersetCard_four_quadrupled_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)
      = kappa7chan4111Excess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (quadrupledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)
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
    exact quadrupledQuadReMoment_sub_eq_zero_of_not_primitive
      ρ μG hN hN3 hρcont u u' hcard hnp hP

/-- **The `(3,2,1,1)` excess sum, converted**: the
`powersetCard 4` tripled-doubled excess sum is the
B7-2a (unsplit) channel excess. -/
theorem sum_powersetCard_four_tripledDoubled_excess
    (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (tripledDoubledQuadReMoment ρ μG C P Q u u'
          - realMoment ρ μG 3 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2)
      = kappa7chan3211Excess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    (tripledDoubledQuadReMoment ρ μG C P Q u u'
      - realMoment ρ μG 3 * realMoment ρ μG 2
        * (e1 ρ μG) ^ 2)
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
    exact tripledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
      ρ μG hN hN3 hρcont u u' hcard hnp hP hQ

/-- **The `(2,2,2,1)` excess sum, converted**: the
`powersetCard 4` triple-doubled excess sum is the
B7-2a channel excess. -/
theorem sum_powersetCard_four_tripledDoubledDoubled_excess
    (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
          - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)
      = kappa7chan2221Excess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    ∑ R ∈ (C.erase P).erase Q,
    (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)
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
    rw [Finset.sum_eq_zero]
    intro R hR
    exact doubledDoubledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
      ρ μG hN hN3 hρcont u u' hcard hnp hP hQ hR

/-- **Counting, card 4, support-only summand over one
seat**: each 4-support is counted once per seat. -/
theorem cnt4a (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, f C
      = 4 * ∑ C ∈ Finset.univ.powersetCard 4, f C := by
  classical
  rw [Finset.sum_congr rfl (fun C hC => by
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hC).2,
      nsmul_eq_mul, Nat.cast_ofNat]), Finset.mul_sum]

/-- **Counting, card 4, support-only summand over two
seats**: `4 · 3` ordered seat pairs. -/
theorem cnt4b (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, f C
      = 12 * ∑ C ∈ Finset.univ.powersetCard 4, f C := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, f C = 12 * f C := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP,
        hcard, show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, support-only summand over
three seats**: `4 · 3 · 2` ordered seat triples. -/
theorem cnt4c (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, f C
      = 24 * ∑ C ∈ Finset.univ.powersetCard 4, f C := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, f C = 24 * f C := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      Finset.sum_congr rfl (fun P hP => by
        rw [← Finset.mul_sum, Finset.sum_const,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, first-seat summand over two
seats**: the second seat contributes a factor `3`. -/
theorem cnt4d (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, g C P
      = 3 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, g C P
        = 3 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP,
        hcard, show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, second-seat summand over two
seats**: by the erase swap, also a factor `3`. -/
theorem cnt4e (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, g C Q
      = 3 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, g C Q
        = 3 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [sum_sum_erase_swap C (fun P Q => g C Q),
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          hcard, show (4 - 1 : ℕ) = 3 from rfl,
          nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, first-seat summand over three
seats**: the remaining seats contribute `3 · 2`. -/
theorem cnt4f (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, g C P
      = 6 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, g C P
        = 6 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      Finset.sum_congr rfl (fun P hP => by
        rw [← Finset.mul_sum, Finset.sum_const,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, second-seat summand over
three seats**: also `3 · 2`. -/
theorem cnt4g (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, g C Q
      = 6 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, g C Q
        = 6 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      sum_sum_erase_swap C
        (fun P Q => (2 : ℝ) * g C Q),
      Finset.sum_congr rfl (fun Q hQ => by
        rw [← Finset.mul_sum, Finset.sum_const,
          Finset.card_erase_of_mem hQ, hcard,
          show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, third-seat summand over three
seats**: also `3 · 2`. -/
theorem cnt4h (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, g C R
      = 6 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, g C R
        = 6 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P _ =>
      sum_sum_erase_swap (C.erase P) (fun Q R => g C R)),
      Finset.sum_congr rfl (fun P hP =>
        Finset.sum_congr rfl (fun R hR => by
          rw [Finset.sum_const, Finset.card_erase_of_mem hR,
            Finset.card_erase_of_mem hP, hcard,
            show (4 - 1 : ℕ) = 3 from rfl,
            show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      sum_sum_erase_swap C (fun P R => (2 : ℝ) * g C R),
      Finset.sum_congr rfl (fun R hR => by
        rw [← Finset.mul_sum, Finset.sum_const,
          Finset.card_erase_of_mem hR, hcard,
          show (4 - 1 : ℕ) = 3 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, pair summand over three
seats, first pair**: the third seat contributes
a factor `2`. -/
theorem cnt4i
    (h : Finset (LayerColumn N) → LayerColumn N → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, h C P Q
      = 2 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
          ∑ Q ∈ C.erase P, h C P Q := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, h C P Q
        = 2 * ∑ P ∈ C, ∑ Q ∈ C.erase P, h C P Q := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          Finset.card_erase_of_mem hP, hcard,
          show (4 - 1 : ℕ) = 3 from rfl,
          show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      Finset.sum_congr rfl (fun P _ => by
        rw [← Finset.mul_sum])]
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, pair summand over three
seats, split pair `(P, R)`**: also a factor `2`. -/
theorem cnt4j
    (h : Finset (LayerColumn N) → LayerColumn N → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, h C P R
      = 2 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
          ∑ Q ∈ C.erase P, h C P Q := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, h C P R
        = 2 * ∑ P ∈ C, ∑ Q ∈ C.erase P, h C P Q := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P _ =>
      sum_sum_erase_swap (C.erase P) (fun Q R => h C P R)),
      Finset.sum_congr rfl (fun P hP =>
        Finset.sum_congr rfl (fun R hR => by
          rw [Finset.sum_const, Finset.card_erase_of_mem hR,
            Finset.card_erase_of_mem hP, hcard,
            show (4 - 1 : ℕ) = 3 from rfl,
            show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul, Nat.cast_ofNat])),
      Finset.sum_congr rfl (fun P _ => by
        rw [← Finset.mul_sum])]
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 4, pair summand over three
seats, second pair `(Q, R)`**: also a factor `2`
(the free seat is rotated to the innermost sum,
where it contributes the constant count `2`). -/
theorem cnt4k
    (h : Finset (LayerColumn N) → LayerColumn N → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, h C Q R
      = 2 * ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
          ∑ Q ∈ C.erase P, h C P Q := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 4,
      ∑ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, h C Q R
        = 2 * ∑ P ∈ C, ∑ Q ∈ C.erase P, h C P Q := by
    intro C hC
    have hcard : C.card = 4 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [sum_sum_erase_swap C
        (fun P Q => ∑ R ∈ (C.erase P).erase Q, h C Q R),
      Finset.sum_congr rfl (fun Q _ =>
        Finset.sum_congr rfl (fun P _ => by
          rw [Finset.erase_right_comm])),
      Finset.sum_congr rfl (fun Q _ =>
        sum_sum_erase_swap (C.erase Q) (fun P R => h C Q R)),
      Finset.sum_congr rfl (fun Q hQ =>
        Finset.sum_congr rfl (fun R hR => by
          rw [Finset.sum_const, Finset.card_erase_of_mem hR,
            Finset.card_erase_of_mem hQ, hcard,
            show (4 - 1 : ℕ) = 3 from rfl,
            show (3 - 1 : ℕ) = 2 from rfl, nsmul_eq_mul,
            Nat.cast_ofNat])),
      Finset.sum_congr rfl (fun Q _ => by
        rw [← Finset.mul_sum]),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 5, support-only summand over one
seat**: factor `5`. -/
theorem cnt5a (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, f C
      = 5 * ∑ C ∈ Finset.univ.powersetCard 5, f C := by
  classical
  rw [Finset.sum_congr rfl (fun C hC => by
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hC).2,
      nsmul_eq_mul, Nat.cast_ofNat]), Finset.mul_sum]

/-- **Counting, card 5, support-only summand over two
seats**: factor `5 · 4`. -/
theorem cnt5b (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, f C
      = 20 * ∑ C ∈ Finset.univ.powersetCard 5, f C := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 5,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, f C = 20 * f C := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP,
        hcard, show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 5, first-seat summand over two
seats**: factor `4`. -/
theorem cnt5c (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, g C P
      = 4 * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 5,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, g C P
        = 4 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [Finset.sum_congr rfl (fun P hP => by
      rw [Finset.sum_const, Finset.card_erase_of_mem hP,
        hcard, show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 5, second-seat summand over two
seats**: factor `4`. -/
theorem cnt5d (g : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, g C Q
      = 4 * ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, g C P := by
  classical
  have key : ∀ C ∈ Finset.univ.powersetCard 5,
      ∑ P ∈ C, ∑ Q ∈ C.erase P, g C Q
        = 4 * ∑ P ∈ C, g C P := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [sum_sum_erase_swap C (fun P Q => g C Q),
      Finset.sum_congr rfl (fun Q hQ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hQ,
          hcard, show (5 - 1 : ℕ) = 4 from rfl,
          nsmul_eq_mul, Nat.cast_ofNat]),
      Finset.mul_sum]
  rw [Finset.sum_congr rfl key, Finset.mul_sum]

/-- **Counting, card 6, support-only summand over one
seat**: factor `6`. -/
theorem cnt6a (f : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, f C
      = 6 * ∑ C ∈ Finset.univ.powersetCard 6, f C := by
  classical
  rw [Finset.sum_congr rfl (fun C hC => by
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hC).2,
      nsmul_eq_mul, Nat.cast_ofNat]), Finset.mul_sum]

/-- **Erasure rotation at card 5**: in a triple sum
over distinct seats of a 5-support, the erased seat
can be rotated to the front. -/
theorem sum_erase_rotate5
    (F : Finset (LayerColumn N) → LayerColumn N → LayerColumn N → ℝ)
    (C : Finset (LayerColumn N)) :
    ∑ P ∈ C, ∑ Q ∈ C.erase P,
      ∑ R ∈ (C.erase P).erase Q, F (C.erase R) P Q
      = ∑ R ∈ C, ∑ P ∈ C.erase R,
        ∑ Q ∈ (C.erase R).erase P, F (C.erase R) P Q := by
  classical
  have step1 : ∀ P ∈ C, ∑ Q ∈ C.erase P,
        ∑ R ∈ (C.erase P).erase Q, F (C.erase R) P Q
      = ∑ R ∈ C.erase P, ∑ Q ∈ (C.erase P).erase R,
          F (C.erase R) P Q := by
    intro P _
    exact sum_sum_erase_swap (C.erase P)
      (fun Q R => F (C.erase R) P Q)
  rw [Finset.sum_congr rfl step1,
    sum_sum_erase_swap C
      (fun P R => ∑ Q ∈ (C.erase P).erase R, F (C.erase R) P Q)]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl
    fun P hP => ?_
  rw [Finset.erase_right_comm]
/-- **The tripled-penta excess sum at one 5-support,
factored** (the `μ₃` analogue of
`doubledPenta_excess_sum_factor`): a private column
of the support splits the sum into `μ₃` times the
erased quad excesses plus `e₁` times the erased
tripled excesses; all other erasures are
non-primitive and vanish. -/
theorem tripledPenta_excess_sum_factor (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ P ∈ C, (tripledQuadReMoment ρ μG C P u u'
        - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 3 * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
            (tripledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
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
  have hvantrip : ∀ x ∈ C, x ≠ X →
      ∑ P ∈ C.erase x,
          (tripledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) = 0 := by
    intro x hx hxX
    have hcard : (C.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hC]
    refine Finset.sum_eq_zero fun P hP => ?_
    exact tripledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG
      hN hN3 hρcont u u' hcard (hnp x hx hxX) hP
  have htermX : (tripledQuadReMoment ρ μG C X u u'
        - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 3
          * (quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 4) := by
    rw [tripledQuadReMoment_strip_tripled ρ μG hN hN3 hρcont
        u u' hsX hpriv]
    ring
  have hterm : ∀ P ∈ C.erase X,
      (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        = e1 ρ μG * (tripledQuadReMoment ρ μG (C.erase X) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
    intro P hP
    rw [tripledQuadReMoment_strip_single ρ μG hN hN3 hρcont
        u u' (Finset.mem_erase.mp hP).2 hXC
        (Ne.symm (Finset.mem_erase.mp hP).1) hsX hpriv]
    ring
  calc ∑ P ∈ C, (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
      = (tripledQuadReMoment ρ μG C X u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ∑ P ∈ C.erase X, (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4) :=
        (Finset.add_sum_erase C _ hXC).symm
    _ = realMoment ρ μG 3
            * (quadReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 4)
          + ∑ P ∈ C.erase X, e1 ρ μG
              * (tripledQuadReMoment ρ μG (C.erase X) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
          rw [htermX, Finset.sum_congr rfl hterm]
    _ = realMoment ρ μG 3 * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
              (tripledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) := by
          rw [← Finset.mul_sum]
          congr 1
          · exact congrArg (fun t => realMoment ρ μG 3 * t)
              (Finset.sum_eq_single X
                (fun x hx hxX => hvan4 x hx hxX)
                (fun h => absurd hXC h)).symm
          · exact congrArg (fun t => e1 ρ μG * t)
              (Finset.sum_eq_single X
                (fun x hx hxX => hvantrip x hx hxX)
                (fun h => absurd hXC h)).symm

/-- **The erased tripled excess sum at order 5,
converted**: summing the tripled excesses of all
erasures of all 5-supports counts each 4-support
`colCount N − 4` times. -/
theorem sum_powersetCard_five_tripled_erase (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ R ∈ C.erase P,
        (tripledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * kappa6chan3111Excess ρ μG u u' := by
  classical
  have hswap : ∀ C : Finset (LayerColumn N),
      (∑ P ∈ C, ∑ R ∈ C.erase P,
          (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
        = ∑ R ∈ C, ∑ P ∈ C.erase R,
            (tripledQuadReMoment ρ μG (C.erase R) P u u'
              - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) :=
    fun C => sum_sum_erase_swap C
      (fun a b => tripledQuadReMoment ρ μG (C.erase b) a u u'
        - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
  rw [Finset.sum_congr rfl (fun C _ => hswap C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T,
        (tripledQuadReMoment ρ μG T P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)),
    sum_powersetCard_four_tripled_excess ρ μG hN hN3 hρcont
      u u']

/-- **The tripled-penta excess sum, converted**:
`μ₃` times the dressed order-4 excess sum plus `e₁`
times the dressed `(3,1,1,1)` channel excess. -/
theorem sum_powersetCard_five_tripledPenta_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
      = realMoment ρ μG 3 * ((colCount N - 4)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4)
            * kappa6chan3111Excess ρ μG u u') := by
  classical
  have hF' : (∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
        ∑ P ∈ C.erase x,
          (tripledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = (colCount N - 4) * kappa6chan3111Excess ρ μG u u' := by
    rw [sum_powersetCard_five_erase_apply
        (fun T => ∑ P ∈ T,
          (tripledQuadReMoment ρ μG T P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)),
      sum_powersetCard_four_tripled_excess ρ μG hN hN3 hρcont
        u u']
  rw [Finset.sum_congr rfl (fun C hC =>
      tripledPenta_excess_sum_factor ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u',
    hF']

/-- **The doubled-doubled-penta excess sum at one
5-support, factored**: a private column splits the
ordered-pair sum into `2μ₂` times the erased doubled
excesses plus `e₁` times the erased doubled-doubled
excesses (the private column can sit in either
doubled seat, hence the `2`); all other erasures
are non-primitive and vanish. -/
theorem ddPenta_excess_sum_factor (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ P ∈ C, ∑ Q ∈ C.erase P,
        (doubledDoubledQuadReMoment ρ μG C P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
      = 2 * realMoment ρ μG 2 * ∑ x ∈ C, ∑ P ∈ C.erase x,
            (doubledQuadReMoment ρ μG (C.erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
            ∑ Q ∈ (C.erase x).erase P,
            (doubledDoubledQuadReMoment ρ μG (C.erase x) P Q u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
  classical
  obtain ⟨X, hXC, s, hsX, hpriv⟩ :=
    exists_private_column_of_card_five (N := N) hN hN3 hC
  have hnp : ∀ x ∈ C, x ≠ X → ¬ IsPrimitiveQuad (C.erase x) := by
    intro x hx hxX hprim
    have hXCx : X ∈ C.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxX, hXC⟩
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXCx s hsX
    exact hpriv Q (Finset.mem_erase.mp hQ).2 hQX hsQ
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
  have hvandd : ∀ x ∈ C, x ≠ X →
      ∑ P ∈ C.erase x, ∑ Q ∈ (C.erase x).erase P,
          (doubledDoubledQuadReMoment ρ μG (C.erase x) P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) = 0 := by
    intro x hx hxX
    have hcard : (C.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hx, hC]
    refine Finset.sum_eq_zero fun P hP =>
      Finset.sum_eq_zero fun Q hQ => ?_
    exact doubledDoubledQuadReMoment_sub_eq_zero_of_not_primitive
      ρ μG hN hN3 hρcont u u' hcard (hnp x hx hxX) hP hQ
  have htermX : ∑ Q ∈ C.erase X,
        (doubledDoubledQuadReMoment ρ μG C X Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
      = realMoment ρ μG 2 * ∑ Q ∈ C.erase X,
          (doubledQuadReMoment ρ μG (C.erase X) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    have hQC : Q ∈ C := (Finset.mem_erase.mp hQ).2
    have hQP : Q ≠ X := (Finset.mem_erase.mp hQ).1
    rw [doubledDoubledQuadReMoment_strip_first ρ μG hN hN3
      hρcont u u' hQC hQP hsX hpriv]
    ring
  have hterm : ∀ P ∈ C.erase X,
      ∑ Q ∈ C.erase P,
          (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        = realMoment ρ μG 2
            * (doubledQuadReMoment ρ μG (C.erase X) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + e1 ρ μG * ∑ Q ∈ (C.erase X).erase P,
              (doubledDoubledQuadReMoment ρ μG (C.erase X) P Q
                u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
    intro P hP
    have hPC : P ∈ C := (Finset.mem_erase.mp hP).2
    have hPX : P ≠ X := (Finset.mem_erase.mp hP).1
    have hXPe : X ∈ C.erase P :=
      Finset.mem_erase.mpr ⟨Ne.symm hPX, hXC⟩
    rw [← Finset.add_sum_erase (C.erase P) _ hXPe]
    congr 1
    · rw [doubledDoubledQuadReMoment_strip_second ρ μG hN hN3
        hρcont u u' hPC (Ne.symm hPX) hsX hpriv]
      ring
    · have hset : (C.erase P).erase X = (C.erase X).erase P :=
        Finset.erase_right_comm
      rw [hset, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hQX : Q ≠ X :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hQ).2).1
      have hQC : Q ∈ C :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hQ).2).2
      have hQP : Q ≠ P := (Finset.mem_erase.mp hQ).1
      rw [doubledDoubledQuadReMoment_strip_single ρ μG hN hN3
        hρcont u u' hPC hQC hXC (Ne.symm hPX) (Ne.symm hQX)
        hQP hsX hpriv]
      ring
  have hS : (∑ x ∈ C, ∑ P ∈ C.erase x,
        (doubledQuadReMoment ρ μG (C.erase x) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ∑ P ∈ C.erase X,
          (doubledQuadReMoment ρ μG (C.erase X) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    Finset.sum_eq_single X
      (fun x hx hxX => hvandbl x hx hxX)
      (fun h => absurd hXC h)
  have hT : (∑ x ∈ C, ∑ P ∈ C.erase x,
        ∑ Q ∈ (C.erase x).erase P,
        (doubledDoubledQuadReMoment ρ μG (C.erase x) P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ∑ P ∈ C.erase X, ∑ Q ∈ (C.erase X).erase P,
          (doubledDoubledQuadReMoment ρ μG (C.erase X) P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    Finset.sum_eq_single X
      (fun x hx hxX => hvandd x hx hxX)
      (fun h => absurd hXC h)
  calc ∑ P ∈ C, ∑ Q ∈ C.erase P,
          (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
      = (∑ Q ∈ C.erase X,
            (doubledDoubledQuadReMoment ρ μG C X Q u u'
              - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3))
          + ∑ P ∈ C.erase X, ∑ Q ∈ C.erase P,
              (doubledDoubledQuadReMoment ρ μG C P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3) :=
        (Finset.add_sum_erase C _ hXC).symm
    _ = realMoment ρ μG 2 * ∑ Q ∈ C.erase X,
              (doubledQuadReMoment ρ μG (C.erase X) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ∑ P ∈ C.erase X, (realMoment ρ μG 2
              * (doubledQuadReMoment ρ μG (C.erase X) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + e1 ρ μG * ∑ Q ∈ (C.erase X).erase P,
                (doubledDoubledQuadReMoment ρ μG (C.erase X) P Q
                  u u'
                  - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
          rw [htermX, Finset.sum_congr rfl hterm]
    _ = 2 * realMoment ρ μG 2 * ∑ x ∈ C, ∑ P ∈ C.erase x,
              (doubledQuadReMoment ρ μG (C.erase x) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + e1 ρ μG * ∑ x ∈ C, ∑ P ∈ C.erase x,
              ∑ Q ∈ (C.erase x).erase P,
              (doubledDoubledQuadReMoment ρ μG (C.erase x) P Q
                u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← hS, ← hT]
          ring

/-- **The doubled-doubled-penta excess sum,
converted**: `2μ₂` times the dressed `(2,1,1,1)`
channel excess plus `e₁` times the dressed
`(2,2,1,1)` channel excess. -/
theorem sum_powersetCard_five_ddPenta_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (doubledDoubledQuadReMoment ρ μG C P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
      = 2 * realMoment ρ μG 2 * ((colCount N - 4)
            * kappa5chanExcess ρ μG u u')
        + e1 ρ μG * ((colCount N - 4)
            * kappa6chan2211Excess ρ μG u u') := by
  classical
  have hF1 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
        ∑ P ∈ C.erase x,
          (doubledQuadReMoment ρ μG (C.erase x) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = (colCount N - 4) * kappa5chanExcess ρ μG u u' := by
    rw [sum_powersetCard_five_erase_apply
        (fun T => ∑ P ∈ T,
          (doubledQuadReMoment ρ μG T P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
        u u']
  have hF2 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
        ∑ P ∈ C.erase x, ∑ Q ∈ (C.erase x).erase P,
          (doubledDoubledQuadReMoment ρ μG (C.erase x) P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = (colCount N - 4) * kappa6chan2211Excess ρ μG u u' := by
    rw [sum_powersetCard_five_erase_apply
        (fun T => ∑ P ∈ T, ∑ Q ∈ T.erase P,
          (doubledDoubledQuadReMoment ρ μG T P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)),
      sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
        hρcont u u']
  rw [Finset.sum_congr rfl (fun C hC =>
      ddPenta_excess_sum_factor ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hF1, hF2]
/-- **Erasure counting, 7 → 6 (generic)**: the
order-7 analogue of `sum_powersetCard_six_erase_apply`,
proved by the same indicator-and-bijection argument
with the card values shifted by one. -/
theorem sum_powersetCard_seven_erase_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 7, ∑ x ∈ C, g (C.erase x)
      = (colCount N - 6) * ∑ T ∈ Finset.univ.powersetCard 6, g T := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 7,
      ∑ x ∈ C, g (C.erase x)
        = ∑ x ∈ Finset.univ, (if x ∈ C then g (C.erase x)
            else 0) := fun C _ =>
    (Finset.sum_congr rfl (fun x hx => (if_pos hx).symm)).trans
      (Finset.sum_subset (Finset.subset_univ C)
        (fun x _ hx => if_neg hx))
  have step2 : ∀ x : LayerColumn N,
      ∑ C ∈ Finset.univ.powersetCard 7, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ T ∈ Finset.univ.powersetCard 6, (if x ∈ T then 0
          else g T) := by
    intro x
    have hA : ∑ C ∈ Finset.univ.powersetCard 7, (if x ∈ C then
          g (C.erase x) else 0)
      = ∑ C ∈ (Finset.univ.powersetCard 7).filter
          (fun C => x ∈ C), g (C.erase x) :=
      (Finset.sum_filter _ _).symm
    have hB : ∑ T ∈ Finset.univ.powersetCard 6, (if x ∈ T then 0
          else g T)
      = ∑ T ∈ (Finset.univ.powersetCard 6).filter
          (fun T => x ∉ T), g T := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hxT : x ∈ T <;> simp [hxT]
    rw [hA, hB]
    refine Finset.sum_bij (fun C _ => C.erase x) ?_ ?_ ?_ ?_
    · intro C hC
      have hC6 : C ∈ Finset.univ.powersetCard 7 :=
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
      have hT5 : T ∈ Finset.univ.powersetCard 6 :=
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
  have step3 : ∀ T ∈ Finset.univ.powersetCard 6,
      ∑ x ∈ Finset.univ, (if x ∈ T then (0 : ℝ) else g T)
        = (colCount N - 6) * g T := by
    intro T hT
    have hT5 : T.card = 6 := (Finset.mem_powersetCard.mp hT).2
    have h5M : 6 ≤ Fintype.card (LayerColumn N) := by
      have hle := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, hT5] at hle
    have hform : ∀ x : LayerColumn N,
        (if x ∈ T then (0 : ℝ) else g T)
        = (if x ∉ T then g T else 0) := fun x => (ite_not _ _ _).symm
    rw [Finset.sum_congr rfl (fun x _ => hform x),
      ← Finset.sum_filter, Finset.sum_const]
    have hcard : (Finset.univ.filter (fun x => x ∉ T)).card
        = Fintype.card (LayerColumn N) - 6 := by
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
/-- **6-subsets of a 7-support are its erasures**:
the card-7 analogue of
`sum_powersetCard_five_subset_eq_sum_erase`. -/
theorem sum_powersetCard_six_subset_eq_sum_erase
    (C : Finset (LayerColumn N)) (hC : C.card = 7)
    (f : Finset (LayerColumn N) → ℝ) :
    ∑ D ∈ Finset.powersetCard 6 C, f D
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
    have hcard : D.card = 6 := (Finset.mem_powersetCard.mp hD).2
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
/-- **The card-6 4-subset sum, generic in the
summand**: each 4-support lies in
`(colCount N − 4)(colCount N − 5)/2` 6-supports.
(The generic form of
`sum_powersetCard_six_quad_subset`.) -/
theorem sum_powersetCard_six_four_subset_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 6,
      ∑ T ∈ Finset.powersetCard 4 C, g T
      = ((colCount N - 4) * (colCount N - 5) / 2)
        * ∑ T ∈ Finset.univ.powersetCard 4, g T := by
  classical
  have h2 : 2 * (∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 4 C, g T)
      = (colCount N - 5) * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4, g T) := by
    have step1 : ∀ C ∈ Finset.univ.powersetCard 6,
        2 * ∑ T ∈ Finset.powersetCard 4 C, g T
          = ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase x),
              g T := by
      intro C hC
      have hC6 : C.card = 6 :=
        (Finset.mem_powersetCard.mp hC).2
      rw [two_mul_sum_powersetCard_four_subset C hC6 g,
        sum_powersetCard_five_subset_eq_sum_erase C hC6
          (fun D => ∑ T ∈ Finset.powersetCard 4 D, g T)]
    have step2 : (∑ C ∈ Finset.univ.powersetCard 6,
          ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase x),
            g T)
        = (colCount N - 5) * ∑ D ∈ Finset.univ.powersetCard 5,
            ∑ T ∈ Finset.powersetCard 4 D, g T :=
      sum_powersetCard_six_erase_apply
        (fun D => ∑ T ∈ Finset.powersetCard 4 D, g T)
    have step3 : (∑ D ∈ Finset.univ.powersetCard 5,
          ∑ T ∈ Finset.powersetCard 4 D, g T)
        = (colCount N - 4)
            * ∑ T ∈ Finset.univ.powersetCard 4, g T := by
      rw [Finset.sum_congr rfl (fun D hD =>
          sum_powersetCard_four_subset_eq_sum_erase D
            (Finset.mem_powersetCard.mp hD).2 g)]
      exact sum_powersetCard_five_erase_apply g
    rw [Finset.mul_sum, Finset.sum_congr rfl step1, step2,
      step3]
  have hI : (∑ C ∈ Finset.univ.powersetCard 6,
        ∑ T ∈ Finset.powersetCard 4 C, g T)
      = ((colCount N - 5) * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4, g T)) / 2 := by
    linarith
  rw [hI]
  ring

/-- **The card-6 5-subset sum, generic in the
summand**: each 5-support lies in `colCount N − 5`
6-supports. -/
theorem sum_powersetCard_six_five_subset_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 6,
      ∑ T ∈ Finset.powersetCard 5 C, g T
      = (colCount N - 5)
        * ∑ T ∈ Finset.univ.powersetCard 5, g T := by
  classical
  rw [Finset.sum_congr rfl (fun C hC =>
      sum_powersetCard_five_subset_eq_sum_erase C
        (Finset.mem_powersetCard.mp hC).2 g)]
  exact sum_powersetCard_six_erase_apply g

/-- **The card-7 6-subset sum, generic in the
summand**: each 6-support lies in `colCount N − 6`
7-supports. -/
theorem sum_powersetCard_seven_six_subset_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 6 C, g T
      = (colCount N - 6)
        * ∑ T ∈ Finset.univ.powersetCard 6, g T := by
  classical
  rw [Finset.sum_congr rfl (fun C hC =>
      sum_powersetCard_six_subset_eq_sum_erase C
        (Finset.mem_powersetCard.mp hC).2 g)]
  exact sum_powersetCard_seven_erase_apply g
/-- **Two times the 5-subset sum of a 7-support**:
each 5-subset of a 7-support lies in exactly two
6-subsets (the card-7 analogue of
`two_mul_sum_powersetCard_four_subset`). -/
theorem two_mul_sum_powersetCard_five_subset
    (C : Finset (LayerColumn N)) (hC : C.card = 7)
    (f : Finset (LayerColumn N) → ℝ) :
    2 * ∑ T ∈ Finset.powersetCard 5 C, f T
      = ∑ D ∈ Finset.powersetCard 6 C,
          ∑ T ∈ Finset.powersetCard 5 D, f T := by
  classical
  have h1 : ∀ T ∈ Finset.powersetCard 5 C,
      ∑ z ∈ C \ T, f T = 2 * f T := by
    intro T hT
    have hsub : T ⊆ C := (Finset.mem_powersetCard.mp hT).1
    have hcard : T.card = 5 := (Finset.mem_powersetCard.mp hT).2
    rw [Finset.sum_const, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hsub, hC, hcard, nsmul_eq_mul]
    norm_num
  have hset : ∀ T : Finset (LayerColumn N),
      C.filter (fun z => z ∉ T) = C \ T := fun T =>
    Finset.ext fun z => by simp [Finset.mem_sdiff]
  have h2 : ∑ T ∈ Finset.powersetCard 5 C, ∑ z ∈ C \ T, f T
      = ∑ T ∈ Finset.powersetCard 5 C,
          ∑ z ∈ C, (if z ∉ T then f T else 0) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← hset T, Finset.sum_filter]
  have h3 : ∑ T ∈ Finset.powersetCard 5 C,
        ∑ z ∈ C, (if z ∉ T then f T else 0)
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 5 (C.erase z), f T := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hset : (Finset.powersetCard 5 C).filter (fun T => z ∉ T)
        = Finset.powersetCard 5 (C.erase z) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hzT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hzT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset z C), hcard⟩, ?_⟩
        exact fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    rw [← Finset.sum_filter, hset]
  have h4 : ∑ D ∈ Finset.powersetCard 6 C,
        ∑ T ∈ Finset.powersetCard 5 D, f T
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 5 (C.erase z), f T :=
    sum_powersetCard_six_subset_eq_sum_erase C hC
      (fun D => ∑ T ∈ Finset.powersetCard 5 D, f T)
  calc 2 * ∑ T ∈ Finset.powersetCard 5 C, f T
      = ∑ T ∈ Finset.powersetCard 5 C, ∑ z ∈ C \ T, f T := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T hT => (h1 T hT).symm
    _ = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 5 (C.erase z), f T :=
        h2.trans h3
    _ = ∑ D ∈ Finset.powersetCard 6 C,
          ∑ T ∈ Finset.powersetCard 5 D, f T := h4.symm
/-- **The card-7 5-subset sum, generic in the
summand**: each 5-support lies in
`(colCount N − 5)(colCount N − 6)/2` 7-supports. -/
theorem sum_powersetCard_seven_five_subset_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 5 C, g T
      = ((colCount N - 5) * (colCount N - 6) / 2)
        * ∑ T ∈ Finset.univ.powersetCard 5, g T := by
  classical
  have h2 : 2 * (∑ C ∈ Finset.univ.powersetCard 7,
        ∑ T ∈ Finset.powersetCard 5 C, g T)
      = (colCount N - 6) * ((colCount N - 5)
          * ∑ T ∈ Finset.univ.powersetCard 5, g T) := by
    have step1 : ∀ C ∈ Finset.univ.powersetCard 7,
        2 * ∑ T ∈ Finset.powersetCard 5 C, g T
          = ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 5 (C.erase x),
              g T := by
      intro C hC
      have hC7 : C.card = 7 :=
        (Finset.mem_powersetCard.mp hC).2
      rw [two_mul_sum_powersetCard_five_subset C hC7 g,
        sum_powersetCard_six_subset_eq_sum_erase C hC7
          (fun D => ∑ T ∈ Finset.powersetCard 5 D, g T)]
    have step2 : (∑ C ∈ Finset.univ.powersetCard 7,
          ∑ x ∈ C, ∑ T ∈ Finset.powersetCard 5 (C.erase x),
            g T)
        = (colCount N - 6) * ∑ D ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 5 D, g T :=
      sum_powersetCard_seven_erase_apply
        (fun D => ∑ T ∈ Finset.powersetCard 5 D, g T)
    have step3 : (∑ D ∈ Finset.univ.powersetCard 6,
          ∑ T ∈ Finset.powersetCard 5 D, g T)
        = (colCount N - 5)
            * ∑ T ∈ Finset.univ.powersetCard 5, g T := by
      rw [Finset.sum_congr rfl (fun D hD =>
          sum_powersetCard_five_subset_eq_sum_erase D
            (Finset.mem_powersetCard.mp hD).2 g)]
      exact sum_powersetCard_six_erase_apply g
    rw [Finset.mul_sum, Finset.sum_congr rfl step1, step2,
      step3]
  have hI : (∑ C ∈ Finset.univ.powersetCard 7,
        ∑ T ∈ Finset.powersetCard 5 C, g T)
      = ((colCount N - 6) * ((colCount N - 5)
          * ∑ T ∈ Finset.univ.powersetCard 5, g T)) / 2 := by
    linarith
  rw [hI]
  ring

/-- **Three times the 4-subset sum of a 7-support**:
each 4-subset of a 7-support lies in exactly three
6-subsets. -/
theorem three_mul_sum_powersetCard_four_subset
    (C : Finset (LayerColumn N)) (hC : C.card = 7)
    (f : Finset (LayerColumn N) → ℝ) :
    ∑ D ∈ Finset.powersetCard 6 C,
      ∑ T ∈ Finset.powersetCard 4 D, f T
      = 3 * ∑ T ∈ Finset.powersetCard 4 C, f T := by
  classical
  have h1 : ∀ T ∈ Finset.powersetCard 4 C,
      ∑ z ∈ C \ T, f T = 3 * f T := by
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
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase z),
          f T := by
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
  calc ∑ D ∈ Finset.powersetCard 6 C,
        ∑ T ∈ Finset.powersetCard 4 D, f T
      = ∑ z ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase z),
          f T :=
        sum_powersetCard_six_subset_eq_sum_erase C hC
          (fun D => ∑ T ∈ Finset.powersetCard 4 D, f T)
    _ = ∑ T ∈ Finset.powersetCard 4 C, ∑ z ∈ C \ T, f T :=
        (h2.trans h3).symm
    _ = 3 * ∑ T ∈ Finset.powersetCard 4 C, f T := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T hT => h1 T hT

/-- **The card-7 4-subset sum, generic in the
summand**: each 4-support lies in
`(colCount N − 4)(colCount N − 5)(colCount N − 6)/6`
7-supports. -/
theorem sum_powersetCard_seven_four_subset_apply
    (g : Finset (LayerColumn N) → ℝ) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 4 C, g T
      = ((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6)
        * ∑ T ∈ Finset.univ.powersetCard 4, g T := by
  classical
  have step2 : (∑ C ∈ Finset.univ.powersetCard 7,
        ∑ D ∈ Finset.powersetCard 6 C,
        ∑ T ∈ Finset.powersetCard 4 D, g T)
      = (colCount N - 6) * ∑ D ∈ Finset.univ.powersetCard 6,
          ∑ T ∈ Finset.powersetCard 4 D, g T := by
    rw [Finset.sum_congr rfl (fun C hC =>
        sum_powersetCard_six_subset_eq_sum_erase C
          (Finset.mem_powersetCard.mp hC).2
          (fun D => ∑ T ∈ Finset.powersetCard 4 D, g T))]
    exact sum_powersetCard_seven_erase_apply
      (fun D => ∑ T ∈ Finset.powersetCard 4 D, g T)
  have h3 : 3 * (∑ C ∈ Finset.univ.powersetCard 7,
        ∑ T ∈ Finset.powersetCard 4 C, g T)
      = (colCount N - 6)
          * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4, g T) := by
    calc 3 * (∑ C ∈ Finset.univ.powersetCard 7,
          ∑ T ∈ Finset.powersetCard 4 C, g T)
        = ∑ C ∈ Finset.univ.powersetCard 7,
            ∑ D ∈ Finset.powersetCard 6 C,
            ∑ T ∈ Finset.powersetCard 4 D, g T := by
          rw [Finset.mul_sum, Finset.sum_congr rfl
            (fun C hC => (three_mul_sum_powersetCard_four_subset
              C (Finset.mem_powersetCard.mp hC).2 g).symm)]
      _ = (colCount N - 6) * ∑ D ∈ Finset.univ.powersetCard 6,
            ∑ T ∈ Finset.powersetCard 4 D, g T := step2
      _ = (colCount N - 6)
            * (((colCount N - 4) * (colCount N - 5) / 2)
              * ∑ T ∈ Finset.univ.powersetCard 4, g T) := by
          rw [sum_powersetCard_six_four_subset_apply g]
  have hI : (∑ C ∈ Finset.univ.powersetCard 7,
        ∑ T ∈ Finset.powersetCard 4 C, g T)
      = ((colCount N - 6)
          * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4, g T)) / 3 := by
    linarith
  rw [hI]
  ring
/-- **The erased quad excess, seen through the
second seat at order 5**: rotating the erasure to
the front and counting the free seat gives
`4 · (colCount N − 4)` times the order-4 excess
sum. -/
theorem sum_powersetCard_five_erase_quad_through (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ R ∈ C.erase P,
        (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4)
      = 4 * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ∑ R ∈ C.erase P,
          (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4))
        = ∑ R ∈ C, (4 : ℝ)
            * (quadReMoment ρ μG (C.erase R) u u'
              - (e1 ρ μG) ^ 4) := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [sum_sum_erase_swap C
      (fun P R => quadReMoment ρ μG (C.erase R) u u'
        - (e1 ρ μG) ^ 4)]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem hR, hcard,
      show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul,
      Nat.cast_ofNat]
  have step2 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ R ∈ C, (4 : ℝ)
          * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
        = 4 * ∑ R ∈ C,
            (quadReMoment ρ μG (C.erase R) u u'
              - (e1 ρ μG) ^ 4) := by
    intro C _
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl step1, Finset.sum_congr rfl step2,
    ← Finset.mul_sum,
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u']

/-- **The rotated quad excess at order 5**: in the
`(2,2,1,1,1)`-family remainder sum, rotating the
erased seat to the front leaves the order-4 excess
sum dressed by `(colCount N − 4) · 12`. -/
theorem sum_powersetCard_five_rotate_quad (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (quadReMoment ρ μG (C.erase R) u u' - (e1 ρ μG) ^ 4)
      = (colCount N - 4) * (12
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  rw [Finset.sum_congr rfl (fun C _ => sum_erase_rotate5
      (fun T _ _ => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T, ∑ Q ∈ T.erase P,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)),
    cnt4b]

/-- **The rotated doubled excess at order 5, first
seat**: dressed by `(colCount N − 4) · 3`. -/
theorem sum_powersetCard_five_rotate_doubled_first (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (doubledQuadReMoment ρ μG (C.erase R) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * (3 * kappa5chanExcess ρ μG u u') := by
  classical
  rw [Finset.sum_congr rfl (fun C _ => sum_erase_rotate5
      (fun T P _ => doubledQuadReMoment ρ μG T P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T, ∑ Q ∈ T.erase P,
        (doubledQuadReMoment ρ μG T P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    cnt4d, sum_powersetCard_four_doubled_excess ρ μG hN hN3
      hρcont u u']

/-- **The rotated doubled excess at order 5, second
seat**: dressed by `(colCount N − 4) · 3`. -/
theorem sum_powersetCard_five_rotate_doubled_second (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (doubledQuadReMoment ρ μG (C.erase R) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * (3 * kappa5chanExcess ρ μG u u') := by
  classical
  rw [Finset.sum_congr rfl (fun C _ => sum_erase_rotate5
      (fun T _ Q => doubledQuadReMoment ρ μG T Q u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T, ∑ Q ∈ T.erase P,
        (doubledQuadReMoment ρ μG T Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    cnt4e, sum_powersetCard_four_doubled_excess ρ μG hN hN3
      hρcont u u']

/-- **The rotated doubled-doubled excess at order
5**: dressed by `colCount N − 4`. -/
theorem sum_powersetCard_five_rotate_dd (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        (doubledDoubledQuadReMoment ρ μG (C.erase R) P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
      = (colCount N - 4) * kappa6chan2211Excess ρ μG u u' := by
  classical
  rw [Finset.sum_congr rfl (fun C _ => sum_erase_rotate5
      (fun T P Q => doubledDoubledQuadReMoment ρ μG T P Q u u'
        - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T, ∑ Q ∈ T.erase P,
        (doubledDoubledQuadReMoment ρ μG T P Q u u'
          - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)),
    sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
      hρcont u u']

/-- **The erased quad excess over the free second
seat at order 5**: dressed by
`(colCount N − 4) · 4`. -/
theorem sum_powersetCard_five_erase_quad_seat (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4)
      = (colCount N - 4) * (4
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ∑ Q ∈ C.erase P,
          (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 4))
        = ∑ P ∈ C, (4 : ℝ)
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4) := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem hP, hcard,
      show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul,
      Nat.cast_ofNat]
  rw [Finset.sum_congr rfl step1,
    sum_powersetCard_five_erase_apply
      (fun T => (4 : ℝ) * (quadReMoment ρ μG T u u'
        - (e1 ρ μG) ^ 4)),
    ← Finset.mul_sum]

/-- **The erased doubled excess over its own seat
at order 5**: dressed by `colCount N − 4`. -/
theorem sum_powersetCard_five_erase_doubled_seat (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (doubledQuadReMoment ρ μG (C.erase P) Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * kappa5chanExcess ρ μG u u' := by
  classical
  rw [sum_powersetCard_five_erase_apply
      (fun T => ∑ Q ∈ T,
        (doubledQuadReMoment ρ μG T Q u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
      u u']

/-- **The erased quad excess over the free first
seat at order 5** (the mirror bracket): dressed by
`(colCount N − 4) · 4`. -/
theorem sum_powersetCard_five_erase_quad_seat2 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (quadReMoment ρ μG (C.erase Q) u u' - (e1 ρ μG) ^ 4)
      = (colCount N - 4) * (4
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ∑ Q ∈ C.erase P,
          (quadReMoment ρ μG (C.erase Q) u u' - (e1 ρ μG) ^ 4))
        = ∑ Q ∈ C, (4 : ℝ)
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4) := by
    intro C hC
    have hcard : C.card = 5 :=
      (Finset.mem_powersetCard.mp hC).2
    rw [sum_sum_erase_swap C
      (fun P Q => quadReMoment ρ μG (C.erase Q) u u'
        - (e1 ρ μG) ^ 4)]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem hQ, hcard,
      show (5 - 1 : ℕ) = 4 from rfl, nsmul_eq_mul,
      Nat.cast_ofNat]
  rw [Finset.sum_congr rfl step1,
    sum_powersetCard_five_erase_apply
      (fun T => (4 : ℝ) * (quadReMoment ρ μG T u u'
        - (e1 ρ μG) ^ 4)),
    ← Finset.mul_sum]

/-- **The erased doubled excess over the mirror
seat at order 5**: dressed by `colCount N − 4`. -/
theorem sum_powersetCard_five_erase_doubled_seat2 (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
      ∑ Q ∈ C.erase P,
        (doubledQuadReMoment ρ μG (C.erase Q) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = (colCount N - 4) * kappa5chanExcess ρ μG u u' := by
  classical
  have hswap : ∀ C : Finset (LayerColumn N),
      (∑ P ∈ C, ∑ Q ∈ C.erase P,
          (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = ∑ Q ∈ C, ∑ P ∈ C.erase Q,
            (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C => sum_sum_erase_swap C
      (fun a b => doubledQuadReMoment ρ μG (C.erase b) a u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
  rw [Finset.sum_congr rfl (fun C _ => hswap C),
    sum_powersetCard_five_erase_apply
      (fun T => ∑ P ∈ T,
        (doubledQuadReMoment ρ μG T P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
      u u']
/-- **The insert bijection**: summing a function
of `insert P T` over the `k`-subsets of `C ∸ P`
is summing it over the `(k+1)`-subsets of `C`
that contain `P`. -/
theorem sum_powersetCard_insert_apply (k : ℕ)
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (hP : P ∈ C) (f : Finset (LayerColumn N) → ℝ) :
    ∑ T ∈ Finset.powersetCard k (C.erase P), f (insert P T)
      = ∑ U ∈ (Finset.powersetCard (k + 1) C).filter
          (fun U => P ∈ U), f U := by
  classical
  refine Finset.sum_bij (fun T _ => insert P T) ?_ ?_ ?_ ?_
  · intro T hT
    have hsub : T ⊆ C.erase P :=
      (Finset.mem_powersetCard.mp hT).1
    have hcard : T.card = k :=
      (Finset.mem_powersetCard.mp hT).2
    have hPnot : P ∉ T :=
      fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset hP
          (hsub.trans (Finset.erase_subset P C)),
        by rw [Finset.card_insert_of_notMem hPnot, hcard]⟩,
      Finset.mem_insert_self P T⟩
  · intro T hT T' hT' h
    have hPnot : P ∉ T := fun hh =>
      (Finset.mem_erase.mp
        ((Finset.mem_powersetCard.mp hT).1 hh)).1 rfl
    have hPnot' : P ∉ T' := fun hh =>
      (Finset.mem_erase.mp
        ((Finset.mem_powersetCard.mp hT').1 hh)).1 rfl
    have h2 : (insert P T).erase P = (insert P T').erase P := by
      rw [h]
    rwa [Finset.erase_insert hPnot, Finset.erase_insert hPnot']
      at h2
  · intro U hU
    have hPU : P ∈ U := (Finset.mem_filter.mp hU).2
    have hsub : U ⊆ C :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hU).1).1
    have hcard : U.card = k + 1 :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hU).1).2
    refine ⟨U.erase P, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
      Finset.insert_erase hPU⟩
    · exact Finset.subset_erase.mpr
        ⟨(Finset.erase_subset P U).trans hsub,
          fun h => (Finset.mem_erase.mp h).1 rfl⟩
    · rw [Finset.card_erase_of_mem hPU, hcard,
        Nat.add_sub_cancel]
  · intro T _
    rfl

/-- **The containing-subset swap**: summing a
seat-dependent function over the `k`-subsets
containing each seat reassembles as the sum over
`k`-subsets of the sum over their own seats. -/
theorem sum_mem_filter_swap (C : Finset (LayerColumn N))
    (k : ℕ) (F : Finset (LayerColumn N) → LayerColumn N → ℝ) :
    ∑ P ∈ C, ∑ U ∈ (Finset.powersetCard k C).filter
        (fun U => P ∈ U), F U P
      = ∑ U ∈ Finset.powersetCard k C, ∑ P ∈ U, F U P := by
  classical
  rw [Finset.sum_congr rfl
    (fun P _ => Finset.sum_filter _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U hU => ?_
  have hsub : U ⊆ C := (Finset.mem_powersetCard.mp hU).1
  rw [← Finset.sum_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]

/-- **The containing-subset count**: a
seat-independent summand over the `k`-subsets
containing each seat reassembles with the factor
`k` (the subset's own cardinality). -/
theorem sum_mem_filter_card (C : Finset (LayerColumn N))
    (k : ℕ) (f : Finset (LayerColumn N) → ℝ) :
    ∑ P ∈ C, ∑ U ∈ (Finset.powersetCard k C).filter
        (fun U => P ∈ U), f U
      = ∑ U ∈ Finset.powersetCard k C, (k : ℝ) * f U := by
  classical
  rw [sum_mem_filter_swap C k (fun U _ => f U)]
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp hU).2,
    nsmul_eq_mul]

/-- **The erased 4-subset sum at order 6**: each
`(C, P)` sees the 4-subsets of `C ∸ P`; erasing
twice and counting gives
`(colCount N − 5)(colCount N − 4)` times the
order-4 excess sum. -/
theorem sum_powersetCard_six_erase_four_subset (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      ∑ T ∈ Finset.powersetCard 4 (C.erase P),
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      = (colCount N - 5) * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 6, ∀ P ∈ C,
      (∑ T ∈ Finset.powersetCard 4 (C.erase P),
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        = ∑ x ∈ C.erase P,
            (quadReMoment ρ μG ((C.erase x).erase P) u u'
              - (e1 ρ μG) ^ 4) := by
    intro C hC P hP
    have hcard : (C.erase P).card = 5 := by
      rw [Finset.card_erase_of_mem hP,
        (Finset.mem_powersetCard.mp hC).2]
    rw [sum_powersetCard_four_subset_eq_sum_erase (C.erase P)
      hcard (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.erase_right_comm]
  rw [Finset.sum_congr rfl (fun C hC =>
      Finset.sum_congr rfl (fun P hP => step1 C hC P hP)),
    Finset.sum_congr rfl (fun C _ => sum_sum_erase_swap C
      (fun P x => quadReMoment ρ μG ((C.erase x).erase P) u u'
        - (e1 ρ μG) ^ 4)),
    sum_powersetCard_six_erase_apply
      (fun D => ∑ P ∈ D,
        (quadReMoment ρ μG (D.erase P) u u' - (e1 ρ μG) ^ 4)),
    sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u']

/-- **The order-5 quad excess in penta dress**:
the plain 5-support excess sum is `e₁` times the
`(colCount N − 4)`-dressed order-4 excess sum. -/
theorem sum_powersetCard_five_penta_quad (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ D ∈ Finset.univ.powersetCard 5,
      (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 5)
      = e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have hqp : (∑ D ∈ Finset.univ.powersetCard 5,
        (quadReMoment ρ μG D u u' - (e1 ρ μG) ^ 5))
      = ∑ D ∈ Finset.univ.powersetCard 5,
          (pentaReMoment ρ μG D u u' - (e1 ρ μG) ^ 5) :=
    Finset.sum_congr rfl fun C _ => by
      rw [pentaReMoment_eq_quadReMoment]
  rw [hqp, sum_powersetCard_five_penta_excess ρ μG hN hN3
    hρcont u u']

/-- **The erased penta excess sum at order 6**:
dressed by `(colCount N − 5) · e₁(colCount N − 4)`
over the order-4 excess sum. -/
theorem sum_powersetCard_six_erase_penta (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      (quadReMoment ρ μG (C.erase P) u u' - (e1 ρ μG) ^ 5)
      = (colCount N - 5) * (e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
  classical
  rw [sum_powersetCard_six_erase_apply
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5),
    sum_powersetCard_five_penta_quad ρ μG hN hN3 hρcont u u']

/-- **The inserted quad excess sum at order 6**:
each 4-support is hit by `(colCount N − 4)
(colCount N − 5)` pairs `(C, P)` through the
insert bijection, as `4` times the card-6
4-subset count. -/
theorem sum_powersetCard_six_insert_quad (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      ∑ T ∈ Finset.powersetCard 3 (C.erase P),
        (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
      = 4 * (((colCount N - 4) * (colCount N - 5) / 2)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
  classical
  have hC : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ∑ T ∈ Finset.powersetCard 3 (C.erase P),
          (quadReMoment ρ μG (insert P T) u u'
            - (e1 ρ μG) ^ 4))
        = ∑ U ∈ Finset.powersetCard 4 C, (4 : ℝ)
            * (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 4) := by
    intro C _
    rw [Finset.sum_congr rfl (fun P hP =>
        sum_powersetCard_insert_apply 3 C P hP
          (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)),
      show (3 + 1 : ℕ) = 4 from rfl,
      sum_mem_filter_card C 4
        (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4),
      Nat.cast_ofNat]
  have hmul : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ U ∈ Finset.powersetCard 4 C, (4 : ℝ)
          * (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 4))
        = 4 * ∑ U ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hC, Finset.sum_congr rfl hmul,
    ← Finset.mul_sum, sum_powersetCard_six_four_subset_apply]

/-- **The inserted penta excess sum at order 6**:
`5 · (colCount N − 5) · e₁(colCount N − 4)` over
the order-4 excess sum. -/
theorem sum_powersetCard_six_insert_penta (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      ∑ T ∈ Finset.powersetCard 4 (C.erase P),
        (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
      = 5 * ((colCount N - 5) * (e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))) := by
  classical
  have hC : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase P),
          (quadReMoment ρ μG (insert P T) u u'
            - (e1 ρ μG) ^ 5))
        = ∑ U ∈ Finset.powersetCard 5 C, (5 : ℝ)
            * (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 5) := by
    intro C _
    rw [Finset.sum_congr rfl (fun P hP =>
        sum_powersetCard_insert_apply 4 C P hP
          (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)),
      show (4 + 1 : ℕ) = 5 from rfl,
      sum_mem_filter_card C 5
        (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5),
      Nat.cast_ofNat]
  have hmul : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ U ∈ Finset.powersetCard 5 C, (5 : ℝ)
          * (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 5))
        = 5 * ∑ U ∈ Finset.powersetCard 5 C,
            (quadReMoment ρ μG U u u' - (e1 ρ μG) ^ 5) :=
    fun C _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hC, Finset.sum_congr rfl hmul,
    ← Finset.mul_sum,
    sum_powersetCard_six_penta_subset ρ μG hN hN3 hρcont u u',
    sum_powersetCard_five_penta_quad ρ μG hN hN3 hρcont u u']

/-- **The seated hexa excess sum at order 6**:
`6` times the landed order-6 hexa conversion. -/
theorem sum_powersetCard_six_seat_hexa (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
      = 6 * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5)
              / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
                ∑ T ∈ Finset.powersetCard 4 C,
                  (quadReMoment ρ μG T u u'
                    - (e1 ρ μG) ^ 4))) := by
  classical
  rw [cnt6a, sum_powersetCard_six_hexaExcess_convert ρ μG hN
    hN3 hρcont u u']

/-- **The inserted doubled excess sum at order
6**: through the insert bijection and the swap,
the card-6 4-subset count of the order-5 channel
excess. -/
theorem sum_powersetCard_six_insert_doubled (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      ∑ T ∈ Finset.powersetCard 3 (C.erase P),
        (doubledQuadReMoment ρ μG (insert P T) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = ((colCount N - 4) * (colCount N - 5) / 2)
          * kappa5chanExcess ρ μG u u' := by
  classical
  have hC : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ∑ T ∈ Finset.powersetCard 3 (C.erase P),
          (doubledQuadReMoment ρ μG (insert P T) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = ∑ U ∈ Finset.powersetCard 4 C, ∑ P ∈ U,
            (doubledQuadReMoment ρ μG U P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    intro C _
    rw [Finset.sum_congr rfl (fun P hP =>
        sum_powersetCard_insert_apply 3 C P hP
          (fun U => doubledQuadReMoment ρ μG U P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      show (3 + 1 : ℕ) = 4 from rfl,
      sum_mem_filter_swap C 4
        (fun U P => doubledQuadReMoment ρ μG U P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)]
  rw [Finset.sum_congr rfl hC,
    sum_powersetCard_six_four_subset_apply
      (fun U => ∑ P ∈ U,
        (doubledQuadReMoment ρ μG U P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
    sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
      u u']

/-- **The inserted doubled-penta excess sum at
order 6**: through the insert bijection and the
swap, the card-6 5-subset count of the landed
order-5 doubled-penta conversion. -/
theorem sum_powersetCard_six_insert_doubledPenta (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      ∑ T ∈ Finset.powersetCard 4 (C.erase P),
        (doubledQuadReMoment ρ μG (insert P T) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
      = (colCount N - 5)
          * (realMoment ρ μG 2 * ((colCount N - 4)
              * ∑ T ∈ Finset.univ.powersetCard 4,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
            + e1 ρ μG * ((colCount N - 4)
              * kappa5chanExcess ρ μG u u')) := by
  classical
  have hC : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase P),
          (doubledQuadReMoment ρ μG (insert P T) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
        = ∑ U ∈ Finset.powersetCard 5 C, ∑ P ∈ U,
            (doubledQuadReMoment ρ μG U P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    intro C _
    rw [Finset.sum_congr rfl (fun P hP =>
        sum_powersetCard_insert_apply 4 C P hP
          (fun U => doubledQuadReMoment ρ μG U P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)),
      show (4 + 1 : ℕ) = 5 from rfl,
      sum_mem_filter_swap C 5
        (fun U P => doubledQuadReMoment ρ μG U P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)]
  have hbridge : (∑ U ∈ Finset.univ.powersetCard 5, ∑ P ∈ U,
        (doubledQuadReMoment ρ μG U P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ∑ U ∈ Finset.univ.powersetCard 5, ∑ P ∈ U,
          (doubledPentaReMoment ρ μG U P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
    Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl
      fun P _ => by
        rw [doubledPentaReMoment_eq_doubledQuadReMoment]
  rw [Finset.sum_congr rfl hC,
    sum_powersetCard_six_five_subset_apply
      (fun U => ∑ P ∈ U,
        (doubledQuadReMoment ρ μG U P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)),
    hbridge, sum_powersetCard_five_doubledPenta_excess ρ μG hN
      hN3 hρcont u u']
/-- **Residual R1 (new at order 7)**: the doubled
excess summed over the 4-subsets of the `Θ`
supports — the doubled sibling of the order-6
residual `S4theta`, forced by the `(2,1,1,1,1,1)`
conversion on `Θ` supports, whose 4-subsets are
primitive (so their doubled excesses do not
vanish, unlike on the rest family). -/
noncomputable def theta4SubsetDoubledSum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ thetaSupports, ∑ T ∈ Finset.powersetCard 4 C,
    ∑ P ∈ T, (doubledQuadReMoment ρ μG T P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)

/-- **Residual R2 (new at order 7)**: the erased
hexa excess summed over the book (Θ(1,3,3))
supports — the part of the order-7 erasure sum
that the book supports do not return to the
order-6 pool. -/
noncomputable def bookHexaEraseSum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ theta133Supports, ∑ x ∈ C,
    (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6)

/-- **Residual R3 (new at order 7)**: the
4-subset quad excess summed over the book
(Θ(1,3,3)) supports — the part of the order-7
4-subset sum carried by the book supports. -/
noncomputable def book4SubsetSum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ theta133Supports, ∑ T ∈ Finset.powersetCard 4 C,
    (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)

/-- **The doubled excess over a 4-subset of a
`C₆` support vanishes seat by seat**: such a
4-subset is not primitive (the order-6 counting
argument), and the doubled excess vanishes on
non-primitive supports. -/
theorem doubled_excess_sum_eq_zero_of_subset_c6Supports
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C ∈ c6Supports) {T : Finset (LayerColumn N)}
    (hT : T ∈ Finset.powersetCard 4 C) :
    ∑ P ∈ T, (doubledQuadReMoment ρ μG T P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) = 0 := by
  classical
  obtain ⟨hsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  refine Finset.sum_eq_zero fun P hP => ?_
  refine doubledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG
    hN hN3 hρcont u u' hTcard ?_ hP
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

/-- **The doubled-hexa excess sum at a private
(rest) 6-support factors through its 4-subsets**:
`2μ₂e₁` times the 4-subset quad excess sum, plus
`e₁²` times the 4-subset doubled excess sum.
The private seat contributes `μ₂ · (e₁ · S)` by
the doubled strip and the penta erasure identity;
the remaining seats contribute
`e₁ · (μ₂ · S + e₁ · T)` by the single strip and
the order-5 doubled-penta factor identity; the
4-subsets through the private column are
non-primitive, so both subset sums run over the
erasure only. -/
theorem doubledHexaExcess_sum_eq_of_private (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 6) (X : LayerColumn N) (hX : X ∈ C)
    (s : LayerSite N) (hsX : s ∈ colSites X)
    (hdeg : siteDegree C s = 1) :
    ∑ P ∈ C, (doubledHexaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      = 2 * realMoment ρ μG 2 * e1 ρ μG
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        + (e1 ρ μG) ^ 2
          * ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
            (doubledQuadReMoment ρ μG T P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
  classical
  have hpriv : ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    intro Y hY hYX hsY
    have hdeg' : (C.filter (fun Q => s ∈ colSites Q)).card = 1 :=
      hdeg
    have hlt : 1 < (C.filter (fun Q => s ∈ colSites Q)).card :=
      Finset.one_lt_card.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hX, hsX⟩,
          Y, Finset.mem_filter.mpr ⟨hY, hsY⟩, Ne.symm hYX⟩
    omega
  have hDcard : (C.erase X).card = 5 := by
    rw [Finset.card_erase_of_mem hX, hC]
  have hnp : ∀ T ∈ Finset.powersetCard 4 C, X ∈ T →
      ¬ IsPrimitiveQuad T := by
    intro T hT hXT hprim
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXT s hsX
    exact hpriv Q ((Finset.mem_powersetCard.mp hT).1 hQ) hQX hsQ
  have hsplit : ∀ g : Finset (LayerColumn N) → ℝ,
      (∀ T ∈ Finset.powersetCard 4 C, X ∈ T → g T = 0) →
      (∑ T ∈ Finset.powersetCard 4 C, g T)
        = ∑ x ∈ C.erase X, g ((C.erase X).erase x) := by
    intro g hg
    have hset : (Finset.powersetCard 4 C).filter
        (fun T => ¬ X ∈ T) = Finset.powersetCard 4 (C.erase X) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hXT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hXT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset X C), hcard⟩, ?_⟩
        exact fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    have hsum := Finset.sum_filter_add_sum_filter_not
      (Finset.powersetCard 4 C) (fun T => X ∈ T) g
    have hzero : ∑ T ∈ (Finset.powersetCard 4 C).filter
        (fun T => X ∈ T), g T = 0 :=
      Finset.sum_eq_zero fun T hT => hg T
        (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
    rw [← hsum, hzero, hset, zero_add,
      sum_powersetCard_four_subset_eq_sum_erase (C.erase X)
        hDcard g]
  have hvanQ : ∀ T ∈ Finset.powersetCard 4 C, X ∈ T →
      (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) = 0 :=
    fun T hT hXT => excess_eq_zero_of_not_primitive ρ μG hN hN3
      hρcont u u' (Finset.mem_powersetCard.mp hT).2 (hnp T hT hXT)
  have hvanD : ∀ T ∈ Finset.powersetCard 4 C, X ∈ T →
      (∑ P ∈ T, (doubledQuadReMoment ρ μG T P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) = 0 :=
    fun T hT hXT => Finset.sum_eq_zero fun P hP =>
      doubledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG hN
        hN3 hρcont u u' (Finset.mem_powersetCard.mp hT).2
        (hnp T hT hXT) hP
  have htermX : (doubledHexaReMoment ρ μG C X u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      = realMoment ρ μG 2 * (e1 ρ μG)
          * ∑ x ∈ C.erase X,
            (quadReMoment ρ μG ((C.erase X).erase x) u u'
              - (e1 ρ μG) ^ 4) := by
    have h1 : doubledHexaReMoment ρ μG C X u u'
        = realMoment ρ μG 2
          * quadReMoment ρ μG (C.erase X) u u' :=
      doubledHexaReMoment_strip_doubled ρ μG hN hN3 hρcont
        u u' hsX hpriv
    have h2 := pentaExcess_eq_e1_sum_erase ρ μG hN hN3 hρcont
      u u' (C.erase X) hDcard
    have h3 : quadReMoment ρ μG (C.erase X) u u'
        = e1 ρ μG * ∑ x ∈ C.erase X,
            (quadReMoment ρ μG ((C.erase X).erase x) u u'
              - (e1 ρ μG) ^ 4) + (e1 ρ μG) ^ 5 := by
      linarith
    rw [h1, h3]
    ring
  have hterm : ∀ P ∈ C.erase X,
      (doubledHexaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      = e1 ρ μG * (doubledPentaReMoment ρ μG (C.erase X) P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) := by
    intro P hP
    have hPC : P ∈ C := (Finset.mem_erase.mp hP).2
    have hPX : P ≠ X := (Finset.mem_erase.mp hP).1
    rw [doubledHexaReMoment_strip_single ρ μG hN hN3 hρcont
        u u' hPC hX (Ne.symm hPX) hsX hpriv,
      doubledHexaReMoment_eq_doubledPentaReMoment]
    ring
  calc ∑ P ∈ C, (doubledHexaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      = (doubledHexaReMoment ρ μG C X u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
        + ∑ P ∈ C.erase X, (doubledHexaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) :=
        (Finset.add_sum_erase C _ hX).symm
    _ = realMoment ρ μG 2 * (e1 ρ μG)
          * ∑ x ∈ C.erase X,
            (quadReMoment ρ μG ((C.erase X).erase x) u u'
              - (e1 ρ μG) ^ 4)
        + e1 ρ μG * (realMoment ρ μG 2
          * ∑ x ∈ C.erase X,
            (quadReMoment ρ μG ((C.erase X).erase x) u u'
              - (e1 ρ μG) ^ 4)
          + e1 ρ μG * ∑ x ∈ C.erase X, ∑ P ∈ (C.erase X).erase x,
            (doubledQuadReMoment ρ μG ((C.erase X).erase x) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
        rw [htermX, Finset.sum_congr rfl hterm,
          ← Finset.mul_sum,
          doubledPenta_excess_sum_factor ρ μG hN hN3 hρcont u u'
            (C.erase X) hDcard]
    _ = 2 * realMoment ρ μG 2 * e1 ρ μG
          * ∑ T ∈ Finset.powersetCard 4 C,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        + (e1 ρ μG) ^ 2
          * ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
            (doubledQuadReMoment ρ μG T P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
        rw [hsplit (fun T => quadReMoment ρ μG T u u'
            - (e1 ρ μG) ^ 4) hvanQ,
          hsplit (fun T => ∑ P ∈ T,
            (doubledQuadReMoment ρ μG T P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) hvanD]
        ring

/-- **The order-7 `(2,1,1,1,1,1)` conversion**:
the seated doubled-hexa excess sum over all
6-supports is the two channel excesses (`C₆` and
`Θ`), plus `2μ₂e₁` times the order-6 `Θ` 4-subset
residual gap, plus `e₁²` times the doubled
sibling gap (residual R1). On the rest family the
private factor identity applies; on `C₆` supports
both subset sums vanish. -/
theorem sum_powersetCard_six_doubledHexaExcess_convert
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
      (doubledHexaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
      = kappa7chan211111C6Excess ρ μG u u'
        + kappa7chan211111ThetaExcess ρ μG u u'
        + 2 * realMoment ρ μG 2 * e1 ρ μG
          * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + (e1 ρ μG) ^ 2
          * (((colCount N - 4) * (colCount N - 5) / 2)
            * kappa5chanExcess ρ μG u u'
            - theta4SubsetDoubledSum ρ μG u u') := by
  classical
  have hC6 : (∑ C ∈ c6Supports, ∑ P ∈ C,
        (doubledHexaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = kappa7chan211111C6Excess ρ μG u u' := rfl
  have hTh : (∑ C ∈ thetaSupports, ∑ P ∈ C,
        (doubledHexaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = kappa7chan211111ThetaExcess ρ μG u u' := rfl
  have hRest : (∑ C ∈ (Finset.univ.powersetCard 6).filter
        (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
        ∑ P ∈ C, (doubledHexaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = 2 * realMoment ρ μG 2 * e1 ρ μG
          * ∑ C ∈ (Finset.univ.powersetCard 6).filter
            (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
            ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        + (e1 ρ μG) ^ 2
          * ∑ C ∈ (Finset.univ.powersetCard 6).filter
            (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
            ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
              (doubledQuadReMoment ρ μG T P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hCcard : C.card = 6 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).2
    have hnot : C ∉ c6Supports ∧ C ∉ thetaSupports :=
      (Finset.mem_filter.mp hC).2
    have hpriv : HasPrivateColumn C := by
      rcases mem_c6_or_theta_or_private_of_card_six hN hN3 C
          hCcard with h | h | h
      · exact absurd h hnot.1
      · exact absurd h hnot.2
      · exact h
    obtain ⟨X, hXC, s, hsX, hdeg⟩ := hpriv
    exact doubledHexaExcess_sum_eq_of_private ρ μG hN hN3
      hρcont u u' C hCcard X hXC s hsX hdeg
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
    have hI := sum_powersetCard_six_four_subset_apply
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
    linarith
  have hS4Dc6 : (∑ C ∈ c6Supports,
        ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
          (doubledQuadReMoment ρ μG T P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) = 0 :=
    Finset.sum_eq_zero fun C hC => Finset.sum_eq_zero fun T hT =>
      doubled_excess_sum_eq_zero_of_subset_c6Supports ρ μG hN
        hN3 hρcont u u' hC hT
  have hsplitS4D := sum_powersetCard_six_split_apply
    (fun C => ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
      (doubledQuadReMoment ρ μG T P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
  rw [hS4Dc6] at hsplitS4D
  have hRestS4D : (∑ C ∈ (Finset.univ.powersetCard 6).filter
        (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports),
        ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
          (doubledQuadReMoment ρ μG T P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((colCount N - 4) * (colCount N - 5) / 2)
          * kappa5chanExcess ρ μG u u'
        - theta4SubsetDoubledSum ρ μG u u' := by
    have hI := sum_powersetCard_six_four_subset_apply
      (fun T => ∑ P ∈ T,
        (doubledQuadReMoment ρ μG T P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
    rw [sum_powersetCard_four_doubled_excess ρ μG hN hN3
      hρcont u u'] at hI
    have htheta : (∑ C ∈ thetaSupports,
          ∑ T ∈ Finset.powersetCard 4 C, ∑ P ∈ T,
            (doubledQuadReMoment ρ μG T P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = theta4SubsetDoubledSum ρ μG u u' := rfl
    linarith
  rw [sum_powersetCard_six_split_apply
      (fun C => ∑ P ∈ C, (doubledHexaReMoment ρ μG C P u u'
        - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)),
    hC6, hTh, hRest, hRestS4, hRestS4D]
  ring
/-- **A non-book 7-support has a private column**:
the contrapositive of B7-0's card-7 classification
— a fully shared 7-support carries the
`Θ(1,3,3)` pattern. The multiplicity fed to the
classification is the support's indicator. -/
theorem hasPrivateColumn_of_not_mem_theta133Supports
    (hN : Even N) (hN3 : 3 ≤ N)
    {C : Finset (LayerColumn N)} (hC : C.card = 7)
    (hC7 : C ∉ theta133Supports) : HasPrivateColumn C := by
  classical
  by_contra hcon
  set m : LayerColumn N → ℕ := fun P => if P ∈ C then 1 else 0
    with hm_def
  have hmult : multSupport m = C := by
    refine Finset.ext fun P => ?_
    simp only [multSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, hm_def]
    constructor
    · intro h
      by_contra hPC
      rw [if_neg hPC] at h
      exact h rfl
    · intro hP
      rw [if_pos hP]
      exact one_ne_zero
  have hall : ∀ P ∈ multSupport m, m P = 1 := by
    intro P hP
    rw [hmult] at hP
    simp only [hm_def, if_pos hP]
  have hm7 : ∑ P, m P = 7 := by
    have h2 : ∀ P, m P = if P ∈ C then 1 else 0 := fun P => rfl
    rw [Finset.sum_congr rfl (fun P _ => h2 P),
      Finset.sum_boole, Finset.filter_univ_mem, Nat.cast_id,
      hC]
  have hW : WFullyShared m := by
    intro s hs
    rw [hmult] at hs
    rw [wSiteDegree_eq_siteDegree_of_all_one m hall s, hmult]
    obtain ⟨P, hPC, hsP⟩ := Finset.mem_biUnion.mp hs
    have hge1 : 1 ≤ siteDegree C s := by
      have hsd : siteDegree C s
          = (C.filter (fun P => s ∈ colSites P)).card := rfl
      rw [hsd]
      exact Finset.one_le_card.mpr
        ⟨P, Finset.mem_filter.mpr ⟨hPC, hsP⟩⟩
    have hne1 : siteDegree C s ≠ 1 := by
      intro hdeg
      exact hcon ⟨P, hPC, s, hsP, hdeg⟩
    omega
  have hpat := card_seven_classification hN hN3 m hm7 hW
    (by rw [hmult]; exact hC)
  rw [hmult] at hpat
  exact hC7 (Finset.mem_filter.mpr
    ⟨Finset.mem_univ C, hC, hpat⟩)

/-- **The hepta excess at a private 7-support**:
`e₁` times the full erasure hexa sum, minus
`2e₁³` times the 4-subset quad excess sum. The
private seat's erasure carries the strip; every
other erasure is a rest 6-support (the private
column stays private in it), whose hexa excess is
the `e₁²` 4-subset form; the double count of
4-subsets of the erased support is `2`, and the
4-subsets through the private column are
non-primitive. -/
theorem heptaExcess_eq_of_private (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 7) (X : LayerColumn N) (hX : X ∈ C)
    (s : LayerSite N) (hsX : s ∈ colSites X)
    (hdeg : siteDegree C s = 1) :
    heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7
      = e1 ρ μG * ∑ x ∈ C,
          (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6)
        - 2 * (e1 ρ μG) ^ 3 * ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
  classical
  have hpriv : ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    intro Y hY hYX hsY
    have hdeg' : (C.filter (fun Q => s ∈ colSites Q)).card = 1 :=
      hdeg
    have hlt : 1 < (C.filter (fun Q => s ∈ colSites Q)).card :=
      Finset.one_lt_card.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hX, hsX⟩,
          Y, Finset.mem_filter.mpr ⟨hY, hsY⟩, Ne.symm hYX⟩
    omega
  have hDcard : (C.erase X).card = 6 := by
    rw [Finset.card_erase_of_mem hX, hC]
  have hfact : quadReMoment ρ μG C u u'
      = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u' := by
    have hsF : ∀ P ∈ C.erase X, s ∉ colSites P :=
      fun P hP => hpriv P (Finset.mem_erase.mp hP).2
        (Finset.mem_erase.mp hP).1
    have hXF : X ∉ C.erase X :=
      fun h => (Finset.mem_erase.mp h).1 rfl
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
  have hnp : ∀ T ∈ Finset.powersetCard 4 C, X ∈ T →
      ¬ IsPrimitiveQuad T := by
    intro T hT hXT hprim
    obtain ⟨Q, hQ, hQX, hsQ⟩ := hprim.2 X hXT s hsX
    exact hpriv Q ((Finset.mem_powersetCard.mp hT).1 hQ) hQX hsQ
  have hsplitC : (∑ T ∈ Finset.powersetCard 4 C,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ∑ T ∈ Finset.powersetCard 4 (C.erase X),
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have hset : (Finset.powersetCard 4 C).filter
        (fun T => ¬ X ∈ T)
        = Finset.powersetCard 4 (C.erase X) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hXT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hXT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset X C), hcard⟩, ?_⟩
        exact fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    have hsum := Finset.sum_filter_add_sum_filter_not
      (Finset.powersetCard 4 C) (fun T => X ∈ T)
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
    have hzero : ∑ T ∈ (Finset.powersetCard 4 C).filter
        (fun T => X ∈ T),
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) = 0 :=
      Finset.sum_eq_zero fun T hT =>
        excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont u u'
          (Finset.mem_powersetCard.mp
            (Finset.mem_filter.mp hT).1).2
          (hnp T (Finset.mem_filter.mp hT).1
            (Finset.mem_filter.mp hT).2)
    rw [← hsum, hzero, hset, zero_add]
  have hrest : ∀ x ∈ C.erase X,
      C.erase x ∈ (Finset.univ.powersetCard 6).filter
        (fun C => C ∉ c6Supports ∧ C ∉ thetaSupports) := by
    intro x hx
    have hxC : x ∈ C := (Finset.mem_erase.mp hx).2
    have hxX : x ≠ X := (Finset.mem_erase.mp hx).1
    have hcard : (C.erase x).card = 6 := by
      rw [Finset.card_erase_of_mem hxC, hC]
    have hdegx : siteDegree (C.erase x) s = 1 := by
      have hfil : (C.erase x).filter (fun Q => s ∈ colSites Q)
          = {X} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨Ne.symm hxX, hX⟩, hsX⟩
        · intro Q hQ
          have hQC : Q ∈ C :=
            (Finset.mem_erase.mp (Finset.mem_filter.mp hQ).1).2
          by_contra hQX
          exact hpriv Q hQC hQX (Finset.mem_filter.mp hQ).2
      have hsd : siteDegree (C.erase x) s
          = ((C.erase x).filter (fun Q => s ∈ colSites Q)).card :=
        rfl
      rw [hsd, hfil, Finset.card_singleton]
    have hsSupp : s ∈ quadSupport (C.erase x) :=
      Finset.mem_biUnion.mpr
        ⟨X, Finset.mem_erase.mpr ⟨Ne.symm hxX, hX⟩, hsX⟩
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
        ?_, ?_⟩
    · intro hmem
      have hpat := (Finset.mem_filter.mp hmem).2.2
      have h2 := hpat.2 s hsSupp
      omega
    · intro hmem
      obtain ⟨-, a, b, hab, ha, hb, hda, hdb, hrest2⟩ :=
        (Finset.mem_filter.mp hmem).2.2
      by_cases hsa : s = a
      · rw [hsa, hda] at hdegx
        omega
      · by_cases hsb : s = b
        · rw [hsb, hdb] at hdegx
          omega
        · have h2 := hrest2 s hsSupp hsa hsb
          omega
  have hsplitx : ∀ x ∈ C.erase X,
      (∑ T ∈ Finset.powersetCard 4 (C.erase x),
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ∑ T ∈ Finset.powersetCard 4 ((C.erase X).erase x),
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    intro x hx
    have hxC : x ∈ C := (Finset.mem_erase.mp hx).2
    have hset : (Finset.powersetCard 4 (C.erase x)).filter
        (fun T => ¬ X ∈ T)
        = Finset.powersetCard 4 ((C.erase x).erase X) := by
      refine Finset.ext fun T => ?_
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hXT⟩
        exact ⟨Finset.subset_erase.mpr ⟨hsub, hXT⟩, hcard⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨hsub.trans (Finset.erase_subset X (C.erase x)),
          hcard⟩, ?_⟩
        exact fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    have hsum := Finset.sum_filter_add_sum_filter_not
      (Finset.powersetCard 4 (C.erase x)) (fun T => X ∈ T)
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
    have hzero : ∑ T ∈ (Finset.powersetCard 4 (C.erase x)).filter
        (fun T => X ∈ T),
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) = 0 :=
      Finset.sum_eq_zero fun T hT =>
        excess_eq_zero_of_not_primitive ρ μG hN hN3 hρcont u u'
          (Finset.mem_powersetCard.mp
            (Finset.mem_filter.mp hT).1).2
          (hnp T (Finset.mem_powersetCard.mpr
              ⟨(Finset.mem_powersetCard.mp
                (Finset.mem_filter.mp hT).1).1.trans
                (Finset.erase_subset x C),
                (Finset.mem_powersetCard.mp
                  (Finset.mem_filter.mp hT).1).2⟩)
            (Finset.mem_filter.mp hT).2)
    rw [← hsum, hzero, hset, zero_add, Finset.erase_right_comm]
  have hmain : (∑ x ∈ C,
        (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6))
      = (hexaReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 6)
        + 2 * (e1 ρ μG) ^ 2
          * ∑ T ∈ Finset.powersetCard 4 (C.erase X),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    have h2 : (∑ x ∈ C.erase X,
          ∑ T ∈ Finset.powersetCard 4 ((C.erase X).erase x),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        = 2 * ∑ T ∈ Finset.powersetCard 4 (C.erase X),
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
      calc (∑ x ∈ C.erase X,
            ∑ T ∈ Finset.powersetCard 4 ((C.erase X).erase x),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
          = ∑ D ∈ Finset.powersetCard 5 (C.erase X),
              ∑ T ∈ Finset.powersetCard 4 D,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
            (sum_powersetCard_five_subset_eq_sum_erase
              (C.erase X) hDcard
              (fun D => ∑ T ∈ Finset.powersetCard 4 D,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))).symm
        _ = 2 * ∑ T ∈ Finset.powersetCard 4 (C.erase X),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
            (two_mul_sum_powersetCard_four_subset (C.erase X)
              hDcard
              (fun T => quadReMoment ρ μG T u u'
                - (e1 ρ μG) ^ 4)).symm
    calc (∑ x ∈ C,
          (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6))
        = (hexaReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 6)
          + ∑ x ∈ C.erase X,
            (hexaReMoment ρ μG (C.erase x) u u'
              - (e1 ρ μG) ^ 6) :=
          (Finset.add_sum_erase C _ hX).symm
      _ = (hexaReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 6)
          + ∑ x ∈ C.erase X, (e1 ρ μG) ^ 2
            * ∑ T ∈ Finset.powersetCard 4 ((C.erase X).erase x),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
          refine congrArg _ (Finset.sum_congr rfl fun x hx => ?_)
          rw [hexaExcess_eq_e1_sq_sum_fourSubsets_of_mem_rest
            ρ μG hN hN3 hρcont u u' (hrest x hx), hsplitx x hx]
      _ = (hexaReMoment ρ μG (C.erase X) u u' - (e1 ρ μG) ^ 6)
          + 2 * (e1 ρ μG) ^ 2
            * ∑ T ∈ Finset.powersetCard 4 (C.erase X),
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
          rw [← Finset.mul_sum, h2]
          ring
  calc heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7
      = (e1 ρ μG) * quadReMoment ρ μG (C.erase X) u u'
          - (e1 ρ μG) ^ 7 := by
        rw [heptaReMoment_eq_quadReMoment, hfact]
    _ = (e1 ρ μG)
          * (hexaReMoment ρ μG (C.erase X) u u'
            - (e1 ρ μG) ^ 6) := by
        rw [hexaReMoment_eq_quadReMoment]
        ring
    _ = e1 ρ μG * ∑ x ∈ C,
          (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6)
        - 2 * (e1 ρ μG) ^ 3 * ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
        rw [hmain, hsplitC]
        ring
/-- **The card-7 4-subset conversion**: the
`(colCount N − 4)(colCount N − 5)(colCount N − 6)/6`
count of the order-4 excess sum (the generic
subset count itself). -/
theorem sum_powersetCard_seven_four_subset_convert
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 4 C,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      = ((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6)
        * ∑ T ∈ Finset.univ.powersetCard 4,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
  sum_powersetCard_seven_four_subset_apply
    (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)

/-- **The card-7 5-subset conversion**: the
`(colCount N − 5)(colCount N − 6)/2` count of the
order-5 penta-dressed excess sum. -/
theorem sum_powersetCard_seven_five_subset_convert
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 5 C,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
      = ((colCount N - 5) * (colCount N - 6) / 2)
        * (e1 ρ μG * ((colCount N - 4)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
  classical
  rw [sum_powersetCard_seven_five_subset_apply,
    sum_powersetCard_five_penta_quad ρ μG hN hN3 hρcont u u']

/-- **The card-7 6-subset conversion**:
`colCount N − 6` times the landed order-6 hexa
conversion (the summand is the quad-headed form
of the hexa excess). -/
theorem sum_powersetCard_seven_six_subset_convert
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      ∑ T ∈ Finset.powersetCard 6 C,
        (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
      = (colCount N - 6) * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5)
              / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
                ∑ T ∈ Finset.powersetCard 4 C,
                  (quadReMoment ρ μG T u u'
                    - (e1 ρ μG) ^ 4))) := by
  classical
  have hbridge : ∀ T : Finset (LayerColumn N),
      (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
        = (hexaReMoment ρ μG T u u' - (e1 ρ μG) ^ 6) :=
    fun T => by rw [hexaReMoment_eq_quadReMoment]
  rw [Finset.sum_congr rfl (fun C _ =>
      Finset.sum_congr rfl (fun T _ => hbridge T)),
    sum_powersetCard_seven_six_subset_apply,
    sum_powersetCard_six_hexaExcess_convert ρ μG hN hN3
      hρcont u u']

/-- **The order-7 hepta conversion**: the hepta
excess sum over all 7-supports is the book
channel excess, plus `e₁` times the
`(colCount N − 6)`-dressed order-6 hexa pool,
minus the two book residuals (R2: the book
erasure hexa sum; R3: the book 4-subset sum, at
`2e₁³`). On non-book supports the private factor
identity applies; the erasure and 4-subset totals
are the generic counts, with the book parts
peeled off as the residuals. -/
theorem sum_powersetCard_seven_heptaExcess_convert
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 7,
      (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)
      = kappa7chanTheta133Excess ρ μG u u'
        + e1 ρ μG * ((colCount N - 6)
          * ∑ D ∈ Finset.univ.powersetCard 6,
            (hexaReMoment ρ μG D u u' - (e1 ρ μG) ^ 6))
        - e1 ρ μG * bookHexaEraseSum ρ μG u u'
        - 2 * (e1 ρ μG) ^ 3
          * (((colCount N - 4) * (colCount N - 5)
              * (colCount N - 6) / 6)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - book4SubsetSum ρ μG u u') := by
  classical
  have hbookset : ((Finset.univ.powersetCard 7).filter
      (fun C => C ∈ theta133Supports)
      : Finset (Finset (LayerColumn N))) = theta133Supports := by
    refine Finset.ext fun S => ?_
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ S,
            card_eq_seven_of_mem_theta133Supports h⟩, h⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.powersetCard 7) (fun C => C ∈ theta133Supports)
    (fun C => heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)
  have hbook : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∈ theta133Supports),
        (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = kappa7chanTheta133Excess ρ μG u u' := by
    rw [hbookset]
    rfl
  have hnonbook : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∉ theta133Supports),
        (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = e1 ρ μG * ∑ C ∈ (Finset.univ.powersetCard 7).filter
          (fun C => C ∉ theta133Supports), ∑ x ∈ C,
            (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6)
        - 2 * (e1 ρ μG) ^ 3
          * ∑ C ∈ (Finset.univ.powersetCard 7).filter
            (fun C => C ∉ theta133Supports),
            ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hCcard : C.card = 7 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).2
    have hCnot : C ∉ theta133Supports :=
      (Finset.mem_filter.mp hC).2
    obtain ⟨X, hXC, s, hsX, hdeg⟩ :=
      hasPrivateColumn_of_not_mem_theta133Supports
        hN hN3 hCcard hCnot
    exact heptaExcess_eq_of_private ρ μG hN hN3 hρcont u u'
      C hCcard X hXC s hsX hdeg
  have hsplitE := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.powersetCard 7) (fun C => C ∈ theta133Supports)
    (fun C => ∑ x ∈ C,
      (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6))
  have hbookE : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∈ theta133Supports), ∑ x ∈ C,
          (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6))
      = bookHexaEraseSum ρ μG u u' := by
    rw [hbookset]
    rfl
  have hEt : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∉ theta133Supports), ∑ x ∈ C,
          (hexaReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 6))
      = (colCount N - 6)
          * ∑ D ∈ Finset.univ.powersetCard 6,
            (hexaReMoment ρ μG D u u' - (e1 ρ μG) ^ 6)
        - bookHexaEraseSum ρ μG u u' := by
    have hE := sum_powersetCard_seven_erase_apply
      (fun D => hexaReMoment ρ μG D u u' - (e1 ρ μG) ^ 6)
    linarith
  have hsplitQ := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.powersetCard 7) (fun C => C ∈ theta133Supports)
    (fun C => ∑ T ∈ Finset.powersetCard 4 C,
      (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
  have hbookQ : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∈ theta133Supports),
        ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = book4SubsetSum ρ μG u u' := by
    rw [hbookset]
    rfl
  have hQt : (∑ C ∈ (Finset.univ.powersetCard 7).filter
        (fun C => C ∉ theta133Supports),
        ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6)
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - book4SubsetSum ρ μG u u' := by
    have hQ := sum_powersetCard_seven_four_subset_apply
      (fun T => quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
    linarith
  rw [← hsplit, hbook, hnonbook, hEt, hQt]
  ring
/-- **Assembly of the `(4,1,1,1)` family**: the
summed pattern rest is the order-4 excess sum at
`16 d⁻⁴` per unit weight, the order-5 channel at
`-6 d⁻⁵`, the order-6 `(3,1,1,1)` channel at
`4 d⁻⁶`, and the order-7 `(4,1,1,1)` channel at
`-d⁻⁷`. -/
theorem sum_exagg4_4111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)))
      = 210 * (16 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5 * kappa5chanExcess ρ μG u u'
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * kappa6chan3111Excess ρ μG u u'
        - ((d : ℝ)⁻¹) ^ 7
          * kappa7chan4111Excess ρ μG u u') := by
    classical
  have hdist : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
      - 6 * ((d : ℝ)⁻¹) ^ 5
        * (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      + 4 * ((d : ℝ)⁻¹) ^ 6
        * (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
      - ((d : ℝ)⁻¹) ^ 7
        * (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4)
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - ((210 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
          * (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 6)
          * (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((210 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
          * (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3) := fun C _ P _ => by ring
  rw [Finset.sum_congr rfl (fun C hC =>
    Finset.sum_congr rfl (fun P hP => hdist C hC P hP))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have aA : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      = 4 * (((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4)
        * ∑ T ∈ Finset.univ.powersetCard 4,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    rw [cnt4a (fun C => ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4)
      * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)), ← Finset.mul_sum]
  have hmulB : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((210 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ((210 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u' := by
    rw [Finset.sum_congr rfl hmulB, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulC : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 6)
        * (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ P ∈ C, (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aC : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan3111Excess ρ μG u u' := by
    rw [Finset.sum_congr rfl hmulC, ← Finset.mul_sum,
      sum_powersetCard_four_tripled_excess ρ μG hN hN3
        hρcont u u']
  have hmulD : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((210 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ P ∈ C, (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aD : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ((210 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (quadrupledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
      = ((210 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * kappa7chan4111Excess ρ μG u u' := by
    rw [Finset.sum_congr rfl hmulD, ← Finset.mul_sum,
      sum_powersetCard_four_quadrupled_excess ρ μG hN hN3
        hρcont u u']
  rw [aA, aB, aC, aD]
  simp only [← Finset.sum_sub_distrib]
  ring

/-- **Assembly of the `(3,2,1,1)` family**: the
summed pattern rest is the order-4 excess sum at
`72 d⁻⁴` per unit weight, the order-5 channel at
`−27 d⁻⁵` (both doubled seats), the order-6
`(3,1,1,1)` channel at `6 d⁻⁶`, the order-6
`(2,2,1,1)` channel at `3 d⁻⁶`, and the order-7
`(3,2,1,1)` channel at `−d⁻⁷`. -/
theorem sum_exagg4_3211 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)))
    = 420 * (72 * ((d : ℝ)⁻¹) ^ 4
        * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      - 27 * ((d : ℝ)⁻¹) ^ 5 * kappa5chanExcess ρ μG u u'
      + 6 * ((d : ℝ)⁻¹) ^ 6
        * kappa6chan3111Excess ρ μG u u'
      + 3 * ((d : ℝ)⁻¹) ^ 6
        * kappa6chan2211Excess ρ μG u u'
      - ((d : ℝ)⁻¹) ^ 7
        * kappa7chan3211Excess ρ μG u u') := by
  classical
  have hdist : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      ∀ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ Q _ => by ring
  rw [Finset.sum_congr rfl (fun C hC =>
    Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => hdist C hC P hP Q hQ)))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have aA : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      = 12 * (((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    rw [cnt4b (fun C => ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 4)
      * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)), ← Finset.mul_sum]
  have hmulB : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 3 * (((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u') := by
    rw [cnt4d (fun C P => ((420 : ℝ) * 6 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulB, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulC : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aC : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 3 * (((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u') := by
    rw [cnt4e (fun C Q => ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulC, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulD : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ P ∈ C, (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aD : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = 3 * (((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan3111Excess ρ μG u u') := by
    rw [cnt4d (fun C P => ((420 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulD, ← Finset.mul_sum,
      sum_powersetCard_four_tripled_excess ρ μG hN hN3
        hρcont u u']
  have hmulE2 : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      (∑ Q ∈ C.erase P,
        ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulE1 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ P ∈ C, ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ => by rw [Finset.mul_sum]
  have aE : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan2211Excess ρ μG u u' := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulE2 C hC P hP)),
      Finset.sum_congr rfl hmulE1, ← Finset.mul_sum,
      sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulF2 : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      (∑ Q ∈ C.erase P,
        ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ Q ∈ C.erase P, (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulF1 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ Q ∈ C.erase P, (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ P ∈ C, ∑ Q ∈ C.erase P, (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2) :=
    fun C _ => by rw [Finset.mul_sum]
  have aF : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P,
        ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = ((420 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * kappa7chan3211Excess ρ μG u u' := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulF2 C hC P hP)),
      Finset.sum_congr rfl hmulF1, ← Finset.mul_sum,
      sum_powersetCard_four_tripledDoubled_excess ρ μG hN hN3
        hρcont u u']
  rw [aA, aB, aC, aD, aE, aF]
  simp only [← Finset.sum_sub_distrib]
  ring

/-- **Assembly of the `(2,2,2,1)` family**: the
summed pattern rest is the order-4 excess sum at
`192 d⁻⁴` per unit weight, the order-5 channel at
`−72 d⁻⁵` (all three doubled seats), the order-6
`(2,2,1,1)` channel at `12 d⁻⁶` (all three pairs),
and the order-7 `(2,2,2,1)` channel at `−d⁻⁷`. -/
theorem sum_exagg4_2221 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
      ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
      (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))
    = 105 * (192 * ((d : ℝ)⁻¹) ^ 4
        * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
      - 72 * ((d : ℝ)⁻¹) ^ 5 * kappa5chanExcess ρ μG u u'
      + 12 * ((d : ℝ)⁻¹) ^ 6
        * kappa6chan2211Excess ρ μG u u'
      - ((d : ℝ)⁻¹) ^ 7
        * kappa7chan2221Excess ρ μG u u') := by
  classical
  have hdist : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      ∀ Q ∈ C.erase P, ∀ R ∈ (C.erase P).erase Q,
      (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = ((105 : ℝ) * 8 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG) :=
    fun C _ P _ Q _ R _ => by ring
  rw [Finset.sum_congr rfl (fun C hC =>
    Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ =>
        Finset.sum_congr rfl (fun R hR =>
          hdist C hC P hP Q hQ R hR))))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have aA : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 8 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      = 24 * (((105 : ℝ) * 8 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    rw [cnt4c (fun C => ((105 : ℝ) * 8 * ((d : ℝ)⁻¹) ^ 4)
      * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)), ← Finset.mul_sum]
  have hmulB : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB1 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 6 * (((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u') := by
    rw [cnt4f (fun C P => ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulB, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have aB2 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 6 * (((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u') := by
    rw [cnt4g (fun C Q => ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulB, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have aB3 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 6 * (((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * kappa5chanExcess ρ μG u u') := by
    rw [cnt4h (fun C R => ((105 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5)
        * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)),
      Finset.sum_congr rfl hmulB, ← Finset.mul_sum,
      sum_powersetCard_four_doubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulC2 : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      (∑ Q ∈ C.erase P,
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulC1 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * ∑ P ∈ C, ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ => by rw [Finset.mul_sum]
  have aC1 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 2 * (((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan2211Excess ρ μG u u') := by
    rw [cnt4i (fun C P Q =>
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulC2 C hC P hP)),
      Finset.sum_congr rfl hmulC1, ← Finset.mul_sum,
      sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
        hρcont u u']
  have aC2 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 2 * (((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan2211Excess ρ μG u u') := by
    rw [cnt4j (fun C P R =>
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulC2 C hC P hP)),
      Finset.sum_congr rfl hmulC1, ← Finset.mul_sum,
      sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
        hρcont u u']
  have aC3 : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = 2 * (((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6)
        * kappa6chan2211Excess ρ μG u u') := by
    rw [cnt4k (fun C Q R =>
        ((105 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulC2 C hC P hP)),
      Finset.sum_congr rfl hmulC1, ← Finset.mul_sum,
      sum_powersetCard_four_doubledDoubled_excess ρ μG hN hN3
        hρcont u u']
  have hmulD3 : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ R ∈ (C.erase P).erase Q, (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG) :=
    fun C _ P _ Q _ => by rw [Finset.mul_sum]
  have hmulD2 : ∀ C ∈ Finset.univ.powersetCard 4, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ R ∈ (C.erase P).erase Q, (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulD1 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ P ∈ C, ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * ∑ P ∈ C, ∑ Q ∈ C.erase P,
          ∑ R ∈ (C.erase P).erase Q, (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG) :=
    fun C _ => by rw [Finset.mul_sum]
  have aD : (∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = ((105 : ℝ) * ((d : ℝ)⁻¹) ^ 7)
        * kappa7chan2221Excess ρ μG u u' := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP =>
          Finset.sum_congr rfl (fun Q hQ =>
            hmulD3 C hC P hP Q hQ))),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulD2 C hC P hP)),
      Finset.sum_congr rfl hmulD1, ← Finset.mul_sum,
      sum_powersetCard_four_tripledDoubledDoubled_excess
        ρ μG hN hN3 hρcont u u']
  rw [aA, aB1, aB2, aB3, aC1, aC2, aC3, aD]
  simp only [← Finset.sum_sub_distrib]
  ring

/-- **Assembly of the card-4 family** (B7-2b-iv):
the three pattern families sum to the order-4
excess sum at `53760 d⁻⁴`, the order-5 channel at
`−20160 d⁻⁵`, the order-6 channels at `3360 d⁻⁶`
and `2520 d⁻⁶`, and the order-7 channels at
`−210 d⁻⁷`, `−420 d⁻⁷`, `−105 d⁻⁷`. -/
theorem sum_exagg4_convert (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, (∑ P ∈ C, (210 : ℝ) * (4 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 4 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        - ((d : ℝ)⁻¹) ^ 7
          * (quadrupledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (420 : ℝ) * (6 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 6 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 3 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 2 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledDoubledQuadReMoment ρ μG C P Q u u'
            - realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P,
            ∑ R ∈ (C.erase P).erase Q, (105 : ℝ) * (8 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - 4 * ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C R u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C P R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledDoubledQuadReMoment ρ μG C Q R u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
            - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)))
      = 53760 * ((d : ℝ)⁻¹) ^ 4
          * ∑ T ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - 20160 * ((d : ℝ)⁻¹) ^ 5 * kappa5chanExcess ρ μG u u'
        + 3360 * ((d : ℝ)⁻¹) ^ 6
          * kappa6chan3111Excess ρ μG u u'
        + 2520 * ((d : ℝ)⁻¹) ^ 6
          * kappa6chan2211Excess ρ μG u u'
        - 210 * ((d : ℝ)⁻¹) ^ 7
          * kappa7chan4111Excess ρ μG u u'
        - 420 * ((d : ℝ)⁻¹) ^ 7
          * kappa7chan3211Excess ρ μG u u'
        - 105 * ((d : ℝ)⁻¹) ^ 7
          * kappa7chan2221Excess ρ μG u u' := by
  classical
  simp only [Finset.sum_add_distrib]
  rw [sum_exagg4_4111 ρ μG hN hN3 hρcont u u',
    sum_exagg4_3211 ρ μG hN hN3 hρcont u u',
    sum_exagg4_2221 ρ μG hN hN3 hρcont u u']
  ring

/-- **Assembly of the `(3,1,1,1,1)` family**: the
summed pattern rest, read off the landed
conversions: the penta pool at `-3 d⁻⁵` per unit
weight (five seats), the doubled pool at
`3 d⁻⁶`, the tripled pool at `-d⁻⁷`, the erased
order-4 pool at `d⁻⁴`, and the through-erasure
terms at `3 d⁻⁴`, `-3 d⁻⁵`, `d⁻⁶`. -/
theorem sum_exagg5_31111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))))
    = 840 * (- 15 * ((d : ℝ)⁻¹) ^ 5 * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
      + 3 * ((d : ℝ)⁻¹) ^ 6 * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
      - ((d : ℝ)⁻¹) ^ 7 * (realMoment ρ μG 3 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u'))
      + ((d : ℝ)⁻¹) ^ 4 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      + (3 * ((d : ℝ)⁻¹) ^ 4 * (4 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - 3 * ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * kappa5chanExcess ρ μG u u')
        + ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u'))) := by
  classical
  have hDPV : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) :=
    Finset.sum_congr rfl (fun C _ =>
      Finset.sum_congr rfl (fun P _ => by
        rw [doubledPentaReMoment_eq_doubledQuadReMoment]))
  have hpush : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (840 : ℝ) * (∑ R ∈ C.erase P, (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
      = ∑ R ∈ C.erase P, (((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4)
        - ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)) :=
    fun C _ P _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun R _ => by ring)
  have hdist : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
      = - ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P, (((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4)
          - ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)) := by
    intro C hC P hP
    rw [← hpush C hC P hP]
    ring
  rw [Finset.sum_congr rfl (fun C hC =>
    Finset.sum_congr rfl (fun P hP => hdist C hC P hP))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have aA1 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, - ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))
      = 5 * (- ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))) := by
    rw [cnt5a (fun C => - ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)), ← Finset.mul_sum,
      sum_powersetCard_five_penta_quad ρ μG hN hN3 hρcont u u']
  have hmulA2 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA2 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 6) * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u')) := by
    rw [Finset.sum_congr rfl hmulA2, ← Finset.mul_sum, hDPV,
      sum_powersetCard_five_doubledPenta_excess ρ μG hN hN3 hρcont u u']
  have hmulA3 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * ∑ P ∈ C, (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA3 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (realMoment ρ μG 3 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u')) := by
    rw [Finset.sum_congr rfl hmulA3, ← Finset.mul_sum,
      sum_powersetCard_five_tripledPenta_excess ρ μG hN hN3 hρcont u u']
  have hmulA4 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA4 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    rw [Finset.sum_congr rfl hmulA4, ← Finset.mul_sum,
      sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u']
  have hmulA5a2 : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ R ∈ C.erase P, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * ∑ R ∈ C.erase P, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulA5a1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * ∑ R ∈ C.erase P, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ R ∈ C.erase P, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA5a : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ R ∈ C.erase P,
        ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 4) * (4 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulA5a2 C hC P hP)),
      Finset.sum_congr rfl hmulA5a1, ← Finset.mul_sum,
      sum_powersetCard_five_erase_quad_through ρ μG hN hN3 hρcont u u']
  have hmulA5b2 : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ R ∈ C.erase P, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulA5b1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ R ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA5b : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ R ∈ C.erase P,
        ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * 3 * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 4) * kappa5chanExcess ρ μG u u') := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulA5b2 C hC P hP)),
      Finset.sum_congr rfl hmulA5b1, ← Finset.mul_sum,
      sum_powersetCard_five_doubled_erase ρ μG hN hN3 hρcont u u']
  have hmulA5c2 : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ R ∈ C.erase P, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ R ∈ C.erase P, (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulA5c1 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ R ∈ C.erase P, (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, ∑ R ∈ C.erase P, (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aA5c : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ R ∈ C.erase P,
        ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (tripledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 3))
      = ((840 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u') := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulA5c2 C hC P hP)),
      Finset.sum_congr rfl hmulA5c1, ← Finset.mul_sum,
      sum_powersetCard_five_tripled_erase ρ μG hN hN3 hρcont u u']
  rw [aA1, aA2, aA3, aA4, aA5a, aA5b, aA5c]
  simp only [← Finset.sum_sub_distrib]
  ring

/-- **Assembly of the `(2,2,1,1,1)` family**: the
summed pattern rest, read off the landed
conversions: the penta pool at `-4 d⁻⁵` per unit
weight (twenty seats), the doubled pool at
`2 d⁻⁶` on each seat (four seats each), the
doubled-doubled pool at `-d⁻⁷`, the erased
brackets at `2 d⁻⁴` / `-d⁻⁵` on each seat, and
the rotated terms at `4 d⁻⁴`, `-2 d⁻⁵`, `-2 d⁻⁵`,
`d⁻⁶`. -/
theorem sum_exagg5_22111 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))
    = 630 * (- 80 * ((d : ℝ)⁻¹) ^ 5 * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
      + 8 * ((d : ℝ)⁻¹) ^ 6 * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
      + 8 * ((d : ℝ)⁻¹) ^ 6 * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
      - ((d : ℝ)⁻¹) ^ 7 * (2 * realMoment ρ μG 2 * ((colCount N - 4) * kappa5chanExcess ρ μG u u')
        + e1 ρ μG * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u'))
      + (2 * ((d : ℝ)⁻¹) ^ 4 * ((colCount N - 4) * (4 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
      + (2 * ((d : ℝ)⁻¹) ^ 4 * ((colCount N - 4) * (4 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
      + (4 * ((d : ℝ)⁻¹) ^ 4 * ((colCount N - 4) * (12 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - 2 * ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * (3 * kappa5chanExcess ρ μG u u'))
        - 2 * ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * (3 * kappa5chanExcess ρ μG u u'))
        + ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u'))) := by
  classical
  have hDPV : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C,
        (doubledPentaReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)) :=
    Finset.sum_congr rfl (fun C _ =>
      Finset.sum_congr rfl (fun P _ => by
        rw [doubledPentaReMoment_eq_doubledQuadReMoment]))
  have hpush : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (630 : ℝ) * (∑ R ∈ (C.erase P).erase Q, (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)))
      = ∑ R ∈ (C.erase P).erase Q, (((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4)
        - ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        - ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) :=
    fun C _ P _ Q _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun R _ => by ring)
  have hdist : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)))
      = - ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4) - ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4) - ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q, (((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4)
          - ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          - ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
          + ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2)) := by
    intro C hC P hP Q hQ
    rw [← hpush C hC P hP Q hQ]
    ring
  rw [Finset.sum_congr rfl (fun C hC =>
    Finset.sum_congr rfl (fun P hP =>
      Finset.sum_congr rfl (fun Q hQ => hdist C hC P hP Q hQ)))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have aB1 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, - ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))
      = 20 * (- ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))) := by
    rw [cnt5b (fun C => - ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)), ← Finset.mul_sum,
      sum_powersetCard_five_penta_quad ρ μG hN hN3 hρcont u u']
  have hmulB2 : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB2 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = 4 * (((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))) := by
    rw [cnt5c (fun C P => ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)),
      Finset.sum_congr rfl hmulB2, ← Finset.mul_sum, hDPV,
      sum_powersetCard_five_doubledPenta_excess ρ μG hN hN3 hρcont u u']
  have aB3 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = 4 * (((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))) := by
    rw [cnt5d (fun C Q => ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)),
      Finset.sum_congr rfl hmulB2, ← Finset.mul_sum, hDPV,
      sum_powersetCard_five_doubledPenta_excess ρ μG hN hN3 hρcont u u']
  have hmulB4q : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB4p : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * ∑ P ∈ C, ∑ Q ∈ C.erase P, (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB4 : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (2 * realMoment ρ μG 2 * ((colCount N - 4) * kappa5chanExcess ρ μG u u')
        + e1 ρ μG * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u')) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB4q C hC P hP)),
      Finset.sum_congr rfl hmulB4p, ← Finset.mul_sum,
      sum_powersetCard_five_ddPenta_excess ρ μG hN hN3 hρcont u u']
  have hmulB5aq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB5ap : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB5a : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ((colCount N - 4) * (4 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB5aq C hC P hP)),
      Finset.sum_congr rfl hmulB5ap, ← Finset.mul_sum,
      sum_powersetCard_five_erase_quad_seat ρ μG hN hN3 hρcont u u']
  have hmulB5bq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB5bp : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB5b : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 4) * kappa5chanExcess ρ μG u u') := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB5bq C hC P hP)),
      Finset.sum_congr rfl hmulB5bp, ← Finset.mul_sum,
      sum_powersetCard_five_erase_doubled_seat ρ μG hN hN3 hρcont u u']
  have hmulB6aq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB6ap : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ Q ∈ C.erase P, (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB6a : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase Q) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ((colCount N - 4) * (4 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB6aq C hC P hP)),
      Finset.sum_congr rfl hmulB6ap, ← Finset.mul_sum,
      sum_powersetCard_five_erase_quad_seat2 ρ μG hN hN3 hρcont u u']
  have hmulB6bq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB6bp : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ Q ∈ C.erase P, (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB6b : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 4) * kappa5chanExcess ρ μG u u') := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB6bq C hC P hP)),
      Finset.sum_congr rfl hmulB6bp, ← Finset.mul_sum,
      sum_powersetCard_five_erase_doubled_seat2 ρ μG hN hN3 hρcont u u']
  have hmulB7ar : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (∑ R ∈ (C.erase P).erase Q, ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ∑ R ∈ (C.erase P).erase Q, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ P _ Q _ => by rw [Finset.mul_sum]
  have hmulB7aq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ∑ R ∈ (C.erase P).erase Q, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB7ap : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB7a : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * (quadReMoment ρ μG (C.erase R) u u'
            - (e1 ρ μG) ^ 4))
      = ((630 : ℝ) * 4 * ((d : ℝ)⁻¹) ^ 4) * ((colCount N - 4) * (12 * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP =>
          Finset.sum_congr rfl (fun Q hQ => hmulB7ar C hC P hP Q hQ))),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB7aq C hC P hP)),
      Finset.sum_congr rfl hmulB7ap, ← Finset.mul_sum,
      sum_powersetCard_five_rotate_quad ρ μG hN hN3 hρcont u u']
  have hmulB7br : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (∑ R ∈ (C.erase P).erase Q, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ Q _ => by rw [Finset.mul_sum]
  have hmulB7bq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB7bp : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB7b : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 4) * (3 * kappa5chanExcess ρ μG u u')) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP =>
          Finset.sum_congr rfl (fun Q hQ => hmulB7br C hC P hP Q hQ))),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB7bq C hC P hP)),
      Finset.sum_congr rfl hmulB7bp, ← Finset.mul_sum,
      sum_powersetCard_five_rotate_doubled_first ρ μG hN hN3 hρcont u u']
  have hmulB7cr : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (∑ R ∈ (C.erase P).erase Q, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ Q _ => by rw [Finset.mul_sum]
  have hmulB7cq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB7cp : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB7c : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((630 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 4) * (3 * kappa5chanExcess ρ μG u u')) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP =>
          Finset.sum_congr rfl (fun Q hQ => hmulB7cr C hC P hP Q hQ))),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB7cq C hC P hP)),
      Finset.sum_congr rfl hmulB7cp, ← Finset.mul_sum,
      sum_powersetCard_five_rotate_doubled_second ρ μG hN hN3 hρcont u u']
  have hmulB7dr : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      ∀ Q ∈ C.erase P,
      (∑ R ∈ (C.erase P).erase Q, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ R ∈ (C.erase P).erase Q, (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ Q _ => by rw [Finset.mul_sum]
  have hmulB7dq : ∀ C ∈ Finset.univ.powersetCard 5, ∀ P ∈ C,
      (∑ Q ∈ C.erase P, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ R ∈ (C.erase P).erase Q, (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ P _ => by rw [Finset.mul_sum]
  have hmulB7dp : ∀ C ∈ Finset.univ.powersetCard 5,
      (∑ P ∈ C, ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q, (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2) :=
    fun C _ => by rw [Finset.mul_sum]
  have aB7d : (∑ C ∈ Finset.univ.powersetCard 5, ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ R ∈ (C.erase P).erase Q,
        ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))
      = ((630 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u') := by
    rw [Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP =>
          Finset.sum_congr rfl (fun Q hQ => hmulB7dr C hC P hP Q hQ))),
      Finset.sum_congr rfl (fun C hC =>
        Finset.sum_congr rfl (fun P hP => hmulB7dq C hC P hP)),
      Finset.sum_congr rfl hmulB7dp, ← Finset.mul_sum,
      sum_powersetCard_five_rotate_dd ρ μG hN hN3 hρcont u u']
  rw [aB1, aB2, aB3, aB4, aB5a, aB5b, aB6a, aB6b, aB7a, aB7b,
    aB7c, aB7d]
  simp only [← Finset.sum_sub_distrib]
  ring

/-- **Assembly of the card-5 family** (B7-2b-iv):
the two pattern families sum to the totals read
off the landed conversions. -/
theorem sum_exagg5_convert (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, (∑ P ∈ C, (840 : ℝ) * (- 3 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 3 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (tripledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 3 * (e1 ρ μG) ^ 4)
        + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG (C.erase P) u u'
            - (e1 ρ μG) ^ 4)
        + ∑ R ∈ C.erase P,
          (3 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 3 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (tripledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 3 * (e1 ρ μG) ^ 3)))
        + ∑ P ∈ C, ∑ Q ∈ C.erase P, (630 : ℝ) * (- 4 * ((d : ℝ)⁻¹) ^ 5
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        + 2 * ((d : ℝ)⁻¹) ^ 6
          * (doubledQuadReMoment ρ μG C Q u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 7
          * (doubledDoubledQuadReMoment ρ μG C P Q u u'
            - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 3)
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase P) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase P) Q u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + (2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG (C.erase Q) u u'
              - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG (C.erase Q) P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        + ∑ R ∈ (C.erase P).erase Q,
          (4 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG (C.erase R) u u'
                - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG (C.erase R) Q u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * (doubledDoubledQuadReMoment ρ μG (C.erase R)
                  P Q u u'
                - (realMoment ρ μG 2) ^ 2 * (e1 ρ μG) ^ 2))))
      = 51240 * ((d : ℝ)⁻¹) ^ 4 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        - 63000 * ((d : ℝ)⁻¹) ^ 5 * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        + 12600 * ((d : ℝ)⁻¹) ^ 6 * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        + e1 ρ μG * ((colCount N - 4) * kappa5chanExcess ρ μG u u'))
        - 11340 * ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 4) * kappa5chanExcess ρ μG u u')
        + 840 * ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u')
        + 630 * ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u')
        - 840 * ((d : ℝ)⁻¹) ^ 7
          * (realMoment ρ μG 3 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
            + e1 ρ μG * ((colCount N - 4) * kappa6chan3111Excess ρ μG u u'))
        - 630 * ((d : ℝ)⁻¹) ^ 7 * (2 * realMoment ρ μG 2 * ((colCount N - 4) * kappa5chanExcess ρ μG u u')
        + e1 ρ μG * ((colCount N - 4) * kappa6chan2211Excess ρ μG u u')) := by
  classical
  rw [Finset.sum_add_distrib,
    sum_exagg5_31111 ρ μG hN hN3 hρcont u u',
    sum_exagg5_22111 ρ μG hN hN3 hρcont u u']
  ring
/-- **Assembly of the card-6 family** (B7-2b-iv):
the summed `W`-rest at weight `2520`, read off
the eight landed card-6 conversions. -/
theorem sum_w6rest_convert (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
            (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = 2520 * (((d : ℝ)⁻¹) ^ 4 * ((colCount N - 5) * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - ((d : ℝ)⁻¹) ^ 5 * ((colCount N - 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))))
        + 2 * ((d : ℝ)⁻¹) ^ 4 * (4 * (((colCount N - 4) * (colCount N - 5) / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))
        - 2 * ((d : ℝ)⁻¹) ^ 5 * (5 * ((colCount N - 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))))
        + 2 * ((d : ℝ)⁻¹) ^ 6 * (6 * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4))))
        - ((d : ℝ)⁻¹) ^ 5 * (((colCount N - 4) * (colCount N - 5) / 2) * kappa5chanExcess ρ μG u u')
        + ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 5)
          * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
            + e1 ρ μG * ((colCount N - 4)
              * kappa5chanExcess ρ μG u u')))
        - ((d : ℝ)⁻¹) ^ 7 * (kappa7chan211111C6Excess ρ μG u u'
        + kappa7chan211111ThetaExcess ρ μG u u'
        + 2 * realMoment ρ μG 2 * e1 ρ μG
          * (((colCount N - 4) * (colCount N - 5) / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4))
        + (e1 ρ μG) ^ 2
          * (((colCount N - 4) * (colCount N - 5) / 2) * kappa5chanExcess ρ μG u u'
            - theta4SubsetDoubledSum ρ μG u u'))) := by
  classical
  have hdist : ∀ C ∈ Finset.univ.powersetCard 6, ∀ P ∈ C,
      (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
        + ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
        - ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
        + ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
        - ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        + ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
        - ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) :=
    fun C _ P _ => by ring
  have step : ((((((((∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) - (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5))) + (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4))) - (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5))) + (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))) - (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))) + (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))) - (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)))
      = ∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C,
            (2520 : ℝ) * (((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4)
            - 2 * ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5)
            + 2 * ((d : ℝ)⁻¹) ^ 6
              * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6)
            - ((d : ℝ)⁻¹) ^ 5
              * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
            + ((d : ℝ)⁻¹) ^ 6
              * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 7
              * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun C hC =>
      Finset.sum_congr rfl (fun P hP => (hdist C hC P hP).symm))
  have hmulW1 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW1 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ((colCount N - 5) * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl hmulW1, ← Finset.mul_sum,
      sum_powersetCard_six_erase_four_subset ρ μG hN hN3 hρcont u u']
  have hmulW2 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW2 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (quadReMoment ρ μG (C.erase P) u u'
                - (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ((colCount N - 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))) := by
    rw [Finset.sum_congr rfl hmulW2, ← Finset.mul_sum,
      sum_powersetCard_six_erase_penta ρ μG hN hN3 hρcont u u']
  have hmulW3 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ P ∈ C, ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW3 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 4) * (4 * (((colCount N - 4) * (colCount N - 5) / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))) := by
    rw [Finset.sum_congr rfl hmulW3, ← Finset.mul_sum,
      sum_powersetCard_six_insert_quad ρ μG hN hN3 hρcont u u']
  have hmulW4 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW4 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (quadReMoment ρ μG (insert P T) u u' - (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 5) * (5 * ((colCount N - 5) * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))))) := by
    rw [Finset.sum_congr rfl hmulW4, ← Finset.mul_sum,
      sum_powersetCard_six_insert_penta ρ μG hN hN3 hρcont u u']
  have hmulW5 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW5 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (hexaReMoment ρ μG C u u' - (e1 ρ μG) ^ 6))
      = ((2520 : ℝ) * 2 * ((d : ℝ)⁻¹) ^ 6) * (6 * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4)))) := by
    rw [Finset.sum_congr rfl hmulW5, ← Finset.mul_sum,
      sum_powersetCard_six_seat_hexa ρ μG hN hN3 hρcont u u']
  have hmulW6 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ P ∈ C, ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW6 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 3 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (((colCount N - 4) * (colCount N - 5) / 2) * kappa5chanExcess ρ μG u u') := by
    rw [Finset.sum_congr rfl hmulW6, ← Finset.mul_sum,
      sum_powersetCard_six_insert_doubled ρ μG hN hN3 hρcont u u']
  have hmulW7 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ P ∈ C, ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW7 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 4 (C.erase P),
                (doubledQuadReMoment ρ μG (insert P T) P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 4))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ((colCount N - 5)
          * (realMoment ρ μG 2 * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
            + e1 ρ μG * ((colCount N - 4)
              * kappa5chanExcess ρ μG u u'))) := by
    rw [Finset.sum_congr rfl hmulW7, ← Finset.mul_sum,
      sum_powersetCard_six_insert_doubledPenta ρ μG hN hN3 hρcont u u']
  have hmulW8 : ∀ C ∈ Finset.univ.powersetCard 6,
      (∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * ∑ P ∈ C, (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5) :=
    fun C _ => by rw [Finset.mul_sum]
  have aW8 : (∑ C ∈ Finset.univ.powersetCard 6, ∑ P ∈ C, ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (doubledHexaReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = ((2520 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (kappa7chan211111C6Excess ρ μG u u'
        + kappa7chan211111ThetaExcess ρ μG u u'
        + 2 * realMoment ρ μG 2 * e1 ρ μG
          * (((colCount N - 4) * (colCount N - 5) / 2) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4))
        + (e1 ρ μG) ^ 2
          * (((colCount N - 4) * (colCount N - 5) / 2) * kappa5chanExcess ρ μG u u'
            - theta4SubsetDoubledSum ρ μG u u')) := by
    rw [Finset.sum_congr rfl hmulW8, ← Finset.mul_sum,
      sum_powersetCard_six_doubledHexaExcess_convert ρ μG hN hN3 hρcont u u']
  rw [← step, aW1, aW2, aW3, aW4, aW5, aW6, aW7, aW8]
  ring

/-- **Assembly of the card-7 family** (B7-2b-iv):
the summed `W`-rest at weight `5040`, read off
the four landed card-7 conversions, with the raw
order-6 hexa pool inside the hepta term folded
through the landed order-6 conversion. -/
theorem sum_w7rest_convert (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 7,
            (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = 5040 * (((d : ℝ)⁻¹) ^ 4 * (((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        - ((d : ℝ)⁻¹) ^ 5 * (((colCount N - 5) * (colCount N - 6) / 2)
        * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))))
        + ((d : ℝ)⁻¹) ^ 6 * ((colCount N - 6) * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4))))
        - ((d : ℝ)⁻¹) ^ 7 * (kappa7chanTheta133Excess ρ μG u u'
        + e1 ρ μG * ((colCount N - 6) * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4))))
        - e1 ρ μG * bookHexaEraseSum ρ μG u u'
        - 2 * (e1 ρ μG) ^ 3
          * (((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - book4SubsetSum ρ μG u u'))) := by
  classical
  have hdist : ∀ C ∈ Finset.univ.powersetCard 7,
      (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
        - ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
        + ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
        - ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7) :=
    fun C _ => by ring
  have step : (((∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) - (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5))) + (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6))) - (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = ∑ C ∈ Finset.univ.powersetCard 7,
            (5040 : ℝ) * (((d : ℝ)⁻¹) ^ 4
            * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
          + ((d : ℝ)⁻¹) ^ 6
            * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6)
          - ((d : ℝ)⁻¹) ^ 7
            * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C hC => (hdist C hC).symm)
  have aZ1 : (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * ∑ T ∈ Finset.powersetCard 4 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 4) * (((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    rw [← Finset.mul_sum,
      sum_powersetCard_seven_four_subset_convert ρ μG hN hN3 hρcont u u']
  have aZ2 : (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * ∑ T ∈ Finset.powersetCard 5 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5))
      = ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 5) * (((colCount N - 5) * (colCount N - 6) / 2)
        * (e1 ρ μG * ((colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)))) := by
    rw [← Finset.mul_sum,
      sum_powersetCard_seven_five_subset_convert ρ μG hN hN3 hρcont u u']
  have aZ3 : (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ∑ T ∈ Finset.powersetCard 6 C,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 6))
      = ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 6) * ((colCount N - 6) * (kappa6chanC6Excess ρ μG u u'
          + kappa6chanThetaExcess ρ μG u u'
          + (e1 ρ μG) ^ 2 * (((colCount N - 4) * (colCount N - 5) / 2)
            * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u'
                  - (e1 ρ μG) ^ 4)))) := by
    rw [← Finset.mul_sum,
      sum_powersetCard_seven_six_subset_convert ρ μG hN hN3 hρcont u u']
  have aZ4 : (∑ C ∈ Finset.univ.powersetCard 7, ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (heptaReMoment ρ μG C u u' - (e1 ρ μG) ^ 7))
      = ((5040 : ℝ) * ((d : ℝ)⁻¹) ^ 7) * (kappa7chanTheta133Excess ρ μG u u'
        + e1 ρ μG * ((colCount N - 6) * ∑ D ∈ Finset.univ.powersetCard 6,
            (hexaReMoment ρ μG D u u' - (e1 ρ μG) ^ 6))
        - e1 ρ μG * bookHexaEraseSum ρ μG u u'
        - 2 * (e1 ρ μG) ^ 3
          * (((colCount N - 4) * (colCount N - 5)
          * (colCount N - 6) / 6) * ∑ T ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            - book4SubsetSum ρ μG u u')) := by
    rw [← Finset.mul_sum,
      sum_powersetCard_seven_heptaExcess_convert ρ μG hN hN3 hρcont u u']
  rw [← step, aZ1, aZ2, aZ3, aZ4,
    sum_powersetCard_six_hexaExcess_convert ρ μG hN hN3 hρcont u u']
  ring
set_option maxHeartbeats 1600000 in
/-- **The total decomposition at order 7**
(B7-2b-iv, the headline): `κ₇^dep` is the
order-6 dependent part dressed by the same
factor `4 + (colCount N − 4) B` as at orders 5
and 6, plus order-5 and order-4 dressings read
off the landed fiber accounting, plus the seven
B7-2a channel excesses at `d⁻⁷` with weights
`-1/24` (`(4,1,1,1)`), `-1/12` (`(3,2,1,1)`,
split into its adjacent and opposite parts),
`-1/48` (`(2,2,2,1)`), `-1/2` (`(2,1,1,1,1,1)`
C6), `-1/2` (`(2,1,1,1,1,1)` theta), `-1`
(theta133 book), plus the forced residuals:
the order-6 C6/theta channels reappear at
`2 e₁ d⁻⁷` (the hepta conversion's hexa pool
carries one more power of the dressing than
the order-6 dressing absorbs), the theta
4-subset sums `S4theta`, `S4thetaD` at
`e₁ (μ₂ − 2 e₁²) d⁻⁷` and `(e₁²/2) d⁻⁷`, and
the book residuals `bookHexaEraseSum` at
`e₁ d⁻⁷` and `book4SubsetSum` at
`-2 e₁³ d⁻⁷`. Every coefficient is read off
the landed accounting (B7-2b-i/ii/iii and the
B7-2a excesses); nothing is fitted. The
statement sits in B7-1's exact variable
context, so the B7-2b-v packaging as
`kappa7dep_eq` is a rename. FENCE: NO CLAIM;
this is a finite counting identity inside the
corpus — parts closed 0, dials 0/4. -/
theorem kappa7dep_total_decomposition (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa7dep ρ μG u u'
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa6dep ρ μG u u'
        + (- (1 / 2) * ((1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ) ^ 2
            - 7 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ)
            + 12 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + 6 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ)
            - 24 * (1 - e1 ρ μG / (d : ℝ))
            + (colCount N : ℝ)
            - (colCount N - 4) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 12))
          * kappa5dep ρ μG u u'
        + ((1 / 6) * ((1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ) ^ 3
            - 9 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ) ^ 2
            + 26 * (1 - e1 ρ μG / (d : ℝ)) ^ 3 * (colCount N : ℝ)
            - 24 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 6 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ) ^ 2
            - 42 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 * (colCount N : ℝ)
            + 72 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            - 3 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) ^ 2 * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 3 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) ^ 2
            + 21 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 6 * (1 - e1 ρ μG / (d : ℝ)) * (colCount N : ℝ)
            - 36 * (1 - e1 ρ μG / (d : ℝ)) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            - 72 * (1 - e1 ρ μG / (d : ℝ))
            - (colCount N : ℝ) * (realMoment ρ μG 3 / (d : ℝ) ^ 3)
            - 9 * (colCount N : ℝ) * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 10 * (colCount N : ℝ)
            + 4 * (realMoment ρ μG 3 / (d : ℝ) ^ 3)
            + 36 * (realMoment ρ μG 2 / (d : ℝ) ^ 2)
            + 24))
          * kappa4dep ρ μG u u'
        + ((d : ℝ)⁻¹) ^ 7
          * (- (1 / 24) * kappa7chan4111Excess ρ μG u u'
            - (1 / 12) * (kappa7chan3211AdjExcess ρ μG u u'
              + kappa7chan3211OppExcess ρ μG u u')
            - (1 / 48) * kappa7chan2221Excess ρ μG u u'
            - (1 / 2) * kappa7chan211111C6Excess ρ μG u u'
            - (1 / 2)
              * kappa7chan211111ThetaExcess ρ μG u u'
            - kappa7chanTheta133Excess ρ μG u u'
            + 2 * e1 ρ μG
              * (kappa6chanC6Excess ρ μG u u'
                + kappa6chanThetaExcess ρ μG u u')
            + e1 ρ μG * (realMoment ρ μG 2
                - 2 * (e1 ρ μG) ^ 2)
              * ∑ C ∈ thetaSupports,
              ∑ T ∈ Finset.powersetCard 4 C,
                (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
            + ((e1 ρ μG) ^ 2 / 2)
              * theta4SubsetDoubledSum ρ μG u u'
            + e1 ρ μG * bookHexaEraseSum ρ μG u u'
            - 2 * (e1 ρ μG) ^ 3
              * book4SubsetSum ρ μG u u') := by
  classical
  have hβ : betaCoeff7 ρ μG u u'
      = (∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 7
          ∂(Measure.pi fun _ : LayerSite N => μG)) / 5040 := by
    have hcong : (∫ α : LayerSite N → G,
          (layerDensSum ρ α u u') ^ 7 / 5040
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          (5040 : ℝ)⁻¹ * (layerDensSum ρ α u u') ^ 7
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with α
      rw [div_eq_inv_mul]
    show betaCoeff7 ρ μG u u' = _
    unfold betaCoeff7
    rw [hcong, integral_const_mul, div_eq_inv_mul]
  rw [kappa7dep_def, hβ,
    betaCoeff7_total ρ μG hN hN3 hρcont u u',
    sum_exagg4_convert ρ μG hN hN3 hρcont u u',
    sum_exagg5_convert ρ μG hN hN3 hρcont u u',
    sum_w6rest_convert ρ μG hN hN3 hρcont u u',
    sum_w7rest_convert ρ μG hN hN3 hρcont u u',
    kappa6dep_eq ρ μG hN hN3 hρcont u u',
    kappa5dep_eq ρ μG hN hN3 hρcont u u',
    kappa4dep_eq ρ μG hN hN3 hρcont u u',
    sum_powersetCard_four_eq_primitive ρ μG hN hN3 hρcont u u',
    ← kappa7chan3211Adj_add_Opp_excess ρ μG u u']
  ring

#print axioms kappa7dep_total_decomposition

/-! **B7-2b-iv close.** The total decomposition
at order 7 is landed above as
`kappa7dep_total_decomposition`, in B7-1's
exact variable context (Even `N`, `3 ≤ N`,
continuity of `g ↦ repMatrix ρ g`), so the
B7-2b-v packaging as `kappa7dep_eq` is a thin
rename. Dressings as landed: order 6 by
`4 + (colCount N − 4) B` (the order-5/order-6
factor again — no new dressing shape at this
order); order 5 and order 4 by the displayed
polynomials in `B`, `colCount N`, `μ₂/d²`,
`μ₃/d³`. Surprises at full rank: the order-6
C6/theta channels reappear at `2 e₁ d⁻⁷`; the
theta 4-subset sum reappears at
`e₁ (μ₂ − 2 e₁²) d⁻⁷` beside its doubled
companion at `(e₁²/2) d⁻⁷`; the theta133 book
carries two named residuals
(`bookHexaEraseSum`, `book4SubsetSum`). The
evaluated ADJ/OPP counts (8 and 4 per
primitive quad) are absorbed in excess form
through `kappa7chan3211Adj_add_Opp_excess`.
FENCES: NO CLAIM; parts closed 0; dials 0/4;
the β line's continuum content is untouched
by this finite identity. -/

end Total7

#print axioms fiber_card_one7
#print axioms fiber_card_two7
#print axioms fiber_card_three7
#print axioms fiber_card_four7
#print axioms fiber_card_five7
#print axioms tripledPentaReMoment_factor_of_private
#print axioms doubledDoubledPentaReMoment_factor_of_private
#print axioms colReMomentPow_support_reduce
#print axioms card_five_erasure_settlement
#print axioms card_six_support_live_or_private
#print axioms doubledHexaReMoment_factor_of_private
#print axioms card_six_fiber_split
#print axioms card_six_family_split_settlement
#print axioms adjPartnerCount_eq_two
#print axioms oppPartnerCount_eq_one
#print axioms kappa7adjPairCount_eq
#print axioms kappa7oppPairCount_eq

end ThetLogos
