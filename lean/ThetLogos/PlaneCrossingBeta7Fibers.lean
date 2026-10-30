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
