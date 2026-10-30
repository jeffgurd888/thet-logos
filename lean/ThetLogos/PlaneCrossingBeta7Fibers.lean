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

#print axioms fiber_card_one7
#print axioms fiber_card_two7
#print axioms fiber_card_three7

end ThetLogos
