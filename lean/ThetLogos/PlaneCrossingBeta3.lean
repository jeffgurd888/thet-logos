/-
# ThetLogos.PlaneCrossingBeta3 — Brick SBP-2: the β³ expansion
of `layerKernel` 𝒜 at general (G, ρ)

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. β2 (`𝒜 ⪰ 0`) and
(H-PF) at general (G, ρ) remain **L+ / open**: this module is
an *expansion* theorem about 𝒜's β-dependence, and **no
positivity conclusion at any β > 0 follows from it** — the
module says so again at its headline. Even `N` is
load-bearing (the no-triangle combinatorics of §1 below is
false at odd `N = 3`, where the coordinate lines wrap into
3-cycles of columns); `N = 2` is fenced out with the corpus's
crossing theory (the collapse needs `3 ≤ N`).

## The question and the answer

β2-1b (`PlaneCrossingBeta2`) proved 𝒜's β¹ and β²
coefficients are (u, u′)-independent constants at general
(G, ρ): 𝒜's dependence is O(β³). The small-β scoping memo
(2026-10-26, §1) argued the collapse survives one more
order, for a lattice-combinatorial reason: a monomial in the
β³ coefficient resists the private-site stripping only if
three distinct columns form a *triangle* in the site
lattice, and at even N the lattice is bipartite — no
triangles. This module proves it:

- **Same column** (∫x_P³): the one-word moments to order 3,
  via LOC-1's `colDensMoment_closed`.
- **Two columns** (∫x_P²x_Q, P ≠ Q): complete factorization,
  LOC-1's `integral_colDens_pow_mul` — the pair is
  independent as random variables, at every degree.
- **Three distinct columns**: the one new integral. A
  private site for one of the three columns always exists
  at even N ≥ 4 (`exists_private_site_triple` — the
  no-triangle lemma, proved here by the coordinate-sum
  invariant: a column's two sites have coordinate sums
  differing by exactly ±1 in `ZMod N`, and a triangle would
  force ε₁ + ε₂ = ε₃ with εᵢ ∈ {1, −1}, i.e. `N ∣ 1` or
  `N ∣ 3`). Stripping that column (`integral_split_inner_pow`)
  and applying the two-column theory to the rest gives
  ∫r_P r_Q r_R = μ₁³ and ∫x_P x_Q x_R = (1 − e₁/d)³.

Consequently the β³ coefficient is the closed form
`C₃ = [M³ − 3M³(e₁/d) + 3M²(q₂/d²) + 3M²(M−1)(e₁²/d²)
− M(μ₃/d³) − 3M(M−1)(e₁q₂/d³) − M(M−1)(M−2)(e₁³/d³)]/6`
(M = 3N³ columns, μ₃ = ∫(Re χ)³), manifestly
(u, u′)-independent: **𝒜's (u, u′)-dependence is O(β⁴)**,
with the explicit tail bound of `layerKernel_tail_bound3`.
Where the β⁴ dependent part lives (spatial plaquette
4-cycles) and whether it has a sign at a given seat are
other bricks (SBP-1 computed the seat case); nothing here
is a sign claim at order 4 or any other order.

Conventions follow the corpus: ρ is a bare `MonoidHom` into
a unitary group, and the moment theory carries the explicit
hypothesis `hρcont : Continuous fun g => repMatrix ρ g`,
exactly as in `PlaneCrossingBeta2` and `PolymerActivity`.
-/

import ThetLogos.PlaneCrossingBeta2
import ThetLogos.PolymerActivity

namespace ThetLogos

open Finset MeasureTheory

section Combinatorics

variable {N : ℕ} [NeZero N]

/-- The coordinate sum of a layer site, in `ZMod N`: the
bipartite colouring invariant of the (even-N) site lattice,
before reduction mod 2 — a column's shift raises it by
exactly `1`, which already separates triangles at `N ≥ 4`. -/
def siteCoordSum (c : LayerSite N) : ZMod N :=
  ∑ μ : Fin 4, c.1 μ

/-- A layer shift raises the coordinate sum by exactly `1`:
the shift changes one coordinate by `+1` and leaves the
others. -/
theorem siteCoordSum_layerShift (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    siteCoordSum (layerShift ν hν c) = siteCoordSum c + 1 := by
  have h : ∀ μ : Fin 4, (layerShift ν hν c).1 μ
      = c.1 μ + (Pi.single ν (1 : ZMod N) : Fin 4 → ZMod N) μ := by
    intro μ
    rw [layerShift_coe, torusShift_apply_coord]
    exact add_comm _ _
  unfold siteCoordSum
  rw [Finset.sum_congr rfl (fun μ _ => h μ), Finset.sum_add_distrib]
  congr 1
  simp [Finset.sum_pi_single']

/-- The two sites of one column have coordinate sums
differing by exactly `±1` in `ZMod N`. -/
theorem siteCoordSum_sub_of_mem_colSites {P : LayerColumn N}
    {s t : LayerSite N} (hs : s ∈ colSites P) (ht : t ∈ colSites P)
    (hst : s ≠ t) :
    siteCoordSum t - siteCoordSum s = 1
      ∨ siteCoordSum t - siteCoordSum s = -1 := by
  rw [mem_colSites] at hs ht
  rcases hs with rfl | hs <;> rcases ht with rfl | ht
  · exact absurd rfl hst
  · left
    rw [ht, siteCoordSum_layerShift]
    exact add_sub_cancel_left _ _
  · right
    rw [hs, siteCoordSum_layerShift, sub_add_eq_sub_sub, sub_self,
      zero_sub]
  · exact absurd (hs.trans ht.symm) hst

/-- The cardinality of a column's site set is `2`. -/
theorem card_colSites (hN : Even N) (P : LayerColumn N) :
    (colSites P).card = 2 := by
  unfold colSites
  exact Finset.card_pair
    (fun h => layerShift_ne_self hN P.2.1 P.2.2 P.1 h.symm)

/-- **The no-triangle lemma (private site for a triple).**
For three pairwise distinct columns at even `N ≥ 4`, some
column has a site belonging to neither of the other two.
The obstruction case — every site shared — forces the
three site sets to be `{a,b}`, `{b,c}`, `{a,c}`; the
coordinate sums then satisfy `ε₁ + ε₂ = ε₃` with
`εᵢ ∈ {1, −1}` in `ZMod N`, forcing `(1 : ZMod N) = 0` or
`(3 : ZMod N) = 0`, i.e. `N ∣ 1` or `N ∣ 3` — excluded by
`3 ≤ N` with `N` even. This is the one new combinatorial
input of the β³ collapse: the bipartite lattice has no
triangles. At odd `N = 3` the statement is false
(coordinate lines wrap into 3-cycles). -/
theorem exists_private_site_triple (hN : Even N) (hN3 : 3 ≤ N)
    {P Q R : LayerColumn N} (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R) :
    (∃ s, s ∈ colSites P ∧ s ∉ colSites Q ∧ s ∉ colSites R)
      ∨ (∃ s, s ∈ colSites Q ∧ s ∉ colSites P ∧ s ∉ colSites R)
      ∨ (∃ s, s ∈ colSites R ∧ s ∉ colSites P ∧ s ∉ colSites Q) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hP, hQ, hR⟩ := hcon
  have hcardP := card_colSites hN P
  have hcardQ := card_colSites hN Q
  have hcardR := card_colSites hN R
  have hPQ' : colSites P ≠ colSites Q :=
    fun h => hPQ (colSites_eq_imp hN hN3 h)
  have hPR' : colSites P ≠ colSites R :=
    fun h => hPR (colSites_eq_imp hN hN3 h)
  have hQR' : colSites Q ≠ colSites R :=
    fun h => hQR (colSites_eq_imp hN hN3 h)
  -- a site of P outside Q
  obtain ⟨a, haP, haQ⟩ : ∃ a ∈ colSites P, a ∉ colSites Q := by
    by_contra h
    push_neg at h
    exact hPQ' (Finset.eq_of_subset_of_card_le
      (fun s hs => h s hs) (by omega))
  have haR : a ∈ colSites R := hP a haP haQ
  -- a site of P also in Q (else P's sites both avoid Q,
  -- forcing colSites P ⊆ colSites R)
  obtain ⟨b, hbP, hbQ⟩ : ∃ b ∈ colSites P, b ∈ colSites Q := by
    by_contra h
    push_neg at h
    have hsub : colSites P ⊆ colSites R :=
      fun s hs => hP s hs (h s hs)
    exact hPR' (Finset.eq_of_subset_of_card_le hsub (by omega))
  -- a site of Q outside P
  obtain ⟨c, hcQ, hcP⟩ : ∃ c ∈ colSites Q, c ∉ colSites P := by
    by_contra h
    push_neg at h
    exact hPQ' ((Finset.eq_of_subset_of_card_le
      (fun s hs => h s hs) (by omega)).symm)
  have hcR : c ∈ colSites R := hQ c hcQ hcP
  -- the three ±1 differences; ε₁ + ε₂ = ε₃ in ZMod N by
  -- telescoping, and each of the eight sign cases forces
  -- (1 : ZMod N) = 0 or (3 : ZMod N) = 0
  have hab : a ≠ b := fun h => haQ (h ▸ hbQ)
  have hbc : b ≠ c := fun h => hcP (h ▸ hbP)
  have hac : a ≠ c := fun h => haQ (h ▸ hcQ)
  have key : (siteCoordSum b - siteCoordSum a)
      + (siteCoordSum c - siteCoordSum b)
      = siteCoordSum c - siteCoordSum a := by
    rw [add_comm (siteCoordSum b - siteCoordSum a)
      (siteCoordSum c - siteCoordSum b)]
    exact sub_add_sub_cancel _ _ _
  have hN1 : ¬ ((1 : ZMod N) = 0) := by
    intro h1
    have hdiv : N ∣ 1 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
        rw [Nat.cast_one]; exact h1)
    have := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hN3' : ¬ ((3 : ZMod N) = 0) := by
    intro h3
    have hdiv : N ∣ 3 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 3).mp (by
        exact_mod_cast h3)
    have hle := Nat.le_of_dvd (by norm_num) hdiv
    have hNeq : N = 3 := le_antisymm hle hN3
    rw [hNeq] at hN
    exact (by decide : ¬ Even (3 : ℕ)) hN
  rcases siteCoordSum_sub_of_mem_colSites haP hbP hab
    with hε₁ | hε₁ <;>
  rcases siteCoordSum_sub_of_mem_colSites hbQ hcQ hbc
    with hε₂ | hε₂ <;>
  rcases siteCoordSum_sub_of_mem_colSites haR hcR hac
    with hε₃ | hε₃ <;>
  rw [hε₁, hε₂, hε₃] at key
  all_goals
    first
      | exact hN1 (by linear_combination key)
      | exact hN1 (by linear_combination -key)
      | exact hN3' (by linear_combination key)
      | exact hN3' (by linear_combination -key)

end Combinatorics

section TripleMoments

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- Triple products of column characters are integrable
(bounded by `d³` entrywise). -/
theorem integrable_colRe_triple_mul
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q R : LayerColumn N) :
    Integrable (fun α => colRe ρ u u' P α * colRe ρ u u' Q α
        * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
  Integrable.of_bound
    (((measurable_colRe ρ hρcont u u' P).mul
      (measurable_colRe ρ hρcont u u' Q)).mul
      (measurable_colRe ρ hρcont u u' R)).aestronglyMeasurable
    ((d : ℝ) * (d : ℝ) * (d : ℝ))
    (Filter.Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (abs_re_charFn_le ρ _) (abs_re_charFn_le ρ _)
          (abs_nonneg _) (Nat.cast_nonneg d))
        (abs_re_charFn_le ρ _) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d)))

/-- Triple products of column densities are integrable
(bounded by `2³` entrywise). -/
theorem integrable_colDensC_triple_mul
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q R : LayerColumn N) :
    Integrable (fun α => colDensC ρ u u' P α * colDensC ρ u u' Q α
        * colDensC ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound ?_ (8 : ℝ)
    (Filter.Eventually.of_forall fun α => ?_)
  · exact (((measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2).mul
      (measurable_colDens ρ hρcont u u' Q.1 Q.2.1 Q.2.2)).mul
      (measurable_colDens ρ hρcont u u' R.1 R.2.1 R.2.2)
      ).aestronglyMeasurable
  · have habs : ∀ X : LayerColumn N, |colDensC ρ u u' X α| ≤ 2 := by
      intro X
      have h0 : (0 : ℝ) ≤ colDensC ρ u u' X α :=
        colDens_nonneg ρ u u' X.1 X.2.1 X.2.2 α
      have h2 : colDensC ρ u u' X α ≤ 2 :=
        colDens_le_two ρ u u' X.1 X.2.1 X.2.2 α
      exact abs_le.mpr ⟨by linarith, h2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |colDensC ρ u u' P α| * |colDensC ρ u u' Q α|
          * |colDensC ρ u u' R α|
        ≤ 2 * 2 * 2 :=
          mul_le_mul
            (mul_le_mul (habs P) (habs Q) (abs_nonneg _)
              (by norm_num))
            (habs R) (abs_nonneg _) (by norm_num)
      _ = 8 := by norm_num

/-- **The directed triple moment.** If `s` is a site of `P`
but of neither `Q` nor `R`, the triple moment strips `P`
off: the private coordinate is a Haar translate inside
`P`'s word and absent from `Q`'s and `R`'s, so
`∫ r_P r_Q r_R = μ₁ · ∫ r_Q r_R = μ₁ · e₁²`. -/
theorem integral_colRe_triple_of_site (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q R : LayerColumn N)
    (s : LayerSite N) (hsP : s ∈ colSites P)
    (hsQ : s ∉ colSites Q) (hsR : s ∉ colSites R)
    (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG 1 * (e1 ρ μG) ^ 2 := by
  classical
  have hbQ : Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : Q.1 ∈ colSites Q := mem_colSites.mpr (Or.inl rfl)
    rw [h] at hmem
    exact hmem
  have hfQ : layerShift Q.2.1 Q.2.2 Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : layerShift Q.2.1 Q.2.2 Q.1 ∈ colSites Q :=
      mem_colSites.mpr (Or.inr rfl)
    rw [h] at hmem
    exact hmem
  have hbR : R.1 ≠ s := by
    intro h
    apply hsR
    have hmem : R.1 ∈ colSites R := mem_colSites.mpr (Or.inl rfl)
    rw [h] at hmem
    exact hmem
  have hfR : layerShift R.2.1 R.2.2 R.1 ≠ s := by
    intro h
    apply hsR
    have hmem : layerShift R.2.1 R.2.2 R.1 ∈ colSites R :=
      mem_colSites.mpr (Or.inr rfl)
    rw [h] at hmem
    exact hmem
  have hInt : Integrable
      (fun z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
        colRe ρ u u' P (splitRecomb s z)
          * colRe ρ u u' Q (splitRecomb s z)
          * colRe ρ u u' R (splitRecomb s z))
      ((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
        (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    refine Integrable.of_bound ?_ ((d : ℝ) * (d : ℝ) * (d : ℝ))
      (Filter.Eventually.of_forall fun z => ?_)
    · have hm : ∀ X : LayerColumn N, Measurable
          (fun z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
            colRe ρ u u' X (splitRecomb s z)) :=
        fun X => (measurable_colRe ρ hρcont u u' X).comp
          (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable
      exact ((hm P).mul (hm Q) |>.mul (hm R)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (abs_re_charFn_le ρ _) (abs_re_charFn_le ρ _)
          (abs_nonneg _) (Nat.cast_nonneg d))
        (abs_re_charFn_le ρ _) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
  have htrans : ∫ α : LayerSite N → G,
        colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G),
          colRe ρ u u' P (splitRecomb s z)
            * colRe ρ u u' Q (splitRecomb s z)
            * colRe ρ u u' R (splitRecomb s z)
          ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
            (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    have h := (measurePreserving_splitEquiv μG
      ({s} : Finset (LayerSite N))).integral_comp
      (splitEquiv ({s} : Finset (LayerSite N))).measurableEmbedding
      (fun z => colRe ρ u u' P (splitRecomb s z)
        * colRe ρ u u' Q (splitRecomb s z)
        * colRe ρ u u' R (splitRecomb s z))
    have hL : ∫ U : LayerSite N → G,
          (fun z => colRe ρ u u' P (splitRecomb s z)
            * colRe ρ u u' Q (splitRecomb s z)
            * colRe ρ u u' R (splitRecomb s z))
            (splitEquiv ({s} : Finset (LayerSite N)) U)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∫ U : LayerSite N → G, colRe ρ u u' P U
            * colRe ρ u u' Q U * colRe ρ u u' R U
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with U
      show colRe ρ u u' P (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))
          * colRe ρ u u' Q (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))
          * colRe ρ u u' R (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))
        = colRe ρ u u' P U * colRe ρ u u' Q U * colRe ρ u u' R U
      rw [splitRecomb_apply_split]
    rw [hL] at h
    exact h
  calc ∫ α : LayerSite N → G,
          colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G),
            colRe ρ u u' P (splitRecomb s z)
              * colRe ρ u u' Q (splitRecomb s z)
              * colRe ρ u u' R (splitRecomb s z)
            ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
              (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) :=
        htrans
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            ∫ v : ↥({s} : Finset (LayerSite N)) → G,
              colRe ρ u u' P (splitRecomb s (v, w))
                * colRe ρ u u' Q (splitRecomb s (v, w))
                * colRe ρ u u' R (splitRecomb s (v, w))
              ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) :=
        integral_prod_symm _ hInt
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            (realMoment ρ μG 1)
              * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                * colRe ρ u u' R (splitRecomb s (fun _ => 1, w)))
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) := by
        apply integral_congr_ae
        filter_upwards with w
        have hQc : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
            colRe ρ u u' Q (splitRecomb s (v, w))
              = colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)) := by
          intro v
          have h1 : splitRecomb s (v, w) Q.1
              = splitRecomb s (fun _ => 1, w) Q.1 :=
            (splitRecomb_snd s (v, w) ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w) ⟨Q.1,
                Finset.mem_compl.mpr (fun hmem =>
                  hbQ (Finset.mem_singleton.mp hmem))⟩).symm
          have h2 : splitRecomb s (v, w) (layerShift Q.2.1 Q.2.2 Q.1)
              = splitRecomb s (fun _ => 1, w)
                  (layerShift Q.2.1 Q.2.2 Q.1) :=
            (splitRecomb_snd s (v, w) ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w)
                ⟨layerShift Q.2.1 Q.2.2 Q.1,
                  Finset.mem_compl.mpr (fun hmem =>
                    hfQ (Finset.mem_singleton.mp hmem))⟩).symm
          exact congrArg (fun g => (charFn ρ g).re)
            (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1 h2)
        have hRc : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
            colRe ρ u u' R (splitRecomb s (v, w))
              = colRe ρ u u' R (splitRecomb s (fun _ => 1, w)) := by
          intro v
          have h1 : splitRecomb s (v, w) R.1
              = splitRecomb s (fun _ => 1, w) R.1 :=
            (splitRecomb_snd s (v, w) ⟨R.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbR (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w) ⟨R.1,
                Finset.mem_compl.mpr (fun hmem =>
                  hbR (Finset.mem_singleton.mp hmem))⟩).symm
          have h2 : splitRecomb s (v, w) (layerShift R.2.1 R.2.2 R.1)
              = splitRecomb s (fun _ => 1, w)
                  (layerShift R.2.1 R.2.2 R.1) :=
            (splitRecomb_snd s (v, w) ⟨layerShift R.2.1 R.2.2 R.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfR (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w)
                ⟨layerShift R.2.1 R.2.2 R.1,
                  Finset.mem_compl.mpr (fun hmem =>
                    hfR (Finset.mem_singleton.mp hmem))⟩).symm
          exact congrArg (fun g => (charFn ρ g).re)
            (colWord_eq_of_agree u u' R.1 R.2.1 R.2.2 h1 h2)
        calc ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                colRe ρ u u' P (splitRecomb s (v, w))
                  * colRe ρ u u' Q (splitRecomb s (v, w))
                  * colRe ρ u u' R (splitRecomb s (v, w))
                ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            = ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                  colRe ρ u u' P (splitRecomb s (v, w))
                    * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                      * colRe ρ u u' R (splitRecomb s (fun _ => 1, w)))
                  ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG) :=
              integral_congr_ae (Filter.Eventually.of_forall fun v => by
                show colRe ρ u u' P (splitRecomb s (v, w))
                    * colRe ρ u u' Q (splitRecomb s (v, w))
                    * colRe ρ u u' R (splitRecomb s (v, w))
                  = colRe ρ u u' P (splitRecomb s (v, w))
                    * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                      * colRe ρ u u' R (splitRecomb s (fun _ => 1, w)))
                rw [hQc v, hRc v]; ring)
          _ = (∫ v : ↥({s} : Finset (LayerSite N)) → G,
                    colRe ρ u u' P (splitRecomb s (v, w))
                    ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG))
                  * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                    * colRe ρ u u' R (splitRecomb s (fun _ => 1, w))) :=
              integral_mul_const _ _
          _ = (realMoment ρ μG 1)
                  * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                    * colRe ρ u u' R (splitRecomb s (fun _ => 1, w))) := by
              congr 1
              have h1 := integral_split_inner_pow ρ μG hN hρcont u u'
                P s hsP w 1
              simpa only [pow_one] using h1
    _ = realMoment ρ μG 1 * (e1 ρ μG) ^ 2 := by
        rw [integral_const_mul]
        congr 1
        have hrestr : ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
              (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                * colRe ρ u u' R (splitRecomb s (fun _ => 1, w)))
              ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)
            = ∫ α : LayerSite N → G, colRe ρ u u' Q α
                * colRe ρ u u' R α
                ∂(Measure.pi fun _ : LayerSite N => μG) := by
          rw [← integral_pi_restrict_real μG ({s}ᶜ : Finset (LayerSite N))
            (fun w => colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
              * colRe ρ u u' R (splitRecomb s (fun _ => 1, w)))]
          apply integral_congr_ae
          filter_upwards with U
          have h1Q : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) Q.1 = U Q.1 :=
            splitRecomb_snd s _ ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩
          have h2Q : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) (layerShift Q.2.1 Q.2.2 Q.1)
              = U (layerShift Q.2.1 Q.2.2 Q.1) :=
            splitRecomb_snd s _ ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩
          have h1R : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) R.1 = U R.1 :=
            splitRecomb_snd s _ ⟨R.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbR (Finset.mem_singleton.mp hmem))⟩
          have h2R : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) (layerShift R.2.1 R.2.2 R.1)
              = U (layerShift R.2.1 R.2.2 R.1) :=
            splitRecomb_snd s _ ⟨layerShift R.2.1 R.2.2 R.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfR (Finset.mem_singleton.mp hmem))⟩
          show colRe ρ u u' Q (splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1))
              * colRe ρ u u' R (splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1))
            = colRe ρ u u' Q U * colRe ρ u u' R U
          congr 1
          · exact congrArg (fun g => (charFn ρ g).re)
              (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1Q h2Q)
          · exact congrArg (fun g => (charFn ρ g).re)
              (colWord_eq_of_agree u u' R.1 R.2.1 R.2.2 h1R h2R)
        rw [hrestr]
        exact integral_cross ρ μG hN hN3 hρcont u u' hQR

/-- **The triple character moment at three distinct
columns:** `∫ r_P r_Q r_R = μ₁³`. The no-triangle lemma
supplies a private site for one of the three columns; the
directed strip and the two-column cross term finish. This
is the β³ case of the private-site collapse — the point
where the order-2 argument would have failed had a
triangle existed. -/
theorem integral_colRe_triple (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (realMoment ρ μG 1) ^ 3 := by
  obtain (⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩) :=
    exists_private_site_triple hN hN3 hPQ hPR hQR
  · have h := integral_colRe_triple_of_site ρ μG hN hN3 hρcont
      u u' P Q R s hs.1 hs.2.1 hs.2.2 hQR
    rw [h, realMoment_one]
    ring
  · have h := integral_colRe_triple_of_site ρ μG hN hN3 hρcont
      u u' Q P R s hs.1 hs.2.1 hs.2.2 hPR
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
        = colRe ρ u u' Q α * colRe ρ u u' P α * colRe ρ u u' R α
      ring)]
    rw [h, realMoment_one]
    ring
  · have h := integral_colRe_triple_of_site ρ μG hN hN3 hρcont
      u u' R P Q s hs.1 hs.2.1 hs.2.2 hPQ
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
        = colRe ρ u u' R α * colRe ρ u u' P α * colRe ρ u u' Q α
      ring)]
    rw [h, realMoment_one]
    ring

/-- **The triple density moment at three distinct columns:**
`∫ x_P x_Q x_R = (1 − e₁/d)³` — the three columns are
independent at the density level for this monomial, by
binomial expansion into character moments: singles `e₁`,
pairs `e₁²` (the P₀-collapse), and the triple `e₁³`
(`integral_colRe_triple`). -/
theorem integral_colDens_triple (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G, colDensC ρ u u' P α
          * colDensC ρ u u' Q α * colDensC ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hexp : ∀ α : LayerSite N → G,
      colDensC ρ u u' P α * colDensC ρ u u' Q α
          * colDensC ρ u u' R α
        = 1 + c * (colRe ρ u u' P α + colRe ρ u u' Q α
            + colRe ρ u u' R α)
          + c ^ 2 * (colRe ρ u u' P α * colRe ρ u u' Q α
            + colRe ρ u u' P α * colRe ρ u u' R α
            + colRe ρ u u' Q α * colRe ρ u u' R α)
          + c ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
            * colRe ρ u u' R α) := by
    intro α
    rw [colDensC_eq_one_add ρ u u' P α,
      colDensC_eq_one_add ρ u u' Q α,
      colDensC_eq_one_add ρ u u' R α]
    ring
  have hIr : ∀ X : LayerColumn N,
      Integrable (fun α => colRe ρ u u' X α)
        (Measure.pi fun _ : LayerSite N => μG) :=
    fun X => integrable_colRe ρ μG hρcont u u' X
  have hIrr : ∀ X Y : LayerColumn N,
      Integrable (fun α => colRe ρ u u' X α * colRe ρ u u' Y α)
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro X Y
    have h := integrable_colRe_pow_mul ρ μG hρcont u u' X Y 1 1
    simpa [pow_one] using h
  have hS1 : Integrable (fun α => colRe ρ u u' P α
        + colRe ρ u u' Q α + colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    ((hIr P).add (hIr Q)).add (hIr R)
  have hS2 : Integrable (fun α => colRe ρ u u' P α
        * colRe ρ u u' Q α + colRe ρ u u' P α * colRe ρ u u' R α
        + colRe ρ u u' Q α * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    ((hIrr P Q).add (hIrr P R)).add (hIrr Q R)
  have hT1 : Integrable (fun α => (1 : ℝ)
        + c * (colRe ρ u u' P α + colRe ρ u u' Q α
          + colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_const (1 : ℝ)).add (hS1.const_mul c)
  have hT2 : Integrable (fun α => ((1 : ℝ)
        + c * (colRe ρ u u' P α + colRe ρ u u' Q α
          + colRe ρ u u' R α))
        + c ^ 2 * (colRe ρ u u' P α * colRe ρ u u' Q α
          + colRe ρ u u' P α * colRe ρ u u' R α
          + colRe ρ u u' Q α * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hT1.add (hS2.const_mul (c ^ 2))
  have hT3 : Integrable (fun α => c ^ 3
        * (colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_triple_mul ρ μG hρcont u u' P Q R).const_mul _
  have hv1 : ∀ X : LayerColumn N,
      ∫ α, colRe ρ u u' X α
          ∂(Measure.pi fun _ : LayerSite N => μG) = e1 ρ μG :=
    fun X => integral_colRe ρ μG hN hρcont u u' X
  have hv2 : ∀ {X Y : LayerColumn N}, X ≠ Y →
      ∫ α, colRe ρ u u' X α * colRe ρ u u' Y α
          ∂(Measure.pi fun _ : LayerSite N => μG) = (e1 ρ μG) ^ 2 :=
    fun {X Y} hXY => integral_cross ρ μG hN hN3 hρcont u u' hXY
  have hv3 : ∫ α, colRe ρ u u' P α * colRe ρ u u' Q α
        * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG) = (e1 ρ μG) ^ 3 := by
    have h := integral_colRe_triple ρ μG hN hN3 hρcont u u'
      hPQ hPR hQR
    rwa [realMoment_one] at h
  have hS1v : ∫ α, (colRe ρ u u' P α + colRe ρ u u' Q α
        + colRe ρ u u' R α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = e1 ρ μG + e1 ρ μG + e1 ρ μG := by
    have e1 := integral_add ((hIr P).add (hIr Q)) (hIr R)
    simp only [Pi.add_apply] at e1
    rw [integral_add (hIr P) (hIr Q), hv1 P, hv1 Q, hv1 R] at e1
    exact e1
  have hS2v : ∫ α, (colRe ρ u u' P α * colRe ρ u u' Q α
        + colRe ρ u u' P α * colRe ρ u u' R α
        + colRe ρ u u' Q α * colRe ρ u u' R α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ 2 + (e1 ρ μG) ^ 2 + (e1 ρ μG) ^ 2 := by
    have e2 := integral_add ((hIrr P Q).add (hIrr P R)) (hIrr Q R)
    simp only [Pi.add_apply] at e2
    rw [integral_add (hIrr P Q) (hIrr P R), hv2 hPQ, hv2 hPR,
      hv2 hQR] at e2
    exact e2
  have hsum : ∫ α : LayerSite N → G,
        (1 + c * (colRe ρ u u' P α + colRe ρ u u' Q α
            + colRe ρ u u' R α)
          + c ^ 2 * (colRe ρ u u' P α * colRe ρ u u' Q α
            + colRe ρ u u' P α * colRe ρ u u' R α
            + colRe ρ u u' Q α * colRe ρ u u' R α)
          + c ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
            * colRe ρ u u' R α))
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 + c * (3 * e1 ρ μG) + c ^ 2 * (3 * (e1 ρ μG) ^ 2)
        + c ^ 3 * (e1 ρ μG) ^ 3 := by
    rw [integral_add hT2 hT3, integral_add hT1 (hS2.const_mul _),
      integral_add (integrable_const (1 : ℝ)) (hS1.const_mul c),
      integral_const, integral_const_mul, integral_const_mul,
      integral_const_mul, hS1v, hS2v, hv3, probReal_univ,
      one_smul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hsum]
  have hfin : (1 : ℝ) - e1 ρ μG / (d : ℝ) = 1 + c * e1 ρ μG := by
    rw [hc, div_eq_inv_mul]
    ring
  rw [hfin]
  ring

end TripleMoments

section ClosedForm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The third β-coefficient of `𝒜`: `∫ layerDensSum³ / 6`
(so `𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + O(β⁴)`). -/
noncomputable def betaCoeff3 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 3 / 6
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- Degree 3, self-paired: `∫ dens_P³
= 1 − 3e₁/d + 3q₂/d² − μ₃/d³` (LOC-1's
`colDensMoment_closed` at `j = 3`, evaluated). -/
theorem colDensMoment_three (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    colDensMoment ρ μG u u' P 3
      = 1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
        - realMoment ρ μG 3 / (d : ℝ) ^ 3 := by
  rw [colDensMoment_closed ρ μG hN hρcont u u' P 3]
  norm_num [Finset.sum_range_succ, realMoment_zero, realMoment_one,
    realMoment_two, div_eq_inv_mul, inv_pow]
  ring

/-- The two-equal pattern value, squared column first:
`∫ x_P² x_Q = (∫x²)(∫x)` at distinct columns (LOC-1's
`integral_colDens_pow_mul` at degrees `(2, 1)`). -/
theorem integral_colDens_sq_mul (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G, colDensC ρ u u' P α
          * colDensC ρ u u' P α * colDensC ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
        * (1 - e1 ρ μG / (d : ℝ)) := by
  have h := integral_colDens_pow_mul ρ μG hN hN3 hρcont u u'
    hPQ 2 1
  rw [colDensMoment_two ρ μG hN hρcont,
    colDensMoment_one ρ μG hN hρcont] at h
  rwa [integral_congr_ae (Filter.Eventually.of_forall fun α => by
    show colDensC ρ u u' P α * colDensC ρ u u' P α
        * colDensC ρ u u' Q α
      = (colDensC ρ u u' P α) ^ 2 * (colDensC ρ u u' Q α) ^ 1
    ring)]

/-- The pure-algebra identity behind the closed form:
assembly values in, `C₃` out. Field identity in
`(M, e, q, t, δ)`; at `δ = 0` both sides reduce to `M³/6`
(all moments vanish there — that case is discharged by the
caller rewriting the moments, here it is the formal
`δ = 0` shadow). -/
theorem betaCoeff3_algebra (M e q t δ : ℝ) :
    (M * (1 - 3 * e / δ + 3 * q / δ ^ 2 - t / δ ^ 3)
      + 3 * M * (M - 1)
        * ((1 - 2 * e / δ + q / δ ^ 2) * (1 - e / δ))
      + M * (M - 1) * (M - 2) * (1 - e / δ) ^ 3) / 6
    = (M ^ 3 - 3 * M ^ 3 * (e / δ)
      + 3 * M ^ 2 * (q / δ ^ 2)
      + 3 * M ^ 2 * (M - 1) * (e ^ 2 / δ ^ 2)
      - M * (t / δ ^ 3)
      - 3 * M * (M - 1) * (e * q / δ ^ 3)
      - M * (M - 1) * (M - 2) * (e ^ 3 / δ ^ 3)) / 6 := by
  by_cases hδ : δ = 0
  · rw [hδ]
    norm_num
    ring
  · field_simp
    ring

/-- **(S7) The third coefficient in closed form.** With
`M = colCount N` columns: the diagonal triples contribute
the `μ₃` form, the `3M(M−1)` two-equal triples the
`(∫x²)(∫x)` form, the `M(M−1)(M−2)` distinct triples the
`(1 − e₁/d)³` form. In particular `betaCoeff3` does not
depend on `(u, u')` at all. -/
theorem betaCoeff3_closed (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    betaCoeff3 ρ μG u u'
      = (colCount N ^ 3 - 3 * colCount N ^ 3 * (e1 ρ μG / (d : ℝ))
        + 3 * colCount N ^ 2 * (q2 ρ μG / (d : ℝ) ^ 2)
        + 3 * colCount N ^ 2 * (colCount N - 1)
          * ((e1 ρ μG) ^ 2 / (d : ℝ) ^ 2)
        - colCount N * (realMoment ρ μG 3 / (d : ℝ) ^ 3)
        - 3 * colCount N * (colCount N - 1)
          * (e1 ρ μG * q2 ρ μG / (d : ℝ) ^ 3)
        - colCount N * (colCount N - 1) * (colCount N - 2)
          * ((e1 ρ μG) ^ 3 / (d : ℝ) ^ 3)) / 6 := by
  classical
  -- two distinct columns exist (for the `(M − 2)` casts)
  have h2card : 2 ≤ Fintype.card (LayerColumn N) := by
    have hne : (⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩ :
          LayerColumn N)
        ≠ ⟨⟨fun _ => 0, by simp⟩, ⟨2, by decide⟩⟩ := by
      intro h
      have h2 := congrArg (fun P : LayerColumn N => (P.2 : Fin 4)) h
      simp only [] at h2
      exact (by decide : (1 : Fin 4) ≠ 2) h2
    have hlt := Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
    exact hlt
  have hcast : ∀ k : ℕ, k ≤ Fintype.card (LayerColumn N) →
      ((Fintype.card (LayerColumn N) - k : ℕ) : ℝ)
        = colCount N - (k : ℝ) := by
    intro k hk
    rw [Nat.cast_sub hk]
    rfl
  have hcc2 : (((Fintype.card (LayerColumn N) - 1) - 1 : ℕ) : ℝ)
      = colCount N - 2 := by
    have hsub : (Fintype.card (LayerColumn N) - 1) - 1
        = Fintype.card (LayerColumn N) - 2 := by omega
    rw [hsub, hcast 2 h2card]
    push_cast
    ring
  -- the three pattern values, as named equations
  have hVself : ∀ P : LayerColumn N,
      ∫ α : LayerSite N → G, colDensC ρ u u' P α
            * colDensC ρ u u' P α * colDensC ρ u u' P α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = 1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
          - realMoment ρ μG 3 / (d : ℝ) ^ 3 := by
    intro P
    rw [← colDensMoment_three ρ μG hN hρcont u u' P]
    unfold colDensMoment
    exact integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colDensC ρ u u' P α * colDensC ρ u u' P α
          * colDensC ρ u u' P α = (colDensC ρ u u' P α) ^ 3
      rw [pow_three]; ring)
  have hVsq : ∀ {X Y : LayerColumn N}, X ≠ Y →
      ∫ α : LayerSite N → G, colDensC ρ u u' X α
            * colDensC ρ u u' X α * colDensC ρ u u' Y α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
          * (1 - e1 ρ μG / (d : ℝ)) :=
    fun {X Y} hXY => integral_colDens_sq_mul ρ μG hN hN3 hρcont
      u u' hXY
  have hVmid : ∀ {X Y : LayerColumn N}, X ≠ Y →
      ∫ α : LayerSite N → G, colDensC ρ u u' X α
            * colDensC ρ u u' Y α * colDensC ρ u u' X α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
          * (1 - e1 ρ μG / (d : ℝ)) := by
    intro X Y hXY
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colDensC ρ u u' X α * colDensC ρ u u' Y α
          * colDensC ρ u u' X α
        = colDensC ρ u u' X α * colDensC ρ u u' X α
          * colDensC ρ u u' Y α
      ring)]
    exact hVsq hXY
  have hVlast : ∀ {X Y : LayerColumn N}, X ≠ Y →
      ∫ α : LayerSite N → G, colDensC ρ u u' Y α
            * colDensC ρ u u' X α * colDensC ρ u u' X α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
          * (1 - e1 ρ μG / (d : ℝ)) := by
    intro X Y hXY
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colDensC ρ u u' Y α * colDensC ρ u u' X α
          * colDensC ρ u u' X α
        = colDensC ρ u u' X α * colDensC ρ u u' X α
          * colDensC ρ u u' Y α
      ring)]
    exact hVsq hXY
  have hVdist : ∀ {P Q R : LayerColumn N}, P ≠ Q → P ≠ R →
      Q ≠ R →
      ∫ α : LayerSite N → G, colDensC ρ u u' P α
            * colDensC ρ u u' Q α * colDensC ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (1 - e1 ρ μG / (d : ℝ)) ^ 3 :=
    fun {P Q R} hPQ hPR hQR => integral_colDens_triple ρ μG hN
      hN3 hρcont u u' hPQ hPR hQR
  -- inner sums over the third index
  have hInnerEq : ∀ P : LayerColumn N,
      (∑ Q : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' P α
              * colDensC ρ u u' Q α * colDensC ρ u u' P α
            ∂(Measure.pi fun _ : LayerSite N => μG))
        = (1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
            - realMoment ρ μG 3 / (d : ℝ) ^ 3)
          + (colCount N - 1)
            * ((1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
              * (1 - e1 ρ μG / (d : ℝ))) := by
    intro P
    rw [← Finset.add_sum_erase Finset.univ
      (fun Q => ∫ α : LayerSite N → G, colDensC ρ u u' P α
        * colDensC ρ u u' Q α * colDensC ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG)) (Finset.mem_univ P)]
    congr 1
    · exact hVself P
    · rw [Finset.sum_congr rfl
        (g := fun _ : LayerColumn N =>
          (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
            * (1 - e1 ρ μG / (d : ℝ)))
        (fun Q hQ => hVmid (X := P) (Y := Q)
          (Ne.symm (Finset.ne_of_mem_erase hQ)))]
      rw [Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_univ P), Finset.card_univ, nsmul_eq_mul,
        hcast 1 (by omega)]
      push_cast
      ring
  have hInnerNe : ∀ (P R : LayerColumn N), R ≠ P →
      (∑ Q : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' P α
              * colDensC ρ u u' Q α * colDensC ρ u u' R α
            ∂(Measure.pi fun _ : LayerSite N => μG))
        = 2 * ((1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
            * (1 - e1 ρ μG / (d : ℝ)))
          + (colCount N - 2) * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    intro P R hRP
    rw [← Finset.add_sum_erase Finset.univ
      (fun Q => ∫ α : LayerSite N → G, colDensC ρ u u' P α
        * colDensC ρ u u' Q α * colDensC ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)) (Finset.mem_univ P),
      ← Finset.add_sum_erase (Finset.univ.erase P)
      (fun Q => ∫ α : LayerSite N → G, colDensC ρ u u' P α
        * colDensC ρ u u' Q α * colDensC ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG))
      (Finset.mem_erase.mpr ⟨hRP, Finset.mem_univ R⟩),
      hVsq (Ne.symm hRP), hVlast hRP,
      Finset.sum_congr rfl
        (g := fun _ : LayerColumn N => (1 - e1 ρ μG / (d : ℝ)) ^ 3)
        (fun Q hQ => hVdist (Ne.symm
            (Finset.mem_erase.mp (Finset.mem_erase.mp hQ).2).1)
          (Ne.symm hRP) (Finset.mem_erase.mp hQ).1),
      Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hRP, Finset.mem_univ R⟩),
      Finset.card_erase_of_mem (Finset.mem_univ P), Finset.card_univ,
      nsmul_eq_mul, hcc2]
    ring
  -- pointwise cube as a triple sum, in (P, R, Q) nesting
  have hpt : ∀ α : LayerSite N → G,
      (layerDensSum ρ α u u') ^ 3
        = ∑ P : LayerColumn N, ∑ R : LayerColumn N,
            ∑ Q : LayerColumn N,
              colDensC ρ u u' P α * colDensC ρ u u' Q α
                * colDensC ρ u u' R α := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u']
    calc (∑ P : LayerColumn N, colDensC ρ u u' P α) ^ 3
        = ((∑ P : LayerColumn N, colDensC ρ u u' P α)
            * (∑ P : LayerColumn N, colDensC ρ u u' P α))
          * (∑ P : LayerColumn N, colDensC ρ u u' P α) := by
          rw [pow_three, mul_assoc]
      _ = (∑ P : LayerColumn N, ∑ Q : LayerColumn N,
            colDensC ρ u u' P α * colDensC ρ u u' Q α)
          * (∑ R : LayerColumn N, colDensC ρ u u' R α) := by
          rw [Finset.sum_mul_sum]
      _ = ∑ P : LayerColumn N, ∑ R : LayerColumn N,
            (∑ Q : LayerColumn N, colDensC ρ u u' P α
              * colDensC ρ u u' Q α) * colDensC ρ u u' R α := by
          rw [Finset.sum_mul_sum]
      _ = ∑ P : LayerColumn N, ∑ R : LayerColumn N,
            ∑ Q : LayerColumn N,
              colDensC ρ u u' P α * colDensC ρ u u' Q α
                * colDensC ρ u u' R α := by
          refine Finset.sum_congr rfl fun P _ =>
            Finset.sum_congr rfl fun R _ => ?_
          rw [Finset.sum_mul]
  have hdiv : (∫ α, (layerDensSum ρ α u u') ^ 3 / 6
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = (∫ α, (layerDensSum ρ α u u') ^ 3
          ∂(Measure.pi fun _ : LayerSite N => μG)) / 6 := by
    have h1 : (∫ α, (layerDensSum ρ α u u') ^ 3 / 6
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α, (6 : ℝ)⁻¹ * (layerDensSum ρ α u u') ^ 3
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by
        ring)
    rw [h1, integral_const_mul]
    ring
  have hIntMul : ∀ P Q R : LayerColumn N,
      Integrable (fun α => colDensC ρ u u' P α
          * colDensC ρ u u' Q α * colDensC ρ u u' R α)
        (Measure.pi fun _ : LayerSite N => μG) :=
    fun P Q R => integrable_colDensC_triple_mul ρ μG hρcont
      u u' P Q R
  unfold betaCoeff3
  rw [hdiv, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum Finset.univ (fun P _ =>
      integrable_finsetSum Finset.univ (fun R _ =>
        integrable_finsetSum Finset.univ (fun Q _ =>
          hIntMul P Q R))),
    Finset.sum_congr rfl (fun P _ =>
      integral_finsetSum Finset.univ (fun R _ =>
        integrable_finsetSum Finset.univ (fun Q _ =>
          hIntMul P Q R))),
    Finset.sum_congr rfl (fun P _ =>
      Finset.sum_congr rfl (fun R _ =>
        integral_finsetSum Finset.univ (fun Q _ =>
          hIntMul P Q R)))]
  -- the assembly: split the middle sum at `R = P`
  have hsplit : ∀ P : LayerColumn N,
      (∑ R : LayerColumn N, ∑ Q : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' P α
              * colDensC ρ u u' Q α * colDensC ρ u u' R α
            ∂(Measure.pi fun _ : LayerSite N => μG))
        = ((1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
              - realMoment ρ μG 3 / (d : ℝ) ^ 3)
            + (colCount N - 1)
              * ((1 - 2 * e1 ρ μG / (d : ℝ)
                  + q2 ρ μG / (d : ℝ) ^ 2) * (1 - e1 ρ μG / (d : ℝ))))
          + ∑ R ∈ Finset.univ.erase P,
            (2 * ((1 - 2 * e1 ρ μG / (d : ℝ)
                  + q2 ρ μG / (d : ℝ) ^ 2) * (1 - e1 ρ μG / (d : ℝ)))
              + (colCount N - 2) * (1 - e1 ρ μG / (d : ℝ)) ^ 3) := by
    intro P
    rw [← Finset.add_sum_erase Finset.univ
      (fun R => ∑ Q : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' P α
              * colDensC ρ u u' Q α * colDensC ρ u u' R α
            ∂(Measure.pi fun _ : LayerSite N => μG))
      (Finset.mem_univ P)]
    congr 1
    · exact hInnerEq P
    · exact Finset.sum_congr rfl fun R hR =>
        hInnerNe P R (Finset.ne_of_mem_erase hR)
  rw [Finset.sum_congr rfl (fun P _ => hsplit P),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul,
    show (Fintype.card (LayerColumn N) : ℝ) = colCount N from rfl,
    Finset.sum_congr rfl (g := fun P : LayerColumn N =>
      (colCount N - 1)
        * (2 * ((1 - 2 * e1 ρ μG / (d : ℝ)
              + q2 ρ μG / (d : ℝ) ^ 2) * (1 - e1 ρ μG / (d : ℝ)))
          + (colCount N - 2) * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
      (fun P _ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem
          (Finset.mem_univ P), Finset.card_univ, nsmul_eq_mul,
          hcast 1 (by omega)]
        push_cast
        ring),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    show (Fintype.card (LayerColumn N) : ℝ) = colCount N from rfl]
  have hdist : colCount N
        * ((1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
              - realMoment ρ μG 3 / (d : ℝ) ^ 3)
            + (colCount N - 1)
              * ((1 - 2 * e1 ρ μG / (d : ℝ)
                  + q2 ρ μG / (d : ℝ) ^ 2) * (1 - e1 ρ μG / (d : ℝ))))
      + colCount N
        * ((colCount N - 1)
          * (2 * ((1 - 2 * e1 ρ μG / (d : ℝ)
                + q2 ρ μG / (d : ℝ) ^ 2) * (1 - e1 ρ μG / (d : ℝ)))
            + (colCount N - 2) * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
      = (colCount N
          * (1 - 3 * e1 ρ μG / (d : ℝ) + 3 * q2 ρ μG / (d : ℝ) ^ 2
            - realMoment ρ μG 3 / (d : ℝ) ^ 3)
        + 3 * colCount N * (colCount N - 1)
          * ((1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
            * (1 - e1 ρ μG / (d : ℝ)))
        + colCount N * (colCount N - 1) * (colCount N - 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3) := by
    ring
  rw [hdist]
  exact betaCoeff3_algebra (colCount N) (e1 ρ μG) (q2 ρ μG)
    (realMoment ρ μG 3) (d : ℝ)

end ClosedForm

section Expansion3

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **(S8) The expansion, real form, one order further.**
For every real `β`, the stratum average of the layer
exponential is `1 − β·C₁ + β²·C₂ − β³·C₃ + R₄(β)` with
`C₁, C₂, C₃` the closed coefficients and `R₄(β)` the
displayed tail series. FENCE: this is an identity of Taylor
coefficients. It implies NO positivity of `𝒜` at any
`β > 0`; `β2` and (H-PF) remain open. -/
theorem layerKernel_real_expansion3 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        - β ^ 3 * betaCoeff3 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
            / ((Nat.factorial (k + 4) : ℝ))
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hexp : ∀ α : LayerSite N → G,
      Real.exp (-(β * layerDensSum ρ α u u'))
        = ∑' n : ℕ, (-β * layerDensSum ρ α u u') ^ n
            / ((Nat.factorial n : ℝ)) := by
    intro α
    have h1 : Real.exp (-(β * layerDensSum ρ α u u'))
        = NormedSpace.exp (-(β * layerDensSum ρ α u u')) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
    apply tsum_congr
    intro n
    rw [neg_mul, smul_eq_mul, div_eq_inv_mul]
  have hSumm : Summable fun n => ∫ α,
        (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_norm_term_int ρ μG hN hρcont β u u').of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have ht0 : (∫ α, (-β * layerDensSum ρ α u u') ^ 0
        / ((Nat.factorial 0 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)) = 1 := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 0 / ((Nat.factorial 0 : ℝ))
          = 1 :=
      fun α => by norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const, probReal_univ, one_smul]
  have ht1 : (∫ α, (-β * layerDensSum ρ α u u') ^ 1
        / ((Nat.factorial 1 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β * betaCoeff1 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 1 / ((Nat.factorial 1 : ℝ))
          = -β * layerDensSum ρ α u u' :=
      fun α => by
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht2 : (∫ α, (-β * layerDensSum ρ α u u') ^ 2
        / ((Nat.factorial 2 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 2 * betaCoeff2 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 2 / ((Nat.factorial 2 : ℝ))
          = β ^ 2 * ((layerDensSum ρ α u u') ^ 2 / 2) := by
      intro α
      have h2 : ((Nat.factorial 2 : ℝ)) = 2 := by
        norm_num [Nat.factorial]
      rw [h2]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht3 : (∫ α, (-β * layerDensSum ρ α u u') ^ 3
        / ((Nat.factorial 3 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β ^ 3 * betaCoeff3 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 3 / ((Nat.factorial 3 : ℝ))
          = -β ^ 3 * ((layerDensSum ρ α u u') ^ 3 / 6) := by
      intro α
      have h3 : ((Nat.factorial 3 : ℝ)) = 6 := by
        norm_num [Nat.factorial]
      rw [h3]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 4,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, ht0, ht1, ht2, ht3]
  ring

/-- **(S8) The expansion of `𝒜` itself, one order
further** (the ℂ-valued layer kernel is the cast of the
real expansion). Same fence: no positivity conclusion. -/
theorem layerKernel_expansion3 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
          - β ^ 3 * betaCoeff3 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
  have hreal : (∫ α, Real.exp (-(layerAction ρ β α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
    integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show Real.exp (-(layerAction ρ β α u u'))
        = Real.exp (-(β * layerDensSum ρ α u u'))
      rw [layerAction_eq])
  calc layerKernel μG ρ β u u'
      = ((∫ α, Real.exp (-(layerAction ρ β α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        show (∫ α, (Real.exp (-(layerAction ρ β α u u')) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG)) = _
        exact integral_ofReal
    _ = ((1 - β * betaCoeff1 ρ μG u u'
          + β ^ 2 * betaCoeff2 ρ μG u u'
          - β ^ 3 * betaCoeff3 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        rw [hreal, layerKernel_real_expansion3 ρ μG hN hρcont β u u']

/-- **(S8) The tail bound at order 4:** `|R₄(β)|
≤ (2M|β|)⁴/24 · exp(2M|β|)`, from `(k+4)! ≥ 24·k!`
termwise. So the remainder after the (constant) β³ term
is genuinely `O(β⁴)` as `β → 0`, with an explicit
constant: **𝒜's (u, u′)-dependence is O(β⁴)** once
`layerKernel_dep_beta3_zero` is in hand. (Still no
positivity conclusion.) -/
theorem layerKernel_tail_bound3 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
        / ((Nat.factorial (k + 4) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ (2 * colCount N * |β|) ^ 4 / 24
        * Real.exp (2 * colCount N * |β|) := by
  set X : ℝ := 2 * colCount N * |β| with hX
  have hc : (0 : ℝ) ≤ colCount N := Nat.cast_nonneg _
  have hXnn : 0 ≤ X :=
    mul_nonneg (mul_nonneg (by norm_num) hc) (abs_nonneg β)
  have hXeq : |β| * (2 * colCount N) = X := by rw [hX]; ring
  have hsumN : Summable fun k => ∫ α,
        ‖(-β * layerDensSum ρ α u u') ^ (k + 4)
          / ((Nat.factorial (k + 4) : ℝ))‖
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_nat_add_iff 4).mpr
      (summable_norm_term_int ρ μG hN hρcont β u u')
  have hsumN' : Summable fun k => ‖∫ α,
        (-β * layerDensSum ρ α u u') ^ (k + 4)
          / ((Nat.factorial (k + 4) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
    hsumN.of_norm_bounded (fun k => by
      have h : ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖
          ≤ ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))‖
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
        norm_integral_le_integral_norm _
      have h2 : ‖‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖‖
          = ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
      rw [h2]
      exact h)
  have hfact : ∀ k : ℕ, (Nat.factorial (k + 4) : ℝ)
      = ((k : ℝ) + 1) * (((k : ℝ) + 2)
        * (((k : ℝ) + 3) * (((k : ℝ) + 4)
          * (Nat.factorial k : ℝ)))) := by
    intro k
    have h : Nat.factorial (k + 4)
        = (k + 4) * ((k + 3) * ((k + 2)
          * ((k + 1) * Nat.factorial k))) := by
      simp only [Nat.factorial_succ]
    calc (Nat.factorial (k + 4) : ℝ)
        = (((k + 4) * ((k + 3) * ((k + 2)
            * ((k + 1) * Nat.factorial k))) : ℕ) : ℝ) := by
          rw [h]
      _ = ((k : ℝ) + 1) * (((k : ℝ) + 2)
            * (((k : ℝ) + 3) * (((k : ℝ) + 4)
              * (Nat.factorial k : ℝ)))) := by
          push_cast
          ring
  have hterm : ∀ k : ℕ, X ^ (k + 4) / (Nat.factorial (k + 4) : ℝ)
      ≤ (X ^ 4 / 24) * (X ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h24 : (24 : ℝ) ≤ ((k : ℝ) + 1) * (((k : ℝ) + 2)
        * (((k : ℝ) + 3) * ((k : ℝ) + 4))) := by
      have e : ((k : ℝ) + 1) * (((k : ℝ) + 2)
          * (((k : ℝ) + 3) * ((k : ℝ) + 4)))
          = (k : ℝ) ^ 4 + 10 * (k : ℝ) ^ 3 + 35 * (k : ℝ) ^ 2
            + 50 * (k : ℝ) + 24 := by ring
      rw [e]
      have h2 := pow_nonneg hk 2
      have h3 := pow_nonneg hk 3
      have h4 := pow_nonneg hk 4
      linarith
    have hpos : (0 : ℝ) < (Nat.factorial (k + 4) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hX4 : (0 : ℝ) ≤ X ^ 4 * X ^ k :=
      mul_nonneg (pow_nonneg hXnn 4) (pow_nonneg hXnn k)
    rw [div_le_iff₀ hpos]
    have hRHS : ((X ^ 4 / 24) * (X ^ k / (Nat.factorial k : ℝ)))
          * (Nat.factorial (k + 4) : ℝ)
        = (X ^ 4 / 24) * X ^ k
          * (((k : ℝ) + 1) * (((k : ℝ) + 2)
            * (((k : ℝ) + 3) * ((k : ℝ) + 4)))) := by
      rw [hfact k]
      field_simp
    rw [hRHS]
    calc X ^ (k + 4) = X ^ 4 * X ^ k := by ring
      _ ≤ (X ^ 4 / 24) * X ^ k
            * (((k : ℝ) + 1) * (((k : ℝ) + 2)
              * (((k : ℝ) + 3) * ((k : ℝ) + 4)))) := by
          have hP : (0 : ℝ) ≤ ((k : ℝ) + 1) * (((k : ℝ) + 2)
              * (((k : ℝ) + 3) * ((k : ℝ) + 4))) :=
            le_trans (by norm_num) h24
          have hrw : (X ^ 4 / 24) * X ^ k
                * (((k : ℝ) + 1) * (((k : ℝ) + 2)
                  * (((k : ℝ) + 3) * ((k : ℝ) + 4))))
              = (X ^ 4 * X ^ k)
                * ((((k : ℝ) + 1) * (((k : ℝ) + 2)
                    * (((k : ℝ) + 3) * ((k : ℝ) + 4)))) / 24) := by
            ring
          rw [hrw]
          exact le_mul_of_one_le_right hX4
            ((one_le_div (by norm_num)).mpr h24)
  calc ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
          / ((Nat.factorial (k + 4) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ ∑' (k : ℕ), ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 4)
          / ((Nat.factorial (k + 4) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        norm_tsum_le_tsum_norm hsumN'
    _ ≤ ∑' (k : ℕ), ∫ α,
            ‖(-β * layerDensSum ρ α u u') ^ (k + 4)
              / ((Nat.factorial (k + 4) : ℝ))‖
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        hsumN'.tsum_le_tsum (fun k => norm_integral_le_integral_norm _)
          hsumN
    _ ≤ ∑' (k : ℕ), X ^ (k + 4) / (Nat.factorial (k + 4) : ℝ) :=
        hsumN.tsum_le_tsum
          (fun k => by
            calc ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 4)
                    / ((Nat.factorial (k + 4) : ℝ))‖
                    ∂(Measure.pi fun _ : LayerSite N => μG)
                ≤ ∫ _α : LayerSite N → G,
                    X ^ (k + 4) / ((Nat.factorial (k + 4) : ℝ))
                    ∂(Measure.pi fun _ : LayerSite N => μG) :=
                  integral_mono_ae
                    (integrable_term ρ μG hN hρcont β u u' (k + 4)).norm
                    (integrable_const _)
                    (Filter.Eventually.of_forall fun α => by
                      have hb := norm_term_le ρ hN β u u' (k + 4) α
                      rwa [hXeq] at hb)
              _ = X ^ (k + 4) / ((Nat.factorial (k + 4) : ℝ)) := by
                  rw [integral_const, probReal_univ, one_smul])
          ((summable_nat_add_iff 4).mpr (Real.summable_pow_div_factorial X))
    _ ≤ ∑' (k : ℕ), (X ^ 4 / 24) * (X ^ k / (Nat.factorial k : ℝ)) :=
        ((summable_nat_add_iff 4).mpr
          (Real.summable_pow_div_factorial X)).tsum_le_tsum hterm
          ((Real.summable_pow_div_factorial X).mul_left _)
    _ = (X ^ 4 / 24) * Real.exp X := by
        rw [tsum_mul_left]
        congr 1
        have h1 : Real.exp X = NormedSpace.exp X :=
          congrFun Real.exp_eq_exp_ℝ _
        rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_inv_mul]

/-- **Headline (β¹, β² and β³ dependence vanish).** At
general `(G, ρ)`, for `N` even and `N ≥ 3`, all three
expansion coefficients of `𝒜` are independent of the
boundary links `(u, u')`: the `(u, u')`-dependence of `𝒜`
is `O(β⁴)`. (The `β¹` and `β²` halves are β2-1b's
`layerKernel_dep_beta2_zero`; the `β³` half is the content
of this brick.) FENCE: an expansion statement — no
positivity of `𝒜` at any `β > 0` follows; `β2` and
(H-PF) remain open. -/
theorem layerKernel_dep_beta3_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' v v' : LayerLink N → G) :
    betaCoeff1 ρ μG u u' = betaCoeff1 ρ μG v v'
      ∧ betaCoeff2 ρ μG u u' = betaCoeff2 ρ μG v v'
      ∧ betaCoeff3 ρ μG u u' = betaCoeff3 ρ μG v v' :=
  ⟨(layerKernel_dep_beta2_zero ρ μG hN hN3 hρcont u u' v v').1,
   (layerKernel_dep_beta2_zero ρ μG hN hN3 hρcont u u' v v').2,
   by rw [betaCoeff3_closed ρ μG hN hN3 hρcont,
      betaCoeff3_closed ρ μG hN hN3 hρcont]⟩

end Expansion3

end ThetLogos
