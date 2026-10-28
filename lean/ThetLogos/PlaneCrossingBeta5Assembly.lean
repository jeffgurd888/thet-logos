/-
# ThetLogos.PlaneCrossingBeta5Assembly — B5-2: the assembly
identity for `κ₅^dep` through the (2,1,1,1) channel

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is an ASSEMBLY brick: pure algebra of the
definitions landed in `PlaneCrossingBeta5` (B5-1), at
general `(G, ρ)` — no irreducibility anywhere. **No sign
is asserted for `kappa5dep`**: the sign question at order
5 is FRONTIER — the surviving channel's degree-(2,1)
sites carry the triple twirl `∫ ρ(g) ρ(g) ρ̄(g)`, which no
module in the tree owns, and no exhibited-square form for
the doubled moment is known. The B5-PROBE seat evaluation
(N = 4, the two seats `(C₃, faithful χ)` and `(S₃, std)`,
channel form `kappa5chan2111`) is restated at exactly its
scope in the fences of the diagonal corollary below;
nothing here widens it.

**The identity, and the correction it carries.** The
seam named in B5-1 expected `kappa5dep` to reduce to the
channel sum `kappa5chan2111` up to normalization and
baseline. The definitions force a richer true form, with
two discrepancies NAMED here: (i) the channel enters
through its *excess* over the fully-split baseline
`μ₂e₁³` per summand, at normalization `−(1/2)·d⁻⁵`
(60 ordered tuples per (support, doubled column), over
the assembly's 120); (ii) there is an order-4 dressing
term `(4 + (M−4)·B)·κ₄^dep` (`M = colCount N`,
`B = 1 − e₁/d`): the `(2,1,1,1)` tuples contribute the
order-4 excess of their support (the sub-multiset
`(1,1,1,1)` inside `x_P²∏x`, with binomial coefficient
2), and the `(1,1,1,1,1)` tuples contribute it through
the private-column factorization of the fivefold moment.
The headline is therefore stated with
`kappa5chanExcess` (the channel sum minus its baseline,
as a defined sum), and a companion lemma rewrites it
through the raw channel `kappa5chan2111` of the probe's
fence.
-/

import Mathlib.Data.Nat.Choose.Multinomial
import ThetLogos.PlaneCrossingBeta5

open MeasureTheory Finset

namespace ThetLogos

section Assembly5

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The (2,1,1,1) channel excess**: the channel sum of
B5-1 with its fully-split baseline `μ₂e₁³` removed
summand by summand — the combination the assembly
identity actually sees. No sign is asserted for it. -/
noncomputable def kappa5chanExcess (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (doubledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)

/-- The channel excess is the raw channel sum minus its
baseline: each primitive quad contributes four doubled
columns, each carrying baseline `μ₂e₁³`. -/
theorem kappa5chanExcess_eq (u u' : LayerLink N → G) :
    kappa5chanExcess ρ μG u u'
      = kappa5chan2111 ρ μG u u'
        - 4 * ((primitiveQuads (N := N)).card : ℝ)
          * realMoment ρ μG 2 * (e1 ρ μG) ^ 3 := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ _P ∈ C, (realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
        = 4 * (realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    rw [Finset.sum_const, hC4, nsmul_eq_mul, Nat.cast_ofNat]
  have step1 : kappa5chanExcess ρ μG u u'
      = kappa5chan2111 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
            (realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    unfold kappa5chanExcess kappa5chan2111
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
        (realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
      = 4 * ((primitiveQuads (N := N)).card : ℝ)
        * realMoment ρ μG 2 * (e1 ρ μG) ^ 3 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-! ## §1. Counting helpers -/

/-- There are at least four columns whenever `3 ≤ N`:
three directions at the zero site, and a fourth column
at a neighbouring site. -/
theorem four_le_card_columns (hN3 : 3 ≤ N) :
    4 ≤ Fintype.card (LayerColumn N) := by
  classical
  have h10 : (1 : ZMod N) ≠ 0 := by
    intro h
    have hcast : ((1 : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_one]; exact h
    rw [ZMod.natCast_eq_zero_iff] at hcast
    have hle : N ≤ 1 := Nat.le_of_dvd (by norm_num) hcast
    omega
  have hs10 : (⟨fun i => if i = 1 then (1 : ZMod N) else 0, by
      show ((if (0 : Fin 4) = 1 then (1 : ZMod N) else 0)).val = 0
      rw [if_neg (by decide), ZMod.val_zero]⟩ : LayerSite N)
      ≠ ⟨fun _ => 0, by simp⟩ := by
    intro h
    have h2 := congrFun (congrArg Subtype.val h) 1
    have h3 : (if (1 : Fin 4) = 1 then (1 : ZMod N) else 0) = 0 := h2
    rw [if_pos rfl] at h3
    exact h10 h3
  have hne : ∀ {ν μ : Fin 4} (hν : ν ≠ 0) (hμ : μ ≠ 0),
      ν ≠ μ →
      (⟨⟨fun _ => 0, by simp⟩, ⟨ν, hν⟩⟩ : LayerColumn N)
        ≠ ⟨⟨fun _ => 0, by simp⟩, ⟨μ, hμ⟩⟩ := by
    intro ν μ hν hμ hνμ h
    have h2 := congrArg (fun P : LayerColumn N => (P.2 : Fin 4)) h
    simp only [] at h2
    exact hνμ h2
  have hsne : ∀ (ν : Fin 4) (hν : ν ≠ 0),
      (⟨⟨fun i => if i = 1 then (1 : ZMod N) else 0, by
        show ((if (0 : Fin 4) = 1 then (1 : ZMod N) else 0)).val = 0
        rw [if_neg (by decide), ZMod.val_zero]⟩, ⟨1, by decide⟩⟩ :
        LayerColumn N)
      ≠ ⟨⟨fun _ => 0, by simp⟩, ⟨ν, hν⟩⟩ := by
    intro ν hν h
    exact hs10 (congrArg Prod.fst h)
  have h4 : ({(⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩ :
        LayerColumn N),
      ⟨⟨fun _ => 0, by simp⟩, ⟨2, by decide⟩⟩,
      ⟨⟨fun _ => 0, by simp⟩, ⟨3, by decide⟩⟩,
      ⟨⟨fun i => if i = 1 then (1 : ZMod N) else 0, by
        show ((if (0 : Fin 4) = 1 then (1 : ZMod N) else 0)).val = 0
        rw [if_neg (by decide), ZMod.val_zero]⟩, ⟨1, by decide⟩⟩} :
      Finset (LayerColumn N)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hne (by decide) (by decide) (by decide),
        ⟨hne (by decide) (by decide) (by decide),
          fun h => hsne 1 (by decide) h.symm⟩⟩),
      Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hne (by decide) (by decide) (by decide),
        fun h => hsne 2 (by decide) h.symm⟩),
      Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun h => hsne 3 (by decide) h.symm),
      Finset.card_singleton]
  have hle : ({(⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩ :
        LayerColumn N),
      ⟨⟨fun _ => 0, by simp⟩, ⟨2, by decide⟩⟩,
      ⟨⟨fun _ => 0, by simp⟩, ⟨3, by decide⟩⟩,
      ⟨⟨fun i => if i = 1 then (1 : ZMod N) else 0, by
        show ((if (0 : Fin 4) = 1 then (1 : ZMod N) else 0)).val = 0
        rw [if_neg (by decide), ZMod.val_zero]⟩, ⟨1, by decide⟩⟩} :
      Finset (LayerColumn N)).card ≤ Finset.univ.card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_univ, h4] at hle
  exact hle

/-- Real cast of a fourfold erased column count. -/
theorem cast_card_erase_four (hN3 : 3 ≤ N) {A B C D : LayerColumn N}
    (hAB : B ∈ Finset.univ.erase A)
    (hABC : C ∈ (Finset.univ.erase A).erase B)
    (hABCD : D ∈ ((Finset.univ.erase A).erase B).erase C) :
    (((((Finset.univ.erase A).erase B).erase C).erase D).card : ℝ)
      = colCount N - 4 := by
  have h4 : 4 ≤ Fintype.card (LayerColumn N) :=
    four_le_card_columns (N := N) hN3
  have hcard : ((((Finset.univ.erase A).erase B).erase C).erase D).card
      = Fintype.card (LayerColumn N) - 4 := by
    have e1 := Finset.card_erase_of_mem hABCD
    have e2 := Finset.card_erase_of_mem hABC
    have e3 := Finset.card_erase_of_mem hAB
    have e4 := Finset.card_erase_of_mem (Finset.mem_univ A)
    rw [Finset.card_univ] at e4
    omega
  rw [hcard, Nat.cast_sub h4, Nat.cast_ofNat]
  rfl

/-- The second density moment in expanded form:
`A₂ = 1 − 2e₁/d + μ₂/d²`. -/
theorem densMomentValue_two :
    densMomentValue ρ μG 2
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

/-! ## §2. Factored moments on supports of size at most three -/

/-- **Character power-moments factor on small supports.**
For `T` of card at most 3 and arbitrary exponents, the
integral of `∏ r_P^{aP}` is the product of the Haar
moments: at card 3 one of the three columns owns a
private site (`exists_private_site_triple`) and the
strip engine separates it; the rest is the two-column
factorization and the single-column Haar moment. -/
theorem integral_colRe_prod_pow_of_card_le_three (hN : Even N)
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
theorem integral_colDens_triple_pow (hN : Even N) (hN3 : 3 ≤ N)
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
      integral_colRe_prod_pow_of_card_le_three ρ μG hN hN3 hρcont
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
theorem integral_colDens_prod_pow_of_card_le_three (hN : Even N)
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
    exact integral_colDens_triple_pow ρ μG hN hN3 hρcont u u' hPQ hPR
      hQR a

/-! ## §3. The per-pattern values at order five -/

/-- **The doubled pattern value.** For a 4-support `C`
and a distinguished column `P ∈ C`, the `(2,1,1,1)`
pattern value splits into its fully-split baseline
`A₂B³`, twice the order-4 excess of the support (the
`(1,1,1,1)` sub-multiset inside `x_P²∏x`, with binomial
coefficient `2 = (2 choose 1)`), and minus the doubled
excess at weight `d⁻⁵`. Proved by the two-level subset
expansion: `x_P²` by `add_pow` over `range 3`, the
remaining three densities by the powerset expansion of
`PlaneCrossingBeta4.integral_colDens_prod_quadruple`. -/
theorem integral_colDens_prod_quadruple_doubled (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) (P : LayerColumn N) (hP : P ∈ C) :
    ∫ α : LayerSite N → G,
        ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hScard : (C.erase P).card = 3 := by
    rw [Finset.card_erase_of_mem hP, hC]
  have hnotP : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
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
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have h4 : (C.erase P).card + 1 = 4 := by rw [hScard]
      rw [h4]
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
        integral_colRe_prod_pow_of_card_le_three ρ μG hN hN3
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
          * (e1 ρ μG) ^ T.card := by
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
            + (if T = C.erase P then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
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
            + (if T = C.erase P then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
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
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
          * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
    have hT0 : ∀ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 0 : ℝ) * c ^ (0 + T.card)
            * (e1 ρ μG) ^ T.card
          = (c * e1 ρ μG) ^ T.card := by
      intro T _
      simp only [Nat.choose_zero_right, Nat.cast_one, zero_add,
        one_mul]
      exact (mul_pow _ _ _).symm
    exact (Finset.sum_congr rfl hT0).trans hBS
  have hB1base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (e1 ρ μG) ^ (T.card + 1))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
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
  have hB1corr : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (if T = C.erase P then
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0))
      = 2 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hScard]
    rw [show (1 + 3 : ℕ) = 4 from rfl, hc4]
    simp only [Nat.choose_one_right, Nat.cast_ofNat]
  have hB1 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 1 : ℝ) * c ^ (1 + T.card)
          * ((e1 ρ μG) ^ (T.card + 1)
            + (if T = C.erase P then
                (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
               else 0)))
      = (2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        + 2 * ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB1base, hB1corr]
  have hB2base : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3 := by
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
  have hB2corr : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (if T = C.erase P then
              (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
             else 0))
      = -(((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    rw [Finset.sum_congr rfl (fun T _ => by rw [mul_ite, mul_zero]),
      Finset.sum_ite_eq' (C.erase P).powerset (C.erase P)
        (fun T => ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true,
      hScard, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show (2 + 3 : ℕ) = 5 from rfl, hc5]
    ring
  have hB2 : (∑ T ∈ (C.erase P).powerset,
        ((2 : ℕ).choose 2 : ℝ) * c ^ (2 + T.card)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ T.card
            + (if T = C.erase P then
                (doubledQuadReMoment ρ μG C P u u'
                  - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
               else 0)))
      = (c ^ 2 * realMoment ρ μG 2)
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3
        - ((d : ℝ)⁻¹) ^ 5
          * (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    rw [Finset.sum_congr rfl (fun T _ => mul_add _ _ _),
      Finset.sum_add_distrib, hB2base, hB2corr]
    simp only [sub_eq_add_neg]
  have hA2 : densMomentValue ρ μG 2
      = 1 + 2 * c * (e1 ρ μG) + c ^ 2 * realMoment ρ μG 2 := by
    rw [densMomentValue_two, hc]
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
    _ = (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + ((2 * c * e1 ρ μG) * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
          + ((c ^ 2 * realMoment ρ μG 2)
              * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            - ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
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
    _ = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
        rw [hA2]
        ring

/-- **The fivefold excess factors through order 4.**
For a 5-support `C`, the private column `X` of B5-0's
selection rule splits the fivefold moment (the B5-1
strip calc at that column), and every other erasure
`C.erase x` is non-primitive — `X`'s private site stays
private there — so its order-4 excess vanishes and the
sum of erasure excesses is the single term at `X`. -/
theorem quadReMoment_card_five_excess (hN : Even N)
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

/-- **The quintuple pattern value.** For a 5-support
`C`, the all-distinct value is the fully-split baseline
`B⁵` plus `B·d⁻⁴` times the sum of the order-4 excesses
of its five 4-subsupports: the subset expansion has
three levels — subsets of size at most 3 factor, the
five 4-subsets contribute their excesses at weight
`c⁴`, and the top subset contributes the fivefold
excess at weight `c⁵`, which the previous lemma factors
as `e₁` times the same erasure sum; `c⁴ + c⁵e₁ =
(1 − e₁/d)·d⁻⁴` closes the assembly. -/
theorem integral_colDens_prod_quintuple (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∫ α : LayerSite N → G, ∏ Q ∈ C, colDensC ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5
        + (1 - e1 ρ μG / (d : ℝ)) * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
  classical
  set c : ℝ := (-(d : ℝ)⁻¹) with hc
  have hc4 : c ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by rw [hc]; ring
  have hc5 : c ^ 5 = -((d : ℝ)⁻¹) ^ 5 := by rw [hc]; ring
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
          + (if T = C then
              c ^ 5 * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
             else 0) := by
    intro T hT
    have hsub : T ⊆ C := Finset.mem_powerset.mp hT
    rw [integral_const_mul]
    by_cases hT5 : T = C
    · subst hT5
      have hnotpc : T ∉ Finset.powersetCard 4 T :=
        fun h => by
          have h4 := (Finset.mem_powersetCard.mp h).2
          rw [hC] at h4
          exact absurd h4 (by decide)
      rw [if_neg hnotpc, if_pos rfl, hC]
      show c ^ 5 * quadReMoment ρ μG T u u'
        = c ^ 5 * (e1 ρ μG) ^ 5 + 0
          + c ^ 5 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 5)
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
            + 0
        ring
      · rw [if_neg hT4, add_zero, add_zero]
        have hcard : T.card ≤ 3 := by
          have h1 : T.card ≤ 5 := le_trans
            (Finset.card_le_card hsub) (le_of_eq hC)
          have hne4 : T.card ≠ 4 := fun h4 =>
            hT4 (Finset.mem_powersetCard.mpr ⟨hsub, h4⟩)
          have hne5 : T.card ≠ 5 := fun h5 =>
            hT5 (Finset.eq_of_subset_of_card_le hsub
              (by rw [hC]; omega))
          omega
        rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3
          hρcont u u' T hcard]
  have hbij : ∑ x ∈ C,
        (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
      = ∑ T ∈ Finset.powersetCard 4 C,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    refine Finset.sum_bij (fun x _ => C.erase x) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_powersetCard.mpr ⟨Finset.erase_subset x C,
        by rw [Finset.card_erase_of_mem hx, hC]⟩
    · intro x hx y hy hxy
      by_contra hne
      have hxmem : x ∈ C.erase y :=
        Finset.mem_erase.mpr ⟨hne, hx⟩
      rw [← hxy] at hxmem
      exact (Finset.mem_erase.mp hxmem).1 rfl
    · intro T hT
      have hsub : T ⊆ C := (Finset.mem_powersetCard.mp hT).1
      have hcard4 : T.card = 4 := (Finset.mem_powersetCard.mp hT).2
      have hsd : (C \ T).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hC,
          hcard4]
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsd
      have hxC : x ∈ C := (Finset.mem_sdiff.mp (by
        rw [hx]
        exact Finset.mem_singleton_self x)).1
      refine ⟨x, hxC, ?_⟩
      have hxT : x ∉ T := (Finset.mem_sdiff.mp (by
        rw [hx]
        exact Finset.mem_singleton_self x)).2
      have hsub2 : T ⊆ C.erase x := by
        intro Q hQ
        exact Finset.mem_erase.mpr
          ⟨fun h => hxT (h ▸ hQ), hsub hQ⟩
      have hcardx : (C.erase x).card = 4 := by
        rw [Finset.card_erase_of_mem hxC, hC]
      exact (Finset.eq_of_subset_of_card_le hsub2
        (by rw [hcardx, hcard4])).symm
    · intro x _
      rfl
  have hBase5 : (∑ T ∈ C.powerset, c ^ T.card * (e1 ρ μG) ^ T.card)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
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
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 5 := by
          rw [Finset.prod_const, hC]
          congr 1
          rw [div_eq_inv_mul]
          ring
  have hMid5 : (∑ T ∈ C.powerset,
        (if T ∈ Finset.powersetCard 4 C then
          c ^ 4 * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
         else 0))
      = c ^ 4 * ∑ x ∈ C,
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
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
    rw [step1, ← Finset.mul_sum, hbij]
  have hTop5 : (∑ T ∈ C.powerset,
        (if T = C then
          c ^ 5 * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5)
         else 0))
      = c ^ 5 * ((e1 ρ μG) * ∑ x ∈ C,
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)) := by
    rw [Finset.sum_ite_eq' C.powerset C
      (fun _ => c ^ 5
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 5))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true]
    rw [quadReMoment_card_five_excess ρ μG hN hN3 hρcont u u' C hC]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun T _ =>
      Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl
              fun Q _ => pow_one (colRe ρ u u' Q α))) _),
    Finset.sum_congr rfl hval, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hBase5, hMid5, hTop5, hc4, hc5]
  ring

/-- **The doubled excess vanishes off primitive
supports.** For a non-primitive 4-support `C` and
`P ∈ C`, `doubledQuadReMoment C P = μ₂·e₁³`: take a
private column `X` of `C`. At `X = P` the doubled
strip leaves `μ₂` times a triple moment, which
factors; at `X ≠ P` the single strip leaves `e₁`
times the doubled moment of a triple, which factors
by the cardinality-≤-3 power factorization. -/
theorem doubledQuadReMoment_sub_eq_zero_of_not_primitive
    (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C)
    {P : LayerColumn N} (hP : P ∈ C) :
    doubledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 3 = 0 := by
  classical
  have hprivC : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    push_neg at hcon
    exact hCnp ⟨hC, hcon⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hprivC
  by_cases hXP : X = P
  · subst hXP
    rw [doubledQuadReMoment_strip_doubled ρ μG hN hN3 hρcont
      u u' hsX hpriv]
    have hcard3 : (C.erase X).card ≤ 3 := by
      have h1 : (C.erase X).card = C.card - 1 :=
        Finset.card_erase_of_mem hXC
      omega
    have hcard3' : (C.erase X).card = 3 := by
      have h1 : (C.erase X).card = C.card - 1 :=
        Finset.card_erase_of_mem hXC
      omega
    show realMoment ρ μG 2 * (∫ α : LayerSite N → G,
        ∏ P ∈ C.erase X, colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG))
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 3 = 0
    rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3 hρcont
      u u' (C.erase X) hcard3, hcard3']
    exact sub_self _
  · have hPX : P ∈ C.erase X :=
      Finset.mem_erase.mpr ⟨Ne.symm hXP, hP⟩
    rw [doubledQuadReMoment_strip_single ρ μG hN hN3 hρcont
      u u' hP hXC hXP hsX hpriv]
    have hcard3X : (C.erase X).card ≤ 3 := by
      have h1 : (C.erase X).card = C.card - 1 :=
        Finset.card_erase_of_mem hXC
      omega
    have hfact : doubledQuadReMoment ρ μG (C.erase X) P u u'
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
      have hcong2 : ∀ α : LayerSite N → G,
          (colRe ρ u u' P α) ^ 2
              * ∏ Q ∈ (C.erase X).erase P, colRe ρ u u' Q α
            = ∏ Q ∈ C.erase X,
                (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1) := by
        intro α
        rw [← Finset.mul_prod_erase (C.erase X)
          (fun Q => (colRe ρ u u' Q α)
            ^ (if Q = P then 2 else 1)) hPX]
        congr 1
        · rw [if_pos rfl]
        · exact Finset.prod_congr rfl fun Q hQ => by
            rw [if_neg (Finset.mem_erase.mp hQ).1, pow_one]
      calc doubledQuadReMoment ρ μG (C.erase X) P u u'
          = ∫ α : LayerSite N → G,
              ∏ Q ∈ C.erase X,
                (colRe ρ u u' Q α) ^ (if Q = P then 2 else 1)
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
            integral_congr_ae
              (Filter.Eventually.of_forall hcong2)
        _ = ∏ Q ∈ C.erase X,
              realMoment ρ μG (if Q = P then 2 else 1) :=
            integral_colRe_prod_pow_of_card_le_three ρ μG hN hN3
              hρcont u u' (C.erase X) hcard3X
              (fun Q => if Q = P then 2 else 1)
        _ = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
            rw [← Finset.mul_prod_erase (C.erase X)
              (fun Q => realMoment ρ μG
                (if Q = P then 2 else 1)) hPX, if_pos rfl]
            have h2 : ∀ Q ∈ (C.erase X).erase P,
                realMoment ρ μG (if Q = P then 2 else 1)
                  = e1 ρ μG := by
              intro Q hQ
              rw [if_neg (Finset.mem_erase.mp hQ).1,
                realMoment_one]
            rw [Finset.prod_congr rfl h2, Finset.prod_const]
            have h3 : ((C.erase X).erase P).card = 2 := by
              rw [Finset.card_erase_of_mem hPX,
                Finset.card_erase_of_mem hXC, hC]
            rw [h3]
    have hring : (e1 ρ μG)
          * (realMoment ρ μG 2 * (e1 ρ μG) ^ 2)
        = realMoment ρ μG 2 * (e1 ρ μG) ^ 3 := by ring
    rw [hfact, hring]
    exact sub_self _

/-- **The powerset channel sum is the primitive
channel sum.** Over the full `powersetCard 4`, the
doubled-excess double sum equals `kappa5chanExcess`:
off `primitiveQuads` every term vanishes by the
previous lemma. -/
theorem sum_powersetCard_four_doubled_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4, ∑ P ∈ C,
        (doubledQuadReMoment ρ μG C P u u'
          - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = kappa5chanExcess ρ μG u u' := by
  classical
  show _ = ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (doubledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
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
    exact doubledQuadReMoment_sub_eq_zero_of_not_primitive ρ μG
      hN hN3 hρcont u u' hcard hnp hP

/-- **The fifth-power expansion, integrated.** The
multinomial expansion of `(layerDensSum)^5`, integrated
termwise: each exponent function `k` contributes its
multinomial coefficient times the integral of the
column-density monomial `∏ P, colDensC(P)^(k P)`.
Integrability of each monomial is by the uniform bound
`|colDensC| ≤ 2` (total mass `2^5 = 32`). -/
theorem integral_layerDensSum_pow_five (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 5
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ k ∈ Finset.piAntidiag Finset.univ 5,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG) := by
  classical
  have hmeas : ∀ P : LayerColumn N,
      Measurable fun α : LayerSite N → G =>
        colDensC ρ u u' P α :=
    fun P => measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2
  have hInt : ∀ k ∈ Finset.piAntidiag Finset.univ 5,
      Integrable (fun α : LayerSite N → G =>
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro k hk
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound
      (Finset.measurable_prod Finset.univ fun P _ =>
        (hmeas P).pow_const (k P)).aestronglyMeasurable
      (32 : ℝ) (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    have hsum5 : ∑ P ∈ Finset.univ, k P = 5 :=
      (Finset.mem_piAntidiag.mp hk).1
    have hle : ∏ P ∈ Finset.univ, |(colDensC ρ u u' P α) ^ (k P)|
        ≤ ∏ P ∈ Finset.univ, (2 : ℝ) ^ (k P) :=
      Finset.prod_le_prod₀ (fun P _ => abs_nonneg _)
        (fun P _ => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_colDensC_le ρ u u' P α) _)
    refine le_trans hle ?_
    rw [Finset.prod_pow_eq_pow_sum, hsum5]
    norm_num
  have hpt : ∀ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 5
      = ∑ k ∈ Finset.piAntidiag Finset.univ 5,
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P) := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u']
    exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ
      (fun P => colDensC ρ u u' P α) 5
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ hInt,
    Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)]

/-- The support of an exponent function: the columns
carrying a nonzero exponent. -/
noncomputable def suppOf (k : LayerColumn N → ℕ) :
    Finset (LayerColumn N) :=
  Finset.univ.filter (fun P => k P ≠ 0)

/-- Summation over all columns collapses to the
support: off-support exponents are zero. -/
theorem sum_univ_eq_sum_suppOf (k : LayerColumn N → ℕ) :
    ∑ P ∈ Finset.univ, k P = ∑ P ∈ suppOf k, k P :=
  (Finset.sum_subset (Finset.filter_subset _ _)
    (fun P _ hP => not_not.mp (fun hne =>
      hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩)))).symm

/-- The monomial integral collapses to the support:
off-support factors are `x^0 = 1`. -/
theorem integral_colDens_prod_pow_univ
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (k : LayerColumn N → ℕ) :
    ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ∏ P ∈ suppOf k, (colDensC ρ u u' P α) ^ (k P)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
  integral_congr_ae (Filter.Eventually.of_forall fun α =>
    (Finset.prod_subset (Finset.filter_subset _ _)
      (fun P _ hP => by
        rw [not_not.mp (fun hne =>
          hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩))]
        exact pow_zero _)).symm)

/-- **Fiberwise split by support.** The integrated
expansion, regrouped by the support of the exponent
function. -/
theorem sum_piAntidiag_fiberwise (F : (LayerColumn N → ℕ) → ℝ) :
    ∑ k ∈ Finset.piAntidiag Finset.univ 5, F k
      = ∑ C ∈ Finset.univ.powerset,
          ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
              (fun k => suppOf k = C), F k :=
  (Finset.sum_fiberwise_of_maps_to (fun k _ =>
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)) F).symm

/-- **Fibers over supports of card `0` or `≥ 6` are
empty**: on its support every exponent is at least
`1`, so the support's card is at most the total
exponent sum `5`, and a card-`0` support carries sum
`0 ≠ 5`. -/
theorem fiber_eq_empty_of_card_ne (C : Finset (LayerColumn N))
    (hC : C.card = 0 ∨ 6 ≤ C.card) :
    (Finset.piAntidiag Finset.univ 5).filter
        (fun k => suppOf k = C) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun k hk => ?_
  have hk5 : ∑ P ∈ Finset.univ, k P = 5 :=
    (Finset.mem_piAntidiag.mp
      (Finset.mem_filter.mp hk).1).1
  have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
  have hsumC : ∑ P ∈ C, k P = 5 := by
    rw [← hsupp, ← sum_univ_eq_sum_suppOf]
    exact hk5
  have hle : C.card ≤ ∑ P ∈ C, k P := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPC : P ∈ suppOf k := hsupp ▸ hP
    have : k P ≠ 0 :=
      (Finset.mem_filter.mp hPC).2
    exact Nat.one_le_iff_ne_zero.mpr this
  rw [hsumC] at hle
  rcases hC with h0 | h6
  · have : C = ∅ := Finset.card_eq_zero.mp h0
    rw [this, Finset.sum_empty] at hsumC
    exact absurd hsumC (by norm_num)
  · omega

/-- **Factorial times choose is the falling product.**
`j ! · C(M, j) = M(M−1)⋯(M−j+1)` as reals, via
`Nat.descFactorial`: induction on `j` when `j ≤ M`,
and both sides vanish when `M < j` (the descending
factorial by `Nat.descFactorial_eq_zero_iff_lt`, the
product by its zero factor at `i = M`). -/
theorem cast_factorial_mul_choose (j : ℕ) :
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

/-- **Multinomial from the factorial product.** If
the factorials of the exponents of `k` multiply to
`p ≠ 0`, the multinomial coefficient is `120 / p`,
by `Nat.multinomial_spec` at total exponent `5`. -/
theorem multinomial_univ_eq (k : LayerColumn N → ℕ)
    (hk5 : ∑ P ∈ Finset.univ, k P = 5) (p : ℕ)
    (hp : ∏ P ∈ Finset.univ, Nat.factorial (k P) = p)
    (hp0 : p ≠ 0) :
    (Nat.multinomial Finset.univ k : ℝ) = 120 / (p : ℝ) := by
  have h := Nat.multinomial_spec Finset.univ k
  rw [hp, hk5] at h
  have h120 : Nat.factorial 5 = 120 := by
    norm_num [Nat.factorial]
  rw [h120] at h
  have h' : (p : ℝ) * (Nat.multinomial Finset.univ k : ℝ)
      = 120 := by exact_mod_cast h
  rw [eq_div_iff (by exact_mod_cast hp0 : (p : ℝ) ≠ 0), mul_comm]
  exact h'

/-- **The card-5 fiber.** Over a 5-support `C`, the
fiber of the expansion is the single indicator
exponent (each exponent on the support is `1`, by
`Finset.sum_eq_sum_iff_of_le` at total `5 = card`),
its multinomial coefficient is `120`, and its value
is the quintuple value `(★)`. -/
theorem fiber_card_five (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 5) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 120 * ((1 - e1 ρ μG / (d : ℝ)) ^ 5
          + (1 - e1 ρ μG / (d : ℝ)) * ((d : ℝ)⁻¹) ^ 4
            * ∑ x ∈ C,
              (quadReMoment ρ μG (C.erase x) u u'
                - (e1 ρ μG) ^ 4)) := by
  classical
  have hfib : (Finset.piAntidiag Finset.univ 5).filter
        (fun k => suppOf k = C)
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
          simp [Finset.filter_mem_eq_inter, hC]
        · intro P _
          exact Finset.mem_univ P
      · have hsupp : suppOf (fun P => if P ∈ C then 1 else 0)
            = C := by
          refine Finset.ext fun P => ?_
          simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
            true_and]
          by_cases hP : P ∈ C <;> simp [hP]
        exact hsupp
    · intro k hk
      have hk5 : ∑ P ∈ Finset.univ, k P = 5 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
      have hsumEq : ∑ P ∈ suppOf k, (fun _ => (1 : ℕ)) P
          = ∑ P ∈ suppOf k, k P := by
        have h1 : ∑ P ∈ suppOf k, (fun _ => (1 : ℕ)) P
            = (suppOf k).card := by simp
        rw [h1]
        have h2 : ∑ P ∈ suppOf k, k P = 5 := by
          rw [← sum_univ_eq_sum_suppOf]
          exact hk5
        rw [h2, hsupp, hC]
      have hone : ∀ P ∈ suppOf k, k P = 1 := by
        have h := (Finset.sum_eq_sum_iff_of_le
          (s := suppOf k) (f := fun _ => (1 : ℕ)) (g := k)
          (fun P hP => Nat.one_le_iff_ne_zero.mpr
            (Finset.mem_filter.mp hP).2)).mp hsumEq
        intro P hP
        exact (h P hP).symm
      funext P
      by_cases hP : P ∈ C
      · have hPs : P ∈ suppOf k := hsupp ▸ hP
        rw [hone P hPs, if_pos hP]
      · have hPs : P ∉ suppOf k := hsupp ▸ hP
        have hk0 : k P = 0 := by
          by_contra hne
          exact hPs (Finset.mem_filter.mpr
            ⟨Finset.mem_univ P, hne⟩)
        rw [hk0, if_neg hP]
  rw [hfib, Finset.sum_singleton]
  have hmult : (Nat.multinomial Finset.univ
        (fun P => if P ∈ C then 1 else 0) : ℝ) = 120 := by
    have hp : ∏ P ∈ Finset.univ,
        Nat.factorial ((fun P => if P ∈ C then 1 else 0) P)
          = 1 := by
      exact (Finset.prod_subset (Finset.subset_univ C)
        (fun P _ hP => by simp [hP])).symm.trans
        (Finset.prod_eq_one fun P _ => by
          by_cases hP : P ∈ C <;> simp [hP])
    have hk5 : ∑ P ∈ Finset.univ,
        (fun P => if P ∈ C then 1 else 0) P = 5 := by
      have h1 : ∀ P ∈ Finset.univ,
          (fun P => if P ∈ C then (1 : ℕ) else 0) P
            = if P ∈ C then 1 else 0 := fun P _ => rfl
      rw [Finset.sum_congr rfl h1, Finset.sum_boole]
      simp [Finset.filter_mem_eq_inter, hC]
    have := multinomial_univ_eq (fun P => if P ∈ C then 1 else 0)
      hk5 1 hp one_ne_zero
    rw [this]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ P ∈ Finset.univ,
          (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 5
        + (1 - e1 ρ μG / (d : ℝ)) * ((d : ℝ)⁻¹) ^ 4
          * ∑ x ∈ C,
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) := by
    have hsupp : suppOf (fun P => if P ∈ C then 1 else 0)
        = C := by
      refine Finset.ext fun P => ?_
      simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases hP : P ∈ C <;> simp [hP]
    rw [integral_colDens_prod_pow_univ ρ μG hρcont u u'
      (fun P => if P ∈ C then 1 else 0), hsupp]
    have hprod : ∀ α : LayerSite N → G,
        ∏ P ∈ C, (colDensC ρ u u' P α)
            ^ ((fun P => if P ∈ C then 1 else 0) P)
          = ∏ P ∈ C, colDensC ρ u u' P α :=
      fun α => Finset.prod_congr rfl fun P hP => by
        simp [hP]
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
    exact integral_colDens_prod_quintuple ρ μG hN hN3 hρcont
      u u' C hC
  rw [hmult, hval]

/-- The doubled pattern at `(C, P)`: exponent `2` at
`P`, exponent `1` on the rest of `C`, `0` off `C` —
the `(2,1,1,1)` exponent shape. -/
noncomputable def doubledPattern (C : Finset (LayerColumn N))
    (P : LayerColumn N) : LayerColumn N → ℕ :=
  fun Q => if Q = P then 2 else if Q ∈ C then 1 else 0

/-- **The card-4 fiber.** Over a 4-support `C`, the
fiber of the expansion is the four doubled patterns
(one per `P ∈ C`): classification by the
excess-exponent sum `∑ (k Q − 1) = 1` over `C`, whose
support in `C` is a singleton. Each pattern has
multinomial coefficient `60` and value `(★₂)`. -/
theorem fiber_card_four (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P ∈ C, (60 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
  classical
  have hsuppPat : ∀ P ∈ C,
      suppOf (doubledPattern C P) = C := by
    intro P hP
    refine Finset.ext fun Q => ?_
    simp only [suppOf, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hQP : Q = P
    · subst hQP
      simp [doubledPattern, hP]
    · by_cases hQC : Q ∈ C <;> simp [doubledPattern, hQP, hQC]
  have hsumPat : ∀ P ∈ C,
      ∑ Q ∈ Finset.univ, doubledPattern C P Q = 5 := by
    intro P hP
    have h1 : ∑ Q ∈ Finset.univ, doubledPattern C P Q
        = ∑ Q ∈ C, doubledPattern C P Q :=
      (Finset.sum_subset (Finset.subset_univ C)
        (fun Q _ hQ => by
          have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
          simp [doubledPattern, hQ, hQP])).symm
    rw [h1, ← Finset.add_sum_erase C _ hP]
    have h2 : ∀ Q ∈ C.erase P, doubledPattern C P Q = 1 :=
      fun Q hQ => by
        simp [doubledPattern, (Finset.mem_erase.mp hQ).1,
          (Finset.mem_erase.mp hQ).2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem hP, hC]
    have hPP : doubledPattern C P P = 2 := by
      simp [doubledPattern]
    rw [hPP]
    decide
  have hmemPat : ∀ P ∈ C, doubledPattern C P
      ∈ (Finset.piAntidiag Finset.univ 5).filter
        (fun k => suppOf k = C) := by
    intro P hP
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨hsumPat P hP, fun Q _ => Finset.mem_univ Q⟩,
      hsuppPat P hP⟩
  have hvalPat : ∀ P ∈ C,
      ((Nat.multinomial Finset.univ (doubledPattern C P) : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ Q ∈ Finset.univ,
                (colDensC ρ u u' Q α) ^ (doubledPattern C P Q)
              ∂(Measure.pi fun _ : LayerSite N => μG)
        = (60 : ℝ)
          * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
            - ((d : ℝ)⁻¹) ^ 5
              * (doubledQuadReMoment ρ μG C P u u'
                - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)) := by
    intro P hP
    have hfact : ∏ Q ∈ Finset.univ,
        Nat.factorial (doubledPattern C P Q) = 2 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial (doubledPattern C P Q)
          = ∏ Q ∈ C, Nat.factorial (doubledPattern C P Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := fun h => hQ (h.symm ▸ hP)
            simp [doubledPattern, hQ, hQP])).symm
      rw [h1, ← Finset.mul_prod_erase C _ hP]
      have h2 : ∀ Q ∈ C.erase P,
          Nat.factorial (doubledPattern C P Q) = 1 :=
        fun Q hQ => by
          simp [doubledPattern, (Finset.mem_erase.mp hQ).1,
            (Finset.mem_erase.mp hQ).2]
      rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
      simp [doubledPattern]
    have hmult : (Nat.multinomial Finset.univ
          (doubledPattern C P) : ℝ) = 60 := by
      have h := multinomial_univ_eq (doubledPattern C P)
        (hsumPat P hP) 2 hfact two_ne_zero
      rw [h]
      norm_num
    have hint : ∫ α : LayerSite N → G,
          ∏ Q ∈ Finset.univ,
            (colDensC ρ u u' Q α) ^ (doubledPattern C P Q)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
      rw [integral_colDens_prod_pow_univ ρ μG hρcont u u'
        (doubledPattern C P), hsuppPat P hP]
      have hprod : ∀ α : LayerSite N → G,
          ∏ Q ∈ C, (colDensC ρ u u' Q α) ^ (doubledPattern C P Q)
            = ∏ Q ∈ C,
              (colDensC ρ u u' Q α) ^ (if Q = P then 2 else 1) :=
        fun α => Finset.prod_congr rfl fun Q hQ => by
          by_cases hQP : Q = P <;> simp [doubledPattern, hQP, hQ]
      rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
      exact integral_colDens_prod_quadruple_doubled ρ μG hN hN3
        hρcont u u' C hC P hP
    rw [hmult, hint]
  have hsurj : ∀ k ∈ (Finset.piAntidiag Finset.univ 5).filter
        (fun k => suppOf k = C),
      ∃ P, ∃ _ : P ∈ C, doubledPattern C P = k := by
    intro k hk
    have hk5 : ∑ Q ∈ Finset.univ, k Q = 5 :=
      (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
    have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
    have hge : ∀ Q ∈ C, 1 ≤ k Q := by
      intro Q hQ
      have hQs : Q ∈ suppOf k := hsupp ▸ hQ
      exact Nat.one_le_iff_ne_zero.mpr
        (Finset.mem_filter.mp hQs).2
    have hsumC : ∑ Q ∈ C, k Q = 5 := by
      rw [← hsupp, ← sum_univ_eq_sum_suppOf]
      exact hk5
    have hm : ∑ Q ∈ C, (k Q - 1) = 1 := by
      have h1 : ∑ Q ∈ C, ((k Q - 1) + 1) = ∑ Q ∈ C, k Q :=
        Finset.sum_congr rfl fun Q hQ =>
          Nat.sub_add_cancel (hge Q hQ)
      rw [Finset.sum_add_distrib] at h1
      have hsc : ∑ Q ∈ C, (1 : ℕ) = 4 := by simp [hC]
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
      have hsumErase : ∑ Q ∈ C.erase P, k Q = 3 := by
        rw [Finset.sum_congr rfl hothers, Finset.sum_const,
          Finset.card_erase_of_mem hPC, hC]
        simp [nsmul_eq_mul]
      have hkP : k P = 2 := by
        have h := Finset.add_sum_erase C k hPC
        omega
      rw [hkP]
      simp [doubledPattern]
    · by_cases hQC : Q ∈ C
      · have hkQ : k Q = 1 := by
          by_contra hne
          have hQD : Q ∈ D := Finset.mem_filter.mpr ⟨hQC, hne⟩
          rw [hP] at hQD
          exact hQP (Finset.mem_singleton.mp hQD)
        rw [hkQ]
        simp [doubledPattern, hQP, hQC]
      · have hkQ : k Q = 0 := by
          by_contra hne
          have hQs : Q ∈ suppOf k := Finset.mem_filter.mpr
            ⟨Finset.mem_univ Q, hne⟩
          rw [hsupp] at hQs
          exact hQC hQs
        rw [hkQ]
        simp [doubledPattern, hQP, hQC]
  exact (Finset.sum_bij (fun P _ => doubledPattern C P)
    hmemPat
    (fun P hP P' hP' h => by
      by_contra hne
      have h2 := congrFun h P
      simp [doubledPattern, hne, hP] at h2)
    hsurj
    (fun P hP => (hvalPat P hP).symm)).symm

/-- **The card-1 fiber.** Over a 1-support `{P}`, the
fiber is the single pure-power exponent `5` at `P`;
multinomial coefficient `1`, value the fifth density
moment. -/
theorem fiber_card_one (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 1) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 5 := by
  classical
  obtain ⟨P, hPeq⟩ := Finset.card_eq_one.mp hC
  have hfib : (Finset.piAntidiag Finset.univ 5).filter
        (fun k => suppOf k = C)
      = {fun Q => if Q = P then 5 else 0} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ?_
    constructor
    · refine ⟨fun Q => if Q = P then 5 else 0, ?_⟩
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun Q _ => Finset.mem_univ Q⟩, ?_⟩
      · rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 5)]
        simp
      · refine Finset.ext fun Q => ?_
        simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
          true_and, hPeq, Finset.mem_singleton]
        by_cases hQ : Q = P <;> simp [hQ]
    · intro k hk
      have hk5 : ∑ Q ∈ Finset.univ, k Q = 5 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
      have hkP : k P = 5 := by
        have h1 : ∑ Q ∈ suppOf k, k Q = 5 := by
          rw [← sum_univ_eq_sum_suppOf]
          exact hk5
        rw [hsupp, hPeq, Finset.sum_singleton] at h1
        exact h1
      funext Q
      by_cases hQ : Q = P
      · rw [hQ, hkP]
        simp
      · have hk0 : k Q = 0 := by
          by_contra hne
          have hQs : Q ∈ suppOf k := Finset.mem_filter.mpr
            ⟨Finset.mem_univ Q, hne⟩
          rw [hsupp, hPeq, Finset.mem_singleton] at hQs
          exact hQ hQs
        rw [hk0]
        simp [hQ]
  rw [hfib, Finset.sum_singleton]
  have hmult : (Nat.multinomial Finset.univ
        (fun Q => if Q = P then 5 else 0) : ℝ) = 1 := by
    have hp : ∏ Q ∈ Finset.univ,
        Nat.factorial ((fun Q => if Q = P then 5 else 0) Q)
          = 120 := by
      have h1 : ∏ Q ∈ Finset.univ,
            Nat.factorial ((fun Q => if Q = P then 5 else 0) Q)
          = ∏ Q ∈ C,
            Nat.factorial ((fun Q => if Q = P then 5 else 0) Q) :=
        (Finset.prod_subset (Finset.subset_univ C)
          (fun Q _ hQ => by
            have hQP : Q ≠ P := by
              rw [hPeq, Finset.mem_singleton] at hQ
              exact hQ
            simp [hQP])).symm
      rw [h1, hPeq, Finset.prod_singleton]
      simp
      norm_num [Nat.factorial]
    have hk5 : ∑ Q ∈ Finset.univ,
        (fun Q => if Q = P then 5 else 0) Q = 5 := by
      rw [Finset.sum_ite_eq' Finset.univ P (fun _ => 5)]
      simp
    have h := multinomial_univ_eq
      (fun Q => if Q = P then 5 else 0) hk5 120 hp
      (by norm_num)
    rw [h]
    norm_num
  have hval : ∫ α : LayerSite N → G,
        ∏ Q ∈ Finset.univ,
          (colDensC ρ u u' Q α)
            ^ ((fun Q => if Q = P then 5 else 0) Q)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 5 := by
    have hsupp : suppOf (fun Q => if Q = P then 5 else 0)
        = C := by
      refine Finset.ext fun Q => ?_
      simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
        true_and, hPeq, Finset.mem_singleton]
      by_cases hQ : Q = P <;> simp [hQ]
    rw [integral_colDens_prod_pow_univ ρ μG hρcont u u'
      (fun Q => if Q = P then 5 else 0), hsupp,
      integral_colDens_prod_pow_of_card_le_three ρ μG hN hN3
        hρcont u u' C (by omega)
        (fun Q => if Q = P then 5 else 0),
      hPeq, Finset.prod_singleton]
    simp
  rw [hmult, hval, one_mul]

/-- **The card-2 fiber.** Over a 2-support `{P, Q}`,
the fiber is the four exponent splits `(a, 5−a)`,
`a = 1..4` (parametrized by the ordered pair
`(k P, k Q)`); the fiber sum evaluates to
`5·A₁A₄ + 10·A₂A₃ + 10·A₃A₂ + 5·A₄A₁`. -/
theorem fiber_card_two (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 2) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 5 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4)
        + 10 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3)
        + 10 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2)
        + 5 * (densMomentValue ρ μG 4 * densMomentValue ρ μG 1) := by
  classical
  obtain ⟨P, Q, hPQ, hCeq⟩ := Finset.card_eq_two.mp hC
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 4 ×ˢ Finset.Icc 1 4).filter
      (fun t => t.1 + t.2 = 5) with hS
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (120
            / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ) : ℝ))
          * (densMomentValue ρ μG t.1
            * densMomentValue ρ μG t.2) := by
    refine (Finset.sum_bij
      (fun t _ => fun X => if X = P then t.1
        else if X = Q then t.2 else 0) ?_ ?_ ?_ ?_).symm
    · intro t ht
      have htS : t.1 + t.2 = 5
          ∧ t.1 ∈ Finset.Icc 1 4 ∧ t.2 ∈ Finset.Icc 1 4 :=
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
        simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
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
      have hk5 : ∑ X ∈ Finset.univ, k X = 5 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 5 := by
        rw [← hsupp, ← sum_univ_eq_sum_suppOf]
        exact hk5
      have hge : ∀ X ∈ C, 1 ≤ k X := by
        intro X hX
        have hXs : X ∈ suppOf k := hsupp ▸ hX
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
              have hXs : X ∈ suppOf k := Finset.mem_filter.mpr
                ⟨Finset.mem_univ X, hne⟩
              rw [hsupp, hCeq, Finset.mem_insert,
                Finset.mem_singleton] at hXs
              exact hXs.elim (fun h => hXP h) (fun h => hXQ h)
            rw [hk0]
            simp [hXP, hXQ]
    · intro t ht
      have htS : t.1 + t.2 = 5
          ∧ t.1 ∈ Finset.Icc 1 4 ∧ t.2 ∈ Finset.Icc 1 4 :=
        ⟨(Finset.mem_filter.mp ht).2,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1,
          (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2⟩
      have hsum : ∑ X ∈ Finset.univ,
          (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) X = 5 := by
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
          = 120 / ((Nat.factorial t.1 * Nat.factorial t.2 : ℕ)
            : ℝ) :=
        multinomial_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : suppOf (fun X => if X = P then t.1
            else if X = Q then t.2 else 0) = C := by
        have ht1 : 1 ≤ t.1 := (Finset.mem_Icc.mp htS.2.1).1
        have ht2 : 1 ≤ t.2 := (Finset.mem_Icc.mp htS.2.2).1
        refine Finset.ext fun X => ?_
        simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
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
        rw [integral_colDens_prod_pow_univ ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_of_card_le_three ρ μG hN hN3
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
  have hSeq : S = {(1, 4), (2, 3), (3, 2), (4, 1)} := by
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
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring

/-- **The card-3 fiber.** Over a 3-support
`{P, Q, R}`, the fiber is the six positive exponent
triples summing to `5` (parametrized by
`(k P, k Q, k R)`); the fiber sum evaluates to the
`(3,1,1)` terms at coefficient `20` and the `(2,2,1)`
terms at coefficient `30`. -/
theorem fiber_card_three (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 3) :
    ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = 20 * (densMomentValue ρ μG 3
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
        + 20 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
        + 20 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
        + 30 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
        + 30 * (densMomentValue ρ μG 2
          * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
        + 30 * (densMomentValue ρ μG 1
          * (densMomentValue ρ μG 2 * densMomentValue ρ μG 2)) := by
  classical
  obtain ⟨P, Q, R, hPQ, hPR, hQR, hCeq⟩ :=
    Finset.card_eq_three.mp hC
  set S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 3 ×ˢ Finset.Icc 1 3 ×ˢ Finset.Icc 1 3).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 5) with hS
  have hnotP : P ∉ ({Q, R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hPQ, hPR⟩
  have hnotQ : Q ∉ ({R} : Finset (LayerColumn N)) := by
    rw [Finset.mem_singleton]
    exact hQR
  have hbij : ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ X ∈ Finset.univ, (colDensC ρ u u' X α) ^ (k X)
              ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ t ∈ S, (120
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
      have htS : t.1 + t.2.1 + t.2.2 = 5
          ∧ t.1 ∈ Finset.Icc 1 3 ∧ t.2.1 ∈ Finset.Icc 1 3
          ∧ t.2.2 ∈ Finset.Icc 1 3 :=
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
        simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
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
      have hk5 : ∑ X ∈ Finset.univ, k X = 5 :=
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1
      have hsupp : suppOf k = C := (Finset.mem_filter.mp hk).2
      have hsumC : ∑ X ∈ C, k X = 5 := by
        rw [← hsupp, ← sum_univ_eq_sum_suppOf]
        exact hk5
      have hge : ∀ X ∈ C, 1 ≤ k X := by
        intro X hX
        have hXs : X ∈ suppOf k := hsupp ▸ hX
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
      have hkP3 : k P ≤ 3 := by omega
      have hkQ3 : k Q ≤ 3 := by omega
      have hkR3 : k R ≤ 3 := by omega
      have hsumC' : k P + k Q + k R = 5 := by omega
      refine ⟨(k P, k Q, k R), ?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_product,
          Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          Finset.mem_Icc]
        exact ⟨⟨⟨hkP1, hkP3⟩, ⟨hkQ1, hkQ3⟩, ⟨hkR1, hkR3⟩⟩,
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
                have hXs : X ∈ suppOf k := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ X, hne⟩
                rw [hsupp, hCeq, Finset.mem_insert,
                  Finset.mem_insert, Finset.mem_singleton]
                  at hXs
                exact hXs.elim hXP
                  (fun h => h.elim hXQ hXR)
              rw [hk0]
              simp [hXP, hXQ, hXR]
    · intro t ht
      have htS : t.1 + t.2.1 + t.2.2 = 5
          ∧ t.1 ∈ Finset.Icc 1 3 ∧ t.2.1 ∈ Finset.Icc 1 3
          ∧ t.2.2 ∈ Finset.Icc 1 3 :=
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
            else if X = R then t.2.2 else 0) X = 5 := by
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
          = 120 / ((Nat.factorial t.1 * Nat.factorial t.2.1
              * Nat.factorial t.2.2 : ℕ) : ℝ) :=
        multinomial_univ_eq _ hsum _ hfact
          (by positivity)
      have hsupp : suppOf (fun X => if X = P then t.1
            else if X = Q then t.2.1
            else if X = R then t.2.2 else 0) = C := by
        refine Finset.ext fun X => ?_
        simp only [suppOf, Finset.mem_filter, Finset.mem_univ,
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
        rw [integral_colDens_prod_pow_univ ρ μG hρcont u u' _,
          hsupp,
          integral_colDens_prod_pow_of_card_le_three ρ μG hN hN3
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
  have hSeq : S = {(3, 1, 1), (1, 3, 1), (1, 1, 3),
      (2, 2, 1), (2, 1, 2), (1, 2, 2)} := by
    refine Finset.ext fun t => ?_
    obtain ⟨a, b, c⟩ := t
    simp only [hS, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hSeq]
  rw [Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_singleton]
  norm_num [Nat.factorial]
  ring

/-- **Powerset sums split by card.** A sum over the
powerset whose terms vanish at cards `0` and `≥ 6`
is the sum over cards `0..5`. -/
theorem sum_powerset_eq_sum_cards (F : Finset (LayerColumn N) → ℝ)
    (hF : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 6 ≤ C.card → F C = 0) :
    ∑ C ∈ Finset.univ.powerset, F C
      = ∑ j ∈ Finset.range 6,
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
  by_cases hM : Fintype.card (LayerColumn N) + 1 ≤ 6
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
      (fun j _ hj6 => ?_)).symm
    simp only [Finset.mem_range, not_lt] at hj6
    refine Finset.sum_eq_zero fun C hC => ?_
    exact hF C (Or.inr (by
      have hCj := (Finset.mem_powersetCard.mp hC).2
      omega))

/-- **The five-support erasure double count.**
`∑_{C₅} ∑_{x ∈ C₅} Excess₄(C₅.erase x) = (M − 4)·Φ`:
swap the sums, erase at the fixed column (a bijection
from 5-supports containing `x` to 4-supports avoiding
`x`), swap back, and count the `M − 4` complements. -/
theorem sum_powersetCard_five_erase_excess (hN : Even N)
    (hN3 : 3 ≤ N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 5, ∑ x ∈ C,
        (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
      = (colCount N - 4) * ∑ T ∈ Finset.univ.powersetCard 4,
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
  classical
  have step1 : ∀ C ∈ Finset.univ.powersetCard 5,
      ∑ x ∈ C, (quadReMoment ρ μG (C.erase x) u u'
          - (e1 ρ μG) ^ 4)
        = ∑ x ∈ Finset.univ, (if x ∈ C then
            (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
          else 0) := fun C _ =>
    (Finset.sum_congr rfl (fun x hx => (if_pos hx).symm)).trans
      (Finset.sum_subset (Finset.subset_univ C)
        (fun x _ hx => if_neg hx))
  have step2 : ∀ x : LayerColumn N,
      ∑ C ∈ Finset.univ.powersetCard 5, (if x ∈ C then
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        else 0)
      = ∑ T ∈ Finset.univ.powersetCard 4, (if x ∈ T then 0
          else (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)) := by
    intro x
    have hA : ∑ C ∈ Finset.univ.powersetCard 5, (if x ∈ C then
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4)
        else 0)
      = ∑ C ∈ (Finset.univ.powersetCard 5).filter
          (fun C => x ∈ C),
          (quadReMoment ρ μG (C.erase x) u u' - (e1 ρ μG) ^ 4) :=
      (Finset.sum_filter _ _).symm
    have hB : ∑ T ∈ Finset.univ.powersetCard 4, (if x ∈ T then 0
          else (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
      = ∑ T ∈ (Finset.univ.powersetCard 4).filter
          (fun T => x ∉ T),
          (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
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
      ∑ x ∈ Finset.univ, (if x ∈ T then (0 : ℝ)
          else (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        = (colCount N - 4)
          * (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4) := by
    intro T hT
    have hT4 : T.card = 4 := (Finset.mem_powersetCard.mp hT).2
    have h4M : 4 ≤ Fintype.card (LayerColumn N) := by
      have hle := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, hT4] at hle
    have hform : ∀ x : LayerColumn N,
        (if x ∈ T then (0 : ℝ)
          else (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4))
        = (if x ∉ T then
            (quadReMoment ρ μG T u u' - (e1 ρ μG) ^ 4)
          else 0) := fun x => (ite_not _ _ _).symm
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

/-- **The total fifth moment, assembled.** The
integrated multinomial expansion, grouped by support
card: cards `1, 2, 3` give exactly `kappa5Const`'s
low patterns (through the falling-factorial choose
identities); card `4` gives the `(2,1,1,1)` baseline
term, `480·d⁻⁴·Φ`, and the channel excess at
`−60·d⁻⁵`; card `5` gives the fully-split baseline
term and the dressing `120·(M−4)·B·d⁻⁴·Φ`. -/
theorem betaCoeff5_total (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 5
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = kappa5Const (N := N) ρ μG
        + (480 + 120 * (colCount N - 4)
            * (1 - e1 ρ μG / (d : ℝ))) * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ primitiveQuads (N := N),
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 60 * ((d : ℝ)⁻¹) ^ 5
          * kappa5chanExcess ρ μG u u' := by
  classical
  have hch2 : ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ))
      = colCount N * (colCount N - 1) / 2 := by
    have h := cast_factorial_mul_choose (N := N) 2
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
    have h := cast_factorial_mul_choose (N := N) 3
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
    have h := cast_factorial_mul_choose (N := N) 4
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
    have h := cast_factorial_mul_choose (N := N) 5
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
  have hG0 : ∑ C ∈ Finset.univ.powersetCard 0,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = 0 := by
    rw [Finset.powersetCard_zero, Finset.sum_singleton,
      fiber_eq_empty_of_card_ne ∅ (Or.inl Finset.card_empty),
      Finset.sum_empty]
  have hG1 : ∑ C ∈ Finset.univ.powersetCard 1,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = colCount N * densMomentValue ρ μG 5 := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_one ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Nat.choose_one_right, nsmul_eq_mul]
    rfl
  have hG2 : ∑ C ∈ Finset.univ.powersetCard 2,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 2 : ℝ))
        * (5 * (densMomentValue ρ μG 1 * densMomentValue ρ μG 4)
          + 10 * (densMomentValue ρ μG 2 * densMomentValue ρ μG 3)
          + 10 * (densMomentValue ρ μG 3 * densMomentValue ρ μG 2)
          + 5 * (densMomentValue ρ μG 4
            * densMomentValue ρ μG 1)) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_two ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hG3 : ∑ C ∈ Finset.univ.powersetCard 3,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 3 : ℝ))
        * (20 * (densMomentValue ρ μG 3
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 1))
          + 20 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 3 * densMomentValue ρ μG 1))
          + 20 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 3))
          + 30 * (densMomentValue ρ μG 2
            * (densMomentValue ρ μG 2 * densMomentValue ρ μG 1))
          + 30 * (densMomentValue ρ μG 2
            * (densMomentValue ρ μG 1 * densMomentValue ρ μG 2))
          + 30 * (densMomentValue ρ μG 1
            * (densMomentValue ρ μG 2
              * densMomentValue ρ μG 2))) := by
    rw [Finset.sum_congr rfl (fun C hC =>
        fiber_card_three ρ μG hN hN3 hρcont u u' C
          (Finset.mem_powersetCard.mp hC).2),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul]
  have hC4 : ∀ C ∈ Finset.univ.powersetCard 4,
      (∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG))
      = 60 * (4 * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
          + 8 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
        - 60 * ((d : ℝ)⁻¹) ^ 5
          * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
    intro C hC
    rw [fiber_card_four ρ μG hN hN3 hρcont u u' C
      (Finset.mem_powersetCard.mp hC).2, ← Finset.mul_sum]
    have hsum : ∑ P ∈ C, (densMomentValue ρ μG 2
          * (1 - e1 ρ μG / (d : ℝ)) ^ 3
          + 2 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
          - ((d : ℝ)⁻¹) ^ 5
            * (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3))
        = 4 * (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
            + 2 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
          - ((d : ℝ)⁻¹) ^ 5
            * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
              - realMoment ρ μG 2 * (e1 ρ μG) ^ 3) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        (Finset.mem_powersetCard.mp hC).2, nsmul_eq_mul,
        Nat.cast_ofNat]
    rw [hsum]
    ring
  have hG4 : ∑ C ∈ Finset.univ.powersetCard 4,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
          * (240 * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
        + 480 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
        - 60 * ((d : ℝ)⁻¹) ^ 5
          * kappa5chanExcess ρ μG u u' := by
    have hX : ∑ C ∈ Finset.univ.powersetCard 4,
        60 * (4 * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
          + 8 * ((d : ℝ)⁻¹) ^ 4
            * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
      = ((Nat.choose (Fintype.card (LayerColumn N)) 4 : ℝ))
          * (240 * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
        + 480 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ Finset.univ.powersetCard 4,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
      have hdist : ∀ C ∈ Finset.univ.powersetCard 4,
          60 * (4 * (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 3)
            + 8 * ((d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))
          = 60 * (4 * (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 3))
            + (480 * ((d : ℝ)⁻¹) ^ 4)
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) :=
        fun C _ => by ring
      rw [Finset.sum_congr rfl hdist,
        Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
    have hY : ∑ C ∈ Finset.univ.powersetCard 4,
        60 * ((d : ℝ)⁻¹) ^ 5
          * ∑ P ∈ C, (doubledQuadReMoment ρ μG C P u u'
            - realMoment ρ μG 2 * (e1 ρ μG) ^ 3)
      = 60 * ((d : ℝ)⁻¹) ^ 5
          * kappa5chanExcess ρ μG u u' := by
      rw [← Finset.mul_sum,
        sum_powersetCard_four_doubled_excess ρ μG hN hN3 hρcont
          u u']
    rw [Finset.sum_congr rfl hC4, Finset.sum_sub_distrib, hX, hY]
  have hG5 : ∑ C ∈ Finset.univ.powersetCard 5,
        ∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG)
      = ((Nat.choose (Fintype.card (LayerColumn N)) 5 : ℝ))
          * (120 * (1 - e1 ρ μG / (d : ℝ)) ^ 5)
        + 120 * (1 - e1 ρ μG / (d : ℝ)) * ((d : ℝ)⁻¹) ^ 4
          * ((colCount N - 4)
            * ∑ C ∈ Finset.univ.powersetCard 4,
              (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)) := by
    have hC5 : ∀ C ∈ Finset.univ.powersetCard 5,
        (∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
            (fun k => suppOf k = C),
          ((Nat.multinomial Finset.univ k : ℝ))
            * ∫ α : LayerSite N → G,
                ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
                ∂(Measure.pi fun _ : LayerSite N => μG))
        = 120 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
          + 120 * (1 - e1 ρ μG / (d : ℝ)) * ((d : ℝ)⁻¹) ^ 4
            * ∑ x ∈ C, (quadReMoment ρ μG (C.erase x) u u'
              - (e1 ρ μG) ^ 4) := by
      intro C hC
      rw [fiber_card_five ρ μG hN hN3 hρcont u u' C
        (Finset.mem_powersetCard.mp hC).2]
      ring
    rw [Finset.sum_congr rfl hC5, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum,
      sum_powersetCard_five_erase_excess ρ μG hN hN3 hρcont u u']
  have hFibVanish : ∀ C : Finset (LayerColumn N),
      C.card = 0 ∨ 6 ≤ C.card →
      (∑ k ∈ (Finset.piAntidiag Finset.univ 5).filter
          (fun k => suppOf k = C),
        ((Nat.multinomial Finset.univ k : ℝ))
          * ∫ α : LayerSite N → G,
              ∏ P ∈ Finset.univ, (colDensC ρ u u' P α) ^ (k P)
              ∂(Measure.pi fun _ : LayerSite N => μG)) = 0 := by
    intro C hC
    rw [fiber_eq_empty_of_card_ne C hC, Finset.sum_empty]
  rw [integral_layerDensSum_pow_five ρ μG hN hρcont u u',
    sum_piAntidiag_fiberwise,
    sum_powerset_eq_sum_cards _ hFibVanish]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hG0, hG1, hG2, hG3, hG4, hG5,
    sum_powersetCard_four_eq_primitive ρ μG hN hN3 hρcont u u']
  unfold kappa5Const
  rw [hch2, hch3, hch4, hch5, densMomentValue_one]
  ring

/-- **B5-2 headline: the κ₅^dep assembly identity.**
At general `(G, ρ)`, even `N`, `3 ≤ N`:

`kappa5dep = (4 + (M − 4)·B) · kappa4dep
            − (d⁻⁵/2) · kappa5chanExcess`,

`B = 1 − e₁/d`, `M = colCount N`. Every term is
accounted: the constant parts are exactly
`kappa5Const`'s seven patterns; the card-`4` fiber
dresses `kappa4dep` by the extension factor
`(4 + (M−4)·B)` — `4` from the four doubled
patterns at each primitive quad itself, `(M−4)·B`
from the quintuple fibers over its `M − 4`
extensions; the surviving non-factored part is the
channel excess at `−d⁻⁵/2` (the `1/2` is
`60/120`: the doubled pattern's multinomial weight
over the fifth power's). The naive expectation
`kappa5dep = kappa5chan2111` is FALSE as stated —
the channel sum differs by the baseline
(`kappa5chanExcess_eq`) and the identity carries
the order-4 dressing term; both discrepancies are
named here, not smoothed. NO sign is asserted:
the sign of `kappa5dep` remains FRONTIER. -/
theorem kappa5dep_eq (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa5dep ρ μG u u'
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa4dep ρ μG u u'
        - ((d : ℝ)⁻¹) ^ 5 / 2 * kappa5chanExcess ρ μG u u' := by
  have hβ : betaCoeff5 ρ μG u u'
      = (∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 5
          ∂(Measure.pi fun _ : LayerSite N => μG)) / 120 := by
    have hcong : (∫ α : LayerSite N → G,
          (layerDensSum ρ α u u') ^ 5 / 120
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
          (120 : ℝ)⁻¹ * (layerDensSum ρ α u u') ^ 5
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with α
      rw [div_eq_inv_mul]
    show betaCoeff5 ρ μG u u' = _
    unfold betaCoeff5
    rw [hcong, integral_const_mul, div_eq_inv_mul]
  rw [kappa5dep_def, hβ,
    betaCoeff5_total ρ μG hN hN3 hρcont u u',
    kappa4dep_eq ρ μG hN hN3 hρcont u u']
  ring

/-- **Diagonal corollary.** On the diagonal
`u' = u` — the form B5-PROBE evaluated at its two
seats (`N = 4` only, channel form): `kappa5dep` on
the diagonal is the dressed order-4 term minus
half the channel excess at `d⁻⁵`. The probe's
identification fence is discharged by this
statement together with `kappa5chanExcess_eq`
(channel excess versus the raw channel sum). -/
theorem kappa5dep_diag (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u : LayerLink N → G) :
    kappa5dep ρ μG u u
      = (4 + (colCount N - 4) * (1 - e1 ρ μG / (d : ℝ)))
          * kappa4dep ρ μG u u
        - ((d : ℝ)⁻¹) ^ 5 / 2 * kappa5chanExcess ρ μG u u :=
  kappa5dep_eq ρ μG hN hN3 hρcont u u

end Assembly5

#print axioms kappa5dep_eq


end ThetLogos
