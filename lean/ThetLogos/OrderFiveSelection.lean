/-
# ThetLogos.OrderFiveSelection — B5-0: the order-5 selection rule

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Pure
Finset/graph combinatorics on owned types
(`LayerColumn N`, `colSites`, `siteDegree`,
`quadSupport`); no analysis, no integrals. This module
defines **no** order-5 coefficient — `betaCoeff5` /
`kappa5dep` are B5-1's objects, not built here — and it
asserts **no sign** for anything. It proves the
combinatorial selection rule that the β⁵ scoping
(`scoping-beta5-2026-10-28.md` §4) registered as a
claim-to-check: at (Even `N`, `3 ≤ N`) the
`(1,1,1,1,1)` channel is empty and the only fully
shared 5-configuration is a primitive quad with one
column doubled. Dials 0/4, unchanged.

**The mechanism.** The layer site graph is bipartite:
sites carry a parity (the coordinate sum read in
`ZMod 2`, well-defined since `2 ∣ N`), and the two
sites of any column have opposite parity. Counting
column endpoints on each parity class separately
(the balance identities of the counting section)
gives, for any fully shared configuration of total
column count `5`: each parity class of the support
has at most two sites (twice the class size is at
most the total degree on that side, which is `5`),
while the columns inject into (even site, odd site)
pairs (a column is determined by its two sites at
`3 ≤ N`, `colSites_eq_imp`). Five columns into at
most `2 × 2 = 4` pairs: contradiction for five
distinct columns; for a multiplicity function the
same bounds force the distinct support to be a
primitive quad carrying multiplicity pattern
`(2,1,1,1)`.
-/

import ThetLogos.PrimitiveQuadPatterns

open Finset

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## Parity of a layer site -/

/-- The parity cast `ZMod N →+* ZMod 2`, from `2 ∣ N`. -/
noncomputable def parityCast (hN : Even N) : ZMod N →+* ZMod 2 :=
  ZMod.castHom (even_iff_two_dvd.mp hN) (ZMod 2)

/-- The parity of a layer site: the sum of its
coordinates read in `ZMod 2`. The time coordinate
contributes `0` (it vanishes on a layer site), so this
is the parity of the spatial coordinate sum. -/
noncomputable def siteParity (hN : Even N) (s : LayerSite N) : ZMod 2 :=
  ∑ j : Fin 4, parityCast hN (s.1 j)

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  exact h x

/-- A shift flips the parity: the shifted site's
coordinate at the shift direction gains `1`, all
others are unchanged, and `1 ≠ 0` in `ZMod 2`. -/
theorem siteParity_layerShift (hN : Even N) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    siteParity hN (layerShift ν hν c) = siteParity hN c + 1 := by
  classical
  have hsum : (∑ j : Fin 4,
      parityCast hN ((Pi.single ν (1 : ZMod N) : Fin 4 → ZMod N) j)) = 1 := by
    rw [Finset.sum_eq_single ν]
    · rw [Pi.single_eq_same, RingHom.map_one]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, RingHom.map_zero]
    · intro h
      exact absurd (Finset.mem_univ ν) h
  have hstep : ∀ j : Fin 4,
      parityCast hN ((layerShift ν hν c).1 j)
        = parityCast hN ((Pi.single ν (1 : ZMod N) : Fin 4 → ZMod N) j)
          + parityCast hN (c.1 j) := by
    intro j
    rw [layerShift_coe, torusShift_apply_coord, RingHom.map_add]
  unfold siteParity
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib, hsum]
  exact add_comm _ _

/-- The two sites of a column have opposite parity. -/
theorem siteParity_head_ne (hN : Even N) (P : LayerColumn N) :
    siteParity hN (layerShift P.2.1 P.2.2 P.1) ≠ siteParity hN P.1 := by
  rw [siteParity_layerShift]
  intro h
  have h2 : siteParity hN P.1 + 1 = siteParity hN P.1 + 0 := by rwa [add_zero]
  exact one_ne_zero (add_left_cancel h2)

/-- Exactly one of a column's two sites has parity
`0`: the cases for the base site. -/
theorem colSites_parity_cases (hN : Even N) (P : LayerColumn N) :
    (siteParity hN P.1 = 0 ∧ siteParity hN (layerShift P.2.1 P.2.2 P.1) ≠ 0)
    ∨ (siteParity hN P.1 ≠ 0 ∧ siteParity hN (layerShift P.2.1 P.2.2 P.1) = 0) := by
  have hne := siteParity_head_ne hN P
  rcases zmod_two_eq_zero_or_one (siteParity hN P.1) with h0 | h1
  · exact Or.inl ⟨h0, fun hb => hne (hb.trans h0.symm)⟩
  · rcases zmod_two_eq_zero_or_one
      (siteParity hN (layerShift P.2.1 P.2.2 P.1)) with g0 | g1
    · exact Or.inr ⟨fun hb => zero_ne_one (hb.symm.trans h1), g0⟩
    · exact absurd (g1.trans h1.symm) hne

/-- Each parity class contains exactly one of a
column's two sites. -/
theorem colSites_filter_parity_cards (hN : Even N) (P : LayerColumn N) :
    ((colSites P).filter (fun s => siteParity hN s = 0)).card = 1 ∧
    ((colSites P).filter (fun s => siteParity hN s ≠ 0)).card = 1 := by
  classical
  have hpair : colSites P = {P.1, layerShift P.2.1 P.2.2 P.1} := rfl
  rcases colSites_parity_cases hN P with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · constructor
    · have hf : (colSites P).filter (fun s => siteParity hN s = 0) = {P.1} := by
        rw [hpair]
        simp only [Finset.filter_insert, Finset.filter_singleton]
        simp [h0, h1]
      rw [hf, Finset.card_singleton]
    · have hf : (colSites P).filter (fun s => siteParity hN s ≠ 0)
          = {layerShift P.2.1 P.2.2 P.1} := by
        rw [hpair]
        simp only [Finset.filter_insert, Finset.filter_singleton]
        simp [h0, h1]
      rw [hf, Finset.card_singleton]
  · constructor
    · have hf : (colSites P).filter (fun s => siteParity hN s = 0)
          = {layerShift P.2.1 P.2.2 P.1} := by
        rw [hpair]
        simp only [Finset.filter_insert, Finset.filter_singleton]
        simp [h0, h1]
      rw [hf, Finset.card_singleton]
    · have hf : (colSites P).filter (fun s => siteParity hN s ≠ 0) = {P.1} := by
        rw [hpair]
        simp only [Finset.filter_insert, Finset.filter_singleton]
        simp [h0, h1]
      rw [hf, Finset.card_singleton]

/-! ## Counting: the balance identities and the pair injection -/

/-- **Double counting over one side.** For any site
predicate `q` met by exactly one site of every
column, the degrees over the `q`-side of the support
sum to the number of columns: each column contributes
exactly one endpoint to that side. -/
theorem sum_siteDegree_filter_eq_card (C : Finset (LayerColumn N))
    {q : LayerSite N → Prop} [DecidablePred q]
    (hq : ∀ P : LayerColumn N, ((colSites P).filter q).card = 1) :
    ∑ s ∈ (quadSupport C).filter q, siteDegree C s = C.card := by
  have hdeg : ∀ s : LayerSite N, siteDegree C s
      = (C.filter fun P => s ∈ colSites P).card := fun s => rfl
  calc ∑ s ∈ (quadSupport C).filter q, siteDegree C s
      = ∑ s ∈ (quadSupport C).filter q,
          ∑ P ∈ C, (if s ∈ colSites P then 1 else 0) :=
        Finset.sum_congr rfl fun s _ => by rw [hdeg s, Finset.card_filter]
    _ = ∑ P ∈ C, ∑ s ∈ (quadSupport C).filter q,
          (if s ∈ colSites P then 1 else 0) := Finset.sum_comm
    _ = ∑ P ∈ C, ((colSites P).filter q).card := by
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [← Finset.card_filter]
        congr 1
        ext s
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨-, hqs⟩, hsP⟩
          exact ⟨hsP, hqs⟩
        · rintro ⟨hsP, hqs⟩
          exact ⟨⟨Finset.mem_biUnion.mpr ⟨P, hP, hsP⟩, hqs⟩, hsP⟩
    _ = ∑ _P ∈ C, (1 : ℕ) :=
        Finset.sum_congr rfl fun P _ => hq P
    _ = C.card := by simp

/-- Balance on the even side: the degrees over the
even support sites sum to the number of columns. -/
theorem sum_siteDegree_even_eq (hN : Even N) (C : Finset (LayerColumn N)) :
    ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s = 0),
      siteDegree C s = C.card :=
  sum_siteDegree_filter_eq_card C
    (fun P => (colSites_filter_parity_cards hN P).1)

/-- Balance on the odd side: the degrees over the
odd support sites sum to the number of columns. -/
theorem sum_siteDegree_odd_eq (hN : Even N) (C : Finset (LayerColumn N)) :
    ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s ≠ 0),
      siteDegree C s = C.card :=
  sum_siteDegree_filter_eq_card C
    (fun P => (colSites_filter_parity_cards hN P).2)

/-- A column read as an ordered pair of sites: its
even site first, its odd site second. -/
noncomputable def parityPair (hN : Even N) (P : LayerColumn N) :
    LayerSite N × LayerSite N :=
  if siteParity hN P.1 = 0 then (P.1, layerShift P.2.1 P.2.2 P.1)
  else (layerShift P.2.1 P.2.2 P.1, P.1)

/-- The ordered pair forgets to the column's two
sites. -/
theorem parityPair_pair (hN : Even N) (P : LayerColumn N) :
    ({(parityPair hN P).1, (parityPair hN P).2} : Finset (LayerSite N))
      = colSites P := by
  classical
  by_cases h : siteParity hN P.1 = 0
  · have hf : parityPair hN P = (P.1, layerShift P.2.1 P.2.2 P.1) := if_pos h
    rw [hf]
    rfl
  · have hf : parityPair hN P = (layerShift P.2.1 P.2.2 P.1, P.1) := if_neg h
    rw [hf]
    exact Finset.pair_comm _ _

/-- **The pair injection.** The columns of `C`
inject into (even support site, odd support site)
pairs — the ordered pair determines the column,
since at `3 ≤ N` a column is determined by its two
sites (`colSites_eq_imp`). -/
theorem card_le_even_mul_odd (hN : Even N) (hN3 : 3 ≤ N)
    (C : Finset (LayerColumn N)) :
    C.card ≤ ((quadSupport C).filter (fun s => siteParity hN s = 0)).card *
      ((quadSupport C).filter (fun s => siteParity hN s ≠ 0)).card := by
  classical
  have hmaps : ∀ P ∈ C, parityPair hN P ∈
      (quadSupport C).filter (fun s => siteParity hN s = 0) ×ˢ
        (quadSupport C).filter (fun s => siteParity hN s ≠ 0) := by
    intro P hP
    have hbase : P.1 ∈ quadSupport C :=
      Finset.mem_biUnion.mpr ⟨P, hP, mem_colSites.mpr (Or.inl rfl)⟩
    have hhead : layerShift P.2.1 P.2.2 P.1 ∈ quadSupport C :=
      Finset.mem_biUnion.mpr ⟨P, hP, mem_colSites.mpr (Or.inr rfl)⟩
    rw [Finset.mem_product]
    rcases colSites_parity_cases hN P with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hf : parityPair hN P = (P.1, layerShift P.2.1 P.2.2 P.1) := if_pos h0
      rw [hf]
      exact ⟨Finset.mem_filter.mpr ⟨hbase, h0⟩,
        Finset.mem_filter.mpr ⟨hhead, h1⟩⟩
    · have hf : parityPair hN P = (layerShift P.2.1 P.2.2 P.1, P.1) := if_neg h0
      rw [hf]
      exact ⟨Finset.mem_filter.mpr ⟨hhead, h1⟩,
        Finset.mem_filter.mpr ⟨hbase, h0⟩⟩
  have hinj : Set.InjOn (parityPair hN) C := by
    intro P _ Q _ hf
    have hcol : colSites P = colSites Q := by
      rw [← parityPair_pair hN P, ← parityPair_pair hN Q]
      have h1 : (parityPair hN P).1 = (parityPair hN Q).1 := congrArg Prod.fst hf
      have h2 : (parityPair hN P).2 = (parityPair hN Q).2 := congrArg Prod.snd hf
      rw [h1, h2]
    exact colSites_eq_imp hN hN3 hcol
  calc C.card ≤ (((quadSupport C).filter (fun s => siteParity hN s = 0)) ×ˢ
        ((quadSupport C).filter (fun s => siteParity hN s ≠ 0))).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ((quadSupport C).filter (fun s => siteParity hN s = 0)).card *
        ((quadSupport C).filter (fun s => siteParity hN s ≠ 0)).card :=
      Finset.card_product _ _

/-! ## Claim 1: no primitive 5-support -/

/-- The sharing property (every site of every column
is read by another column) forces every support site
to have degree at least `2`. -/
theorem two_le_siteDegree_of_sharing {C : Finset (LayerColumn N)}
    (hshare : ∀ P ∈ C, ∀ s ∈ colSites P,
      ∃ Q ∈ C, Q ≠ P ∧ s ∈ colSites Q)
    {s : LayerSite N} (hs : s ∈ quadSupport C) : 2 ≤ siteDegree C s := by
  obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨Q, hQ, hQP, hsQ⟩ := hshare P hP s hsP
  have hsub : ({P, Q} : Finset (LayerColumn N)) ⊆
      C.filter (fun P => s ∈ colSites P) := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rw [Finset.mem_filter]
    rcases hR with rfl | rfl
    · exact ⟨hP, hsP⟩
    · exact ⟨hQ, hsQ⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_pair (fun hh => hQP hh.symm)] at h
  exact h

/-- **No primitive 5-support.** At (Even `N`,
`3 ≤ N`) there is no set of five distinct columns
whose every support site has degree at least `2`:
the balance identities put at most two even and two
odd sites in the support, and the pair injection
then leaves room for at most four columns. This is
the death of the `(1,1,1,1,1)` channel. -/
theorem no_primitive_five_support (hN : Even N) (hN3 : 3 ≤ N)
    (C : Finset (LayerColumn N)) (hC : C.card = 5)
    (hdeg : ∀ s ∈ quadSupport C, 2 ≤ siteDegree C s) : False := by
  classical
  have hEven : ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s = 0),
      siteDegree C s = 5 := by rw [sum_siteDegree_even_eq hN C, hC]
  have hOdd : ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s ≠ 0),
      siteDegree C s = 5 := by rw [sum_siteDegree_odd_eq hN C, hC]
  have hEvenBound : 2 * ((quadSupport C).filter
        (fun s => siteParity hN s = 0)).card ≤ 5 := by
    have h1 : (∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s = 0),
          (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s = 0),
          siteDegree C s :=
      Finset.sum_le_sum fun s hs => hdeg s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have hOddBound : 2 * ((quadSupport C).filter
        (fun s => siteParity hN s ≠ 0)).card ≤ 5 := by
    have h1 : (∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s ≠ 0),
          (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport C).filter (fun s => siteParity hN s ≠ 0),
          siteDegree C s :=
      Finset.sum_le_sum fun s hs => hdeg s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have hinj := card_le_even_mul_odd hN hN3 C
  rw [hC] at hinj
  have hprod : ((quadSupport C).filter (fun s => siteParity hN s = 0)).card *
      ((quadSupport C).filter (fun s => siteParity hN s ≠ 0)).card ≤ 4 := by
    have h := Nat.mul_le_mul
      (show ((quadSupport C).filter (fun s => siteParity hN s = 0)).card ≤ 2
        by omega)
      (show ((quadSupport C).filter (fun s => siteParity hN s ≠ 0)).card ≤ 2
        by omega)
    omega
  omega

/-- **No primitive 5-support, sharing form.** The
order-5 generalization of `IsPrimitiveQuad`'s
condition at card `5` is uninhabited: no five
distinct columns have every site of every column
shared with another column of the set. -/
theorem no_primitive_five_support_sharing (hN : Even N) (hN3 : 3 ≤ N)
    (C : Finset (LayerColumn N)) (hC : C.card = 5)
    (hshare : ∀ P ∈ C, ∀ s ∈ colSites P,
      ∃ Q ∈ C, Q ≠ P ∧ s ∈ colSites Q) : False :=
  no_primitive_five_support hN hN3 C hC
    (fun s hs => two_le_siteDegree_of_sharing hshare hs)

/-! ## Claim 2: the `(2,1,1,1)` channel -/

/-- The degree of a site counted with multiplicity:
the total multiplicity of the columns through `s`. -/
noncomputable def wSiteDegree (m : LayerColumn N → ℕ) (s : LayerSite N) : ℕ :=
  ∑ P ∈ Finset.univ.filter (fun P => s ∈ colSites P), m P

/-- **Weighted double counting over one side.** For
a multiplicity function `m` supported in `S` and any
site predicate `q` met by exactly one site of every
column, the weighted degrees over the `q`-side of
the support of `S` sum to the total multiplicity
over `S`: each column contributes its multiplicity
once to that side. -/
theorem sum_wSiteDegree_filter_eq (m : LayerColumn N → ℕ)
    (S : Finset (LayerColumn N))
    (hmS : ∀ P : LayerColumn N, m P ≠ 0 → P ∈ S)
    {q : LayerSite N → Prop} [DecidablePred q]
    (hq : ∀ P : LayerColumn N, ((colSites P).filter q).card = 1) :
    ∑ s ∈ (quadSupport S).filter q, wSiteDegree m s = ∑ P ∈ S, m P := by
  have hw : ∀ s : LayerSite N, wSiteDegree m s
      = ∑ P : LayerColumn N, (if s ∈ colSites P then m P else 0) :=
    fun s => Finset.sum_filter _ _
  have hcard : ∀ P ∈ S,
      ((quadSupport S).filter q).filter (fun s => s ∈ colSites P)
        = (colSites P).filter q := by
    intro P hP
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hqs⟩, hsP⟩
      exact ⟨hsP, hqs⟩
    · rintro ⟨hsP, hqs⟩
      exact ⟨⟨Finset.mem_biUnion.mpr ⟨P, hP, hsP⟩, hqs⟩, hsP⟩
  calc ∑ s ∈ (quadSupport S).filter q, wSiteDegree m s
      = ∑ s ∈ (quadSupport S).filter q,
          ∑ P : LayerColumn N, (if s ∈ colSites P then m P else 0) :=
        Finset.sum_congr rfl fun s _ => hw s
    _ = ∑ P : LayerColumn N, ∑ s ∈ (quadSupport S).filter q,
          (if s ∈ colSites P then m P else 0) := Finset.sum_comm
    _ = ∑ P : LayerColumn N,
          m P * (((quadSupport S).filter q).filter
            (fun s => s ∈ colSites P)).card := by
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Nat.cast_id, Nat.mul_comm]
    _ = ∑ P ∈ S, m P * (((quadSupport S).filter q).filter
          (fun s => s ∈ colSites P)).card := by
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intro P _ hP
        have hmP : m P = 0 := by
          by_contra hne
          exact hP (hmS P hne)
        rw [hmP, Nat.zero_mul]
    _ = ∑ P ∈ S, m P := by
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hcard P hP, hq P, Nat.mul_one]

/-- Arithmetic squeeze: two numbers, each at most
`2`, with sum at most `3`, have product at most `2`. -/
theorem mul_le_two_of_sum_le_three {x y : ℕ} (hx : x ≤ 2) (hy : y ≤ 2)
    (hxy : x + y ≤ 3) : x * y ≤ 2 := by
  interval_cases x <;> interval_cases y <;> omega

/-- Arithmetic squeeze: two numbers, each at most
`2`, with sum at most `2`, have product at most `1`. -/
theorem mul_le_one_of_sum_le_two {x y : ℕ} (hx : x ≤ 2) (hy : y ≤ 2)
    (hxy : x + y ≤ 2) : x * y ≤ 1 := by
  interval_cases x <;> interval_cases y <;> omega

/-- **The `(2,1,1,1)` channel characterization.**
Let `m` be a multiplicity function on columns with
total multiplicity `5`, fully shared: every column
of positive multiplicity has both of its sites read
by another column of positive multiplicity. Then at
(Even `N`, `3 ≤ N`) the distinct support of `m` is
a primitive quad, and the multiplicity pattern is
exactly `(2,1,1,1)`: one column doubled, the other
three single. Together with `no_primitive_five_support`
this says a fully shared 5-configuration has no
other channel. -/
theorem five_column_channel_characterization (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm5 : ∑ P, m P = 5)
    (hshare : ∀ P : LayerColumn N, m P ≠ 0 →
      ∀ s ∈ colSites P, ∃ Q ≠ P, m Q ≠ 0 ∧ s ∈ colSites Q) :
    IsPrimitiveQuad (Finset.univ.filter (fun P => m P ≠ 0)) ∧
    ∃ P₀ ∈ Finset.univ.filter (fun P => m P ≠ 0), m P₀ = 2 ∧
      ∀ P ∈ Finset.univ.filter (fun P => m P ≠ 0), P ≠ P₀ → m P = 1 := by
  classical
  set S : Finset (LayerColumn N) :=
    Finset.univ.filter (fun P => m P ≠ 0) with hSdef
  have hmemS : ∀ P : LayerColumn N, P ∈ S ↔ m P ≠ 0 := fun P => by
    simp [hSdef]
  have hsumS : ∑ P ∈ S, m P = 5 := by
    rw [← hm5]
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro P _ hP
    by_contra hne
    exact hP ((hmemS P).mpr hne)
  have hshareS : ∀ P ∈ S, ∀ s ∈ colSites P,
      ∃ Q ∈ S, Q ≠ P ∧ s ∈ colSites Q := by
    intro P hP s hsP
    obtain ⟨Q, hQne, hmQ, hsQ⟩ := hshare P ((hmemS P).mp hP) s hsP
    exact ⟨Q, (hmemS Q).mpr hmQ, hQne, hsQ⟩
  have hdegS : ∀ s ∈ quadSupport S, 2 ≤ siteDegree S s :=
    fun s hs => two_le_siteDegree_of_sharing hshareS hs
  have hwdegS : ∀ s ∈ quadSupport S, 2 ≤ wSiteDegree m s := by
    intro s hs
    obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨Q, hQne, hmQ, hsQ⟩ := hshare P ((hmemS P).mp hP) s hsP
    have hPQ : ({P, Q} : Finset (LayerColumn N)) ⊆
        Finset.univ.filter (fun R => s ∈ colSites R) := by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rw [Finset.mem_filter]
      rcases hR with rfl | rfl
      · exact ⟨Finset.mem_univ _, hsP⟩
      · exact ⟨Finset.mem_univ _, hsQ⟩
    have hle : ∑ R ∈ ({P, Q} : Finset (LayerColumn N)), m R
        ≤ wSiteDegree m s :=
      Finset.sum_le_sum_of_subset_of_nonneg hPQ
        (fun R _ _ => Nat.zero_le _)
    rw [Finset.sum_pair (Ne.symm hQne)] at hle
    have hmP : m P ≠ 0 := (hmemS P).mp hP
    omega
  have hEvenW : ∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0),
      wSiteDegree m s = 5 :=
    (sum_wSiteDegree_filter_eq m S
      (fun P hPne => (hmemS P).mpr hPne)
      (fun P => (colSites_filter_parity_cards hN P).1)).trans hsumS
  have hOddW : ∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0),
      wSiteDegree m s = 5 :=
    (sum_wSiteDegree_filter_eq m S
      (fun P hPne => (hmemS P).mpr hPne)
      (fun P => (colSites_filter_parity_cards hN P).2)).trans hsumS
  have hEvenBound : 2 * ((quadSupport S).filter
        (fun s => siteParity hN s = 0)).card ≤ 5 := by
    have h1 : (∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0),
          (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0),
          wSiteDegree m s :=
      Finset.sum_le_sum fun s hs => hwdegS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have hOddBound : 2 * ((quadSupport S).filter
        (fun s => siteParity hN s ≠ 0)).card ≤ 5 := by
    have h1 : (∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0),
          (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0),
          wSiteDegree m s :=
      Finset.sum_le_sum fun s hs => hwdegS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have hinjS := card_le_even_mul_odd hN hN3 S
  have hdegSum : ∑ s ∈ quadSupport S, siteDegree S s = 2 * S.card := by
    have h1 := sum_siteDegree_even_eq hN S
    have h2 := sum_siteDegree_odd_eq hN S
    have h3 : (∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0),
          siteDegree S s)
        + (∑ s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0),
          siteDegree S s)
        = ∑ s ∈ quadSupport S, siteDegree S s :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    omega
  have hsupp_le : (quadSupport S).card ≤ S.card := by
    have h1 : (∑ s ∈ quadSupport S, (2 : ℕ))
        ≤ ∑ s ∈ quadSupport S, siteDegree S s :=
      Finset.sum_le_sum fun s hs => hdegS s hs
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at h1
    omega
  have hXY : ((quadSupport S).filter (fun s => siteParity hN s = 0)).card
      + ((quadSupport S).filter (fun s => siteParity hN s ≠ 0)).card
      = (quadSupport S).card :=
    Finset.card_filter_add_card_filter_not _
  have hkle : S.card ≤ 4 := by
    have h := Nat.mul_le_mul
      (show ((quadSupport S).filter (fun s => siteParity hN s = 0)).card ≤ 2
        by omega)
      (show ((quadSupport S).filter (fun s => siteParity hN s ≠ 0)).card ≤ 2
        by omega)
    omega
  have hk4 : S.card = 4 := by
    by_contra hne
    have hk3 : S.card ≤ 3 := by omega
    have hsupp3 : (quadSupport S).card ≤ 3 := le_trans hsupp_le hk3
    have hk2 : S.card ≤ 2 :=
      le_trans hinjS
        (mul_le_two_of_sum_le_three (by omega) (by omega) (by omega))
    have hsupp2 : (quadSupport S).card ≤ 2 := le_trans hsupp_le hk2
    have hk1 : S.card ≤ 1 :=
      le_trans hinjS
        (mul_le_one_of_sum_le_two (by omega) (by omega) (by omega))
    obtain ⟨P, hP⟩ : ∃ P, P ∈ S := by
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ P ∈ S, m P = 0 :=
        Finset.sum_eq_zero fun P hP => absurd hP (hcon P)
      omega
    have hall : ∀ Q ∈ S, Q = P := by
      intro Q hQ
      by_contra hne2
      have hsub : ({P, Q} : Finset (LayerColumn N)) ⊆ S := by
        intro R hR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hR
        rcases hR with rfl | rfl
        · exact hP
        · exact hQ
      have h := Finset.card_le_card hsub
      rw [Finset.card_pair (fun hh => hne2 hh.symm)] at h
      omega
    have hdeg1 : siteDegree S P.1 = 1 := by
      have hfil : S.filter (fun R => P.1 ∈ colSites R) = {P} := by
        ext R
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hRS, -⟩
          exact hall R hRS
        · intro hR
          rw [hR]
          exact ⟨hP, mem_colSites.mpr (Or.inl rfl)⟩
      show (S.filter (fun R => P.1 ∈ colSites R)).card = 1
      rw [hfil, Finset.card_singleton]
    have hP1supp : P.1 ∈ quadSupport S :=
      Finset.mem_biUnion.mpr ⟨P, hP, mem_colSites.mpr (Or.inl rfl)⟩
    have hge := hdegS P.1 hP1supp
    omega
  obtain ⟨P₀, hP₀S, hP₀2⟩ : ∃ P₀ ∈ S, 2 ≤ m P₀ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ P ∈ S, m P ≤ ∑ _P ∈ S, (1 : ℕ) :=
      Finset.sum_le_sum fun P hP => by
        have h2 := hcon P hP
        omega
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hk4] at h1
    omega
  have hrest : ∀ P ∈ S, P ≠ P₀ → m P = 1 := by
    intro P hP hne
    have hcardEE : ((S.erase P).erase P₀).card = 2 := by
      rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm hne, hP₀S⟩),
        Finset.card_erase_of_mem hP, hk4]
    have hsumEE : 2 ≤ ∑ R ∈ (S.erase P).erase P₀, m R := by
      have h1 : (∑ _R ∈ (S.erase P).erase P₀, (1 : ℕ))
          ≤ ∑ R ∈ (S.erase P).erase P₀, m R :=
        Finset.sum_le_sum fun R hR => by
          have hRS : R ∈ S :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
          have hmR : m R ≠ 0 := (hmemS R).mp hRS
          omega
      rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hcardEE] at h1
    have hsumE : m P₀ + ∑ R ∈ (S.erase P).erase P₀, m R
        = ∑ R ∈ S.erase P, m R :=
      Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hne, hP₀S⟩)
    have htot : m P + ∑ R ∈ S.erase P, m R = 5 := by
      rw [← hsumS]
      exact Finset.add_sum_erase _ _ hP
    have hmP : m P ≠ 0 := (hmemS P).mp hP
    omega
  have hP₀eq : m P₀ = 2 := by
    have hsumRest : ∑ R ∈ S.erase P₀, m R = 3 := by
      have hcardE : (S.erase P₀).card = 3 := by
        rw [Finset.card_erase_of_mem hP₀S, hk4]
      calc ∑ R ∈ S.erase P₀, m R = ∑ _R ∈ S.erase P₀, (1 : ℕ) :=
            Finset.sum_congr rfl fun R hR =>
              hrest R (Finset.mem_erase.mp hR).2 (Finset.mem_erase.mp hR).1
        _ = 3 := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hcardE,
              Nat.mul_one]
    have htot : m P₀ + ∑ R ∈ S.erase P₀, m R = 5 := by
      rw [← hsumS]
      exact Finset.add_sum_erase _ _ hP₀S
    omega
  exact ⟨⟨hk4, hshareS⟩, P₀, hP₀S, hP₀eq, hrest⟩

/-- **Multiplicity cap.** In a fully shared
5-configuration no column appears three or more
times: every multiplicity is at most `2`. -/
theorem five_column_multiplicity_le_two (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm5 : ∑ P, m P = 5)
    (hshare : ∀ P : LayerColumn N, m P ≠ 0 →
      ∀ s ∈ colSites P, ∃ Q ≠ P, m Q ≠ 0 ∧ s ∈ colSites Q)
    (P : LayerColumn N) : m P ≤ 2 := by
  obtain ⟨-, P₀, hP₀S, hP₀eq, hrest⟩ :=
    five_column_channel_characterization hN hN3 m hm5 hshare
  by_cases hP : P ∈ Finset.univ.filter (fun P => m P ≠ 0)
  · rcases eq_or_ne P P₀ with rfl | hne
    · rw [hP₀eq]
    · have h1 : m P = 1 := hrest P hP hne
      omega
  · have hmP : m P = 0 := by
      by_contra hne
      exact hP (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hne⟩)
    omega

end ThetLogos
