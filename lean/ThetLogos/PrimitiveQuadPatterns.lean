/-
# ThetLogos.PrimitiveQuadPatterns — PQ-0: the pattern split of
the primitive quads

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Pure
Finset/graph combinatorics on owned types
(`LayerColumn N`, `colSites`); no analysis, no integrals.
This brick evaluates nothing — it sorts the primitive
quads of `PlaneCrossingBeta4` by their sharing pattern,
and records the orientation split data at each site that
the later evaluation bricks (PW-4/PW-5) consume. Dials
0/4, unchanged.

**What a pattern is here.** A primitive quad `C` has 4
columns and 8 site slots. The degree of a site is the
number of columns of `C` incident to it; primitivity
forces every support site to have degree `≥ 2`, and no
site has degree `> 4`. The four pattern predicates below
are degree data over the support, with the `(2,2,2,2)`
case split by the existence of a digon pair (two distinct
columns over the same unordered site pair). At each site
the orientation record is the split `(plain, conjugated)`:
columns based at the site contribute a plain factor of
their word there, columns headed at the site a conjugated
one (`PlaneCrossingBeta2.colWord`).

**Correction to the scoping picture, landed at full
rank.** The scoping (`scoping-pw3-fs-2026-10-27.md` §2)
priced the four types — `C4`, `digon ⊔ digon`, `(3,3,2)`,
`(4,2,2)` — as the live possibilities, with parallel
multiplicity `≤ 2` "since the sites determine the
direction". Checking against the owned objects sharpens
this: multiplicity `≤ 2` holds at every even `N`
(`colSites_fiber_card_le_two` below), but at `3 ≤ N` the
landed `colSites_eq_imp` (a column is determined by its
two sites) forces multiplicity `≤ 1` — a reverse column
over the same site pair exists only when `N ∣ 2`. Hence
at the assembly's `N` (`Even`, `3 ≤ N`) the types
`digon ⊔ digon`, `(3,3,2)`, `(4,2,2)` are **uninhabited**
and every primitive quad is a `C4`
(`primitive_pattern_eq_C4`). The four-pattern partition
itself (`primitive_pattern_partition`) is proved at
general even `N`, where all four types are live, and the
hub orientation facts are proved conditionally on the
patterns: in a `(4,2,2)` quad the hub carries split
`(2,2)`; in a `(3,3,2)` quad the degree-3 sites carry
`(2,1)`/`(1,2)` and the degree-2 site one of
`(2,0)`, `(1,1)`, `(0,2)`; in a `C4` a site carries
`(2,0)` iff every incident column is based there (a
source of the cycle orientation, at the level of the
split data), `(0,2)` iff every incident column is headed
there (a sink), and `(1,1)` otherwise. The `N = 4` wrap
check is §Wrap: the partition's proof uses no `5 ≤ N`
hypothesis anywhere, and a straight-wrap `C4` at `N = 4`
is exhibited.
-/

import ThetLogos.PlaneCrossingBeta4

open Finset

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## Definitions -/

/-- The support of a finite set of columns: the sites
read by at least one of its columns. -/
noncomputable def quadSupport (C : Finset (LayerColumn N)) : Finset (LayerSite N) :=
  C.biUnion colSites

/-- The degree of a site in a set of columns: the number
of columns of `C` incident to `s`. -/
noncomputable def siteDegree (C : Finset (LayerColumn N)) (s : LayerSite N) : ℕ :=
  (C.filter fun P => s ∈ colSites P).card

/-- The orientation record at a site: `(plain, conjugated)`
— the number of columns of `C` based at `s` (plain factor
of the column word at `s`) and the number whose head is
`s` (conjugated factor). -/
noncomputable def siteSplit (C : Finset (LayerColumn N)) (s : LayerSite N) : ℕ × ℕ :=
  ((C.filter fun P => P.1 = s).card,
   (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s).card)

/-- A digon pair: two distinct columns over the same
unordered site pair (each the reverse of the other). -/
def IsDigonPair (P Q : LayerColumn N) : Prop :=
  P ≠ Q ∧ colSites P = colSites Q

/-- The `(2,2,2,2)` degree pattern: four support sites,
each of degree `2`. -/
def HasPattern2222 (C : Finset (LayerColumn N)) : Prop :=
  (quadSupport C).card = 4 ∧ ∀ s ∈ quadSupport C, siteDegree C s = 2

/-- The `C4` pattern: degree pattern `(2,2,2,2)` with no
digon pair — the sharing multigraph is a single 4-cycle. -/
def HasPatternC4 (C : Finset (LayerColumn N)) : Prop :=
  HasPattern2222 C ∧ ¬ ∃ P ∈ C, ∃ Q ∈ C, IsDigonPair P Q

/-- The `digon ⊔ digon` pattern: degree pattern
`(2,2,2,2)` containing a digon pair (the remaining two
columns are then forced to be a second digon pair over
the complementary two sites). -/
def HasPatternDigonDigon (C : Finset (LayerColumn N)) : Prop :=
  HasPattern2222 C ∧ ∃ P ∈ C, ∃ Q ∈ C, IsDigonPair P Q

/-- The `(3,3,2)` degree pattern: three support sites of
degrees `3, 3, 2` in some order. -/
def HasPattern332 (C : Finset (LayerColumn N)) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ quadSupport C = {a, b, c}
    ∧ siteDegree C a = 3 ∧ siteDegree C b = 3 ∧ siteDegree C c = 2

/-- The `(4,2,2)` degree pattern: three support sites of
degrees `4, 2, 2` in some order (the degree-`4` site is
the hub). -/
def HasPattern422 (C : Finset (LayerColumn N)) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ quadSupport C = {a, b, c}
    ∧ siteDegree C a = 4 ∧ siteDegree C b = 2 ∧ siteDegree C c = 2


/-! ## Degree basics -/

/-- A column reads exactly two sites (its base and its
head, which differ at even `N`). -/
theorem card_colSites_two (hN : Even N) (P : LayerColumn N) :
    (colSites P).card = 2 := by
  have h : colSites P = {P.1, layerShift P.2.1 P.2.2 P.1} := rfl
  rw [h, Finset.card_pair]
  exact Ne.symm (layerShift_ne_self hN P.2.1 P.2.2 P.1)

/-- No site has degree above the number of columns. -/
theorem siteDegree_le_four {C : Finset (LayerColumn N)} (hC : C.card = 4)
    (s : LayerSite N) : siteDegree C s ≤ 4 := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun P => s ∈ colSites P) C)
  rwa [hC] at h

/-- Primitivity: every support site has degree at least
`2` — each of its sites is shared with another column. -/
theorem two_le_siteDegree {C : Finset (LayerColumn N)}
    (hC : IsPrimitiveQuad C) {s : LayerSite N}
    (hs : s ∈ quadSupport C) : 2 ≤ siteDegree C s := by
  have hs' : s ∈ C.biUnion colSites := hs
  obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs'
  obtain ⟨Q, hQ, hQP, hsQ⟩ := hC.2 P hP s hsP
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

/-- Double counting: the degrees over the support sum
to `8` — four columns, two sites each. -/
theorem sum_siteDegree_eq (hN : Even N) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) :
    ∑ s ∈ quadSupport C, siteDegree C s = 8 := by
  have hswap : ((quadSupport C).sigma
        (fun s => C.filter fun P => s ∈ colSites P)).card
      = (C.sigma colSites).card := by
    apply Finset.card_bij (fun x _ => ⟨x.2, x.1⟩)
    · intro x hx
      rw [Finset.mem_sigma] at hx ⊢
      have hx2 := Finset.mem_filter.mp hx.2
      exact ⟨hx2.1, hx2.2⟩
    · intro a₁ _ a₂ _ h
      obtain ⟨s₁, P₁⟩ := a₁
      obtain ⟨s₂, P₂⟩ := a₂
      obtain ⟨hf, hs⟩ := Sigma.ext_iff.mp h
      have hs' : s₁ = s₂ := eq_of_heq hs
      subst hf
      subst hs'
      rfl
    · intro b hb
      rw [Finset.mem_sigma] at hb
      have hb1 : b.2 ∈ C.biUnion colSites :=
        Finset.mem_biUnion.mpr ⟨b.1, hb.1, hb.2⟩
      exact ⟨⟨b.2, b.1⟩,
        Finset.mem_sigma.mpr ⟨hb1, Finset.mem_filter.mpr ⟨hb.1, hb.2⟩⟩,
        Sigma.eta b⟩
  have hI1 : (C.sigma colSites).card = 8 := by
    rw [Finset.card_sigma]
    have h2 : ∑ P ∈ C, (colSites P).card = ∑ _P ∈ C, (2 : ℕ) :=
      Finset.sum_congr rfl fun P _ => card_colSites_two hN P
    rw [h2, Finset.sum_const, hC, nsmul_eq_mul, Nat.cast_id]
    decide
  have hI2 : ((quadSupport C).sigma
        (fun s => C.filter fun P => s ∈ colSites P)).card
      = ∑ s ∈ quadSupport C, siteDegree C s := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl fun s _ => rfl
  omega

/-- The support of a primitive quad has at most four
sites: `2 · card ≤ ∑ degrees = 8`. -/
theorem quadSupport_card_le_four (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C) :
    (quadSupport C).card ≤ 4 := by
  have h1 : ∑ s ∈ quadSupport C, (2 : ℕ)
      ≤ ∑ s ∈ quadSupport C, siteDegree C s :=
    Finset.sum_le_sum fun s hs => two_le_siteDegree hC hs
  rw [sum_siteDegree_eq hN hC.1, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at h1
  omega

/-- The support of a primitive quad has at least two
sites: `∑ degrees = 8 ≤ 4 · card`. -/
theorem quadSupport_card_ge_two (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C) :
    2 ≤ (quadSupport C).card := by
  have h1 : ∑ s ∈ quadSupport C, siteDegree C s
      ≤ ∑ s ∈ quadSupport C, (4 : ℕ) :=
    Finset.sum_le_sum fun s _ => siteDegree_le_four hC.1 s
  rw [sum_siteDegree_eq hN hC.1, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at h1
  omega

/-! ## Parallel multiplicity and digon pairs -/

/-- **Parallel multiplicity ≤ 2.** At most two columns
of any set share the same pair of sites: the base map is
injective on a `colSites` fiber, since a base and a site
pair determine the head, and the sites determine the
direction (`layerShift_inj_dir`). -/
theorem colSites_fiber_card_le_two (hN : Even N)
    (C : Finset (LayerColumn N)) (t : Finset (LayerSite N)) :
    (C.filter fun P => colSites P = t).card ≤ 2 := by
  classical
  by_cases hempty : (C.filter fun P => colSites P = t) = ∅
  · simp [hempty]
  · obtain ⟨P₀, hP₀⟩ := Finset.nonempty_of_ne_empty hempty
    rw [Finset.mem_filter] at hP₀
    have ht2 : t.card = 2 := by
      rw [← hP₀.2]
      exact card_colSites_two hN P₀
    have hle := Finset.card_le_card_of_injOn (fun P : LayerColumn N => P.1)
      (s := C.filter fun P => colSites P = t) (t := t)
      (by
        intro P hP
        simp only [Finset.mem_coe, Finset.mem_filter] at hP
        rw [Finset.mem_coe, ← hP.2]
        exact mem_colSites.mpr (Or.inl rfl))
      (by
        intro P hP Q hQ hbase
        simp only [Finset.mem_coe, Finset.mem_filter] at hP hQ
        change P.1 = Q.1 at hbase
        have h1 : layerShift P.2.1 P.2.2 P.1 ∈ colSites P :=
          mem_colSites.mpr (Or.inr rfl)
        have h2 : layerShift P.2.1 P.2.2 P.1 ∈ colSites Q := by
          have hPQ : colSites P = colSites Q := hP.2.trans hQ.2.symm
          rwa [hPQ] at h1
        rw [mem_colSites] at h2
        have hhead : layerShift P.2.1 P.2.2 P.1
            = layerShift Q.2.1 Q.2.2 Q.1 := by
          rcases h2 with h2 | h2
          · exfalso
            apply layerShift_ne_self hN P.2.1 P.2.2 P.1
            rw [h2]
            exact hbase.symm
          · exact h2
        have hhead' : layerShift P.2.1 P.2.2 P.1
            = layerShift Q.2.1 Q.2.2 P.1 := by
          rwa [hbase.symm] at hhead
        exact Prod.ext hbase
          (Subtype.ext (layerShift_inj_dir hN P.2.2 Q.2.2 P.1 hhead')))
    exact ht2 ▸ hle

/-- At `3 ≤ N` the multiplicity drops to `≤ 1`: a column
is determined by its two sites (`colSites_eq_imp`), so
no digon pair exists at all. -/
theorem colSites_fiber_card_le_one (hN : Even N) (hN3 : 3 ≤ N)
    (C : Finset (LayerColumn N)) (t : Finset (LayerSite N)) :
    (C.filter fun P => colSites P = t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P hP Q hQ
  rw [Finset.mem_filter] at hP hQ
  exact colSites_eq_imp hN hN3 (hP.2.trans hQ.2.symm)

/-- In a digon pair, each column is based at the other's
head: the two columns are mutual reverses. -/
theorem digon_swap (hN : Even N) {P Q : LayerColumn N}
    (hPQ : P ≠ Q) (h : colSites P = colSites Q) :
    Q.1 = layerShift P.2.1 P.2.2 P.1 ∧
      P.1 = layerShift Q.2.1 Q.2.2 Q.1 := by
  have key : ∀ {P Q : LayerColumn N}, P ≠ Q →
      colSites P = colSites Q →
      Q.1 = layerShift P.2.1 P.2.2 P.1 := by
    intro P Q hPQ h
    have hmem : Q.1 ∈ colSites P := by
      rw [h]
      exact mem_colSites.mpr (Or.inl rfl)
    rw [mem_colSites] at hmem
    rcases hmem with hmem | hmem
    · exfalso
      apply hPQ
      have hmem2 : layerShift Q.2.1 Q.2.2 Q.1 ∈ colSites P := by
        rw [h]
        exact mem_colSites.mpr (Or.inr rfl)
      rw [mem_colSites] at hmem2
      have hne : layerShift Q.2.1 Q.2.2 Q.1 ≠ P.1 :=
        fun hh => layerShift_ne_self hN Q.2.1 Q.2.2 Q.1
          (hh.trans hmem.symm)
      have hhead : layerShift Q.2.1 Q.2.2 Q.1
          = layerShift P.2.1 P.2.2 P.1 := by
        rcases hmem2 with h2 | h2
        · exact absurd h2 hne
        · exact h2
      have hhead' : layerShift Q.2.1 Q.2.2 Q.1
          = layerShift P.2.1 P.2.2 Q.1 := by
        rwa [← hmem] at hhead
      exact Prod.ext hmem.symm
        (Subtype.ext
          (layerShift_inj_dir hN Q.2.2 P.2.2 Q.1 hhead').symm)
    · exact hmem
  exact ⟨key hPQ h, key (fun hh => hPQ hh.symm) h.symm⟩

/-! ## The `(4,4)` impossibility -/

/-- **No primitive quad has two degree-`4` sites** (the
`(4,4)` degree pattern is impossible): if two sites each
met all four columns, every column would lie over that
one site pair — four columns in a fiber of size at most
two. -/
theorem not_two_degree_four (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : C.card = 4)
    {a b : LayerSite N} (hab : a ≠ b)
    (ha : siteDegree C a = 4) (hb : siteDegree C b = 4) : False := by
  classical
  have incident_of_deg_four : ∀ {s : LayerSite N},
      siteDegree C s = 4 → ∀ P ∈ C, s ∈ colSites P := by
    intro s hs P hP
    have hF : (C.filter fun P => s ∈ colSites P) = C := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hC]
      exact hs.ge
    have hmem : P ∈ C.filter (fun P => s ∈ colSites P) := by
      rw [hF]
      exact hP
    exact (Finset.mem_filter.mp hmem).2
  have key : ∀ P ∈ C, colSites P = {a, b} := by
    intro P hP
    have hia : a ∈ colSites P := incident_of_deg_four ha P hP
    have hib : b ∈ colSites P := incident_of_deg_four hb P hP
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hia
      · exact hib
    · rw [card_colSites_two hN P, Finset.card_pair hab]
  have hsub : C ⊆ C.filter (fun P => colSites P = {a, b}) := by
    intro P hP
    exact Finset.mem_filter.mpr ⟨hP, key P hP⟩
  have hle := Finset.card_le_card hsub
  rw [hC] at hle
  have hfiber := colSites_fiber_card_le_two hN C {a, b}
  omega

/-- The support of a primitive quad never has exactly
two sites. -/
theorem quadSupport_card_ne_two (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C) :
    (quadSupport C).card ≠ 2 := by
  intro hk
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hk
  have hsum := sum_siteDegree_eq hN hC.1
  rw [hsupp, Finset.sum_pair hab] at hsum
  have ha4 : siteDegree C a ≤ 4 := siteDegree_le_four hC.1 a
  have hb4 : siteDegree C b ≤ 4 := siteDegree_le_four hC.1 b
  have ha : siteDegree C a = 4 := by omega
  have hb : siteDegree C b = 4 := by omega
  exact not_two_degree_four hN hC.1 hab ha hb

/-! ## Orientation splits -/

/-- The split at a site sums to the degree: every
incident column is based at the site or headed at it,
exclusively (base and head differ at even `N`). -/
theorem siteSplit_add (hN : Even N) (C : Finset (LayerColumn N))
    (s : LayerSite N) :
    (siteSplit C s).1 + (siteSplit C s).2 = siteDegree C s := by
  classical
  have hunion : (C.filter fun P => s ∈ colSites P)
      = (C.filter fun P => P.1 = s)
        ∪ (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_union, mem_colSites]
    constructor
    · rintro ⟨hC, hs | hs⟩
      · exact Or.inl ⟨hC, hs.symm⟩
      · exact Or.inr ⟨hC, hs.symm⟩
    · rintro (⟨hC, h⟩ | ⟨hC, h⟩)
      · exact ⟨hC, Or.inl h.symm⟩
      · exact ⟨hC, Or.inr h.symm⟩
  have hdisj : Disjoint (C.filter fun P => P.1 = s)
      (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s) := by
    rw [Finset.disjoint_left]
    intro P hP1 hP2
    rw [Finset.mem_filter] at hP1 hP2
    apply layerShift_ne_self hN P.2.1 P.2.2 P.1
    rw [hP2.2]
    exact hP1.2.symm
  have hdeg : siteDegree C s
      = (C.filter fun P => s ∈ colSites P).card := rfl
  rw [hdeg, hunion]
  exact (Finset.card_union_of_disjoint hdisj).symm

/-- The plain count at a support site is at most
`card (support) - 1`: the head map injects the columns
based at `s` into the remaining support sites (a base
and a head determine the column, by
`layerShift_inj_dir`). -/
theorem siteSplit_fst_le (hN : Even N) (C : Finset (LayerColumn N))
    {s : LayerSite N} (hs : s ∈ quadSupport C) :
    (siteSplit C s).1 ≤ (quadSupport C).card - 1 := by
  classical
  have hle := Finset.card_le_card_of_injOn
    (fun P : LayerColumn N => layerShift P.2.1 P.2.2 P.1)
    (s := C.filter fun P => P.1 = s) (t := (quadSupport C).erase s)
    (by
      intro P hP
      simp only [Finset.mem_coe, Finset.mem_filter] at hP
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · exact fun hh => layerShift_ne_self hN P.2.1 P.2.2 P.1
          (hh.trans hP.2.symm)
      · have hmem : layerShift P.2.1 P.2.2 P.1 ∈ colSites P :=
          mem_colSites.mpr (Or.inr rfl)
        exact Finset.subset_biUnion_of_mem colSites hP.1 hmem)
    (by
      intro P hP Q hQ hhead
      simp only [Finset.mem_coe, Finset.mem_filter] at hP hQ
      change layerShift P.2.1 P.2.2 P.1
        = layerShift Q.2.1 Q.2.2 Q.1 at hhead
      have hhead' : layerShift P.2.1 P.2.2 P.1
          = layerShift Q.2.1 Q.2.2 P.1 := by
        have e2 : layerShift Q.2.1 Q.2.2 Q.1
            = layerShift Q.2.1 Q.2.2 P.1 := by
          rw [hQ.2, ← hP.2]
        exact hhead.trans e2
      exact Prod.ext (hP.2.trans (hQ.2.symm))
        (Subtype.ext (layerShift_inj_dir hN P.2.2 Q.2.2 P.1 hhead')))
  have herase : ((quadSupport C).erase s).card
      = (quadSupport C).card - 1 := Finset.card_erase_of_mem hs
  rw [herase] at hle
  exact hle

/-- The conjugated count at a support site is at most
`card (support) - 1`: the base map injects the columns
headed at `s` into the remaining support sites. -/
theorem siteSplit_snd_le (hN : Even N) (C : Finset (LayerColumn N))
    {s : LayerSite N} (hs : s ∈ quadSupport C) :
    (siteSplit C s).2 ≤ (quadSupport C).card - 1 := by
  classical
  have hle := Finset.card_le_card_of_injOn
    (fun P : LayerColumn N => P.1)
    (s := C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s)
    (t := (quadSupport C).erase s)
    (by
      intro P hP
      simp only [Finset.mem_coe, Finset.mem_filter] at hP
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · exact fun hh => layerShift_ne_self hN P.2.1 P.2.2 P.1
          (hh.trans hP.2.symm).symm
      · have hmem : P.1 ∈ colSites P := mem_colSites.mpr (Or.inl rfl)
        exact Finset.subset_biUnion_of_mem colSites hP.1 hmem)
    (by
      intro P hP Q hQ hbase
      simp only [Finset.mem_coe, Finset.mem_filter] at hP hQ
      change P.1 = Q.1 at hbase
      have hhead : layerShift P.2.1 P.2.2 P.1
          = layerShift Q.2.1 Q.2.2 P.1 := by
        have e2 : layerShift Q.2.1 Q.2.2 Q.1
            = layerShift Q.2.1 Q.2.2 P.1 := by
          rw [hbase]
        exact hP.2.trans ((hQ.2.symm).trans e2)
      exact Prod.ext hbase
        (Subtype.ext (layerShift_inj_dir hN P.2.2 Q.2.2 P.1 hhead)))
  have herase : ((quadSupport C).erase s).card
      = (quadSupport C).card - 1 := Finset.card_erase_of_mem hs
  rw [herase] at hle
  exact hle

/-- A three-element support written as `{a, b, c}` with
distinct entries has card `3`. -/
theorem quadSupport_card_of_eq_insert3 {C : Finset (LayerColumn N)}
    {a b c : LayerSite N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupp : quadSupport C = {a, b, c}) : (quadSupport C).card = 3 := by
  have ha' : a ∉ ({b, c} : Finset (LayerSite N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have hb' : b ∉ ({c} : Finset (LayerSite N)) := by
    simp only [Finset.mem_singleton]
    exact hbc
  rw [hsupp, Finset.card_insert_of_notMem ha',
    Finset.card_insert_of_notMem hb', Finset.card_singleton]

/-- At a degree-`3` site in a three-site support, the
split is `(2, 1)` or `(1, 2)`: the split sums to `3` and
each part is at most `2` (the injection bounds). -/
theorem siteSplit_of_degree_three (hN : Even N)
    (C : Finset (LayerColumn N)) {s : LayerSite N}
    (hs : s ∈ quadSupport C) (hcard : (quadSupport C).card = 3)
    (hdeg : siteDegree C s = 3) :
    siteSplit C s = (2, 1) ∨ siteSplit C s = (1, 2) := by
  have hadd := siteSplit_add hN C s
  rw [hdeg] at hadd
  have h1 := siteSplit_fst_le hN C hs
  have h2 := siteSplit_snd_le hN C hs
  rw [hcard] at h1 h2
  have h3 : (siteSplit C s).1 = 2 ∧ (siteSplit C s).2 = 1
      ∨ (siteSplit C s).1 = 1 ∧ (siteSplit C s).2 = 2 := by omega
  rcases h3 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact Or.inl (Prod.ext h1' h2')
  · exact Or.inr (Prod.ext h1' h2')

/-- At a degree-`2` site the split is one of `(2, 0)`,
`(1, 1)`, `(0, 2)`: it sums to `2`. -/
theorem siteSplit_of_degree_two (hN : Even N)
    (C : Finset (LayerColumn N)) {s : LayerSite N}
    (hdeg : siteDegree C s = 2) :
    siteSplit C s = (2, 0) ∨ siteSplit C s = (1, 1)
      ∨ siteSplit C s = (0, 2) := by
  have hadd := siteSplit_add hN C s
  rw [hdeg] at hadd
  have h3 : (siteSplit C s).1 = 2 ∧ (siteSplit C s).2 = 0
      ∨ (siteSplit C s).1 = 1 ∧ (siteSplit C s).2 = 1
      ∨ (siteSplit C s).1 = 0 ∧ (siteSplit C s).2 = 2 := by omega
  rcases h3 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact Or.inl (Prod.ext h1' h2')
  · exact Or.inr (Or.inl (Prod.ext h1' h2'))
  · exact Or.inr (Or.inr (Prod.ext h1' h2'))

/-- **The `(4,2,2)` hub split.** In a `(4,2,2)` quad the
hub (the degree-`4` site) carries split `(2, 2)`: the
split sums to `4` over a three-site support, and each
part is at most `2` by the injection bounds. -/
theorem pattern422_hub_split (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : HasPattern422 C) :
    ∃ a ∈ quadSupport C, siteDegree C a = 4
      ∧ siteSplit C a = (2, 2) := by
  obtain ⟨a, b, c, hab, hac, hbc, hsupp, hda, -, -⟩ := hC
  have hcard : (quadSupport C).card = 3 :=
    quadSupport_card_of_eq_insert3 hab hac hbc hsupp
  have hs : a ∈ quadSupport C := by
    rw [hsupp]
    exact Finset.mem_insert_self a {b, c}
  refine ⟨a, hs, hda, ?_⟩
  have hadd := siteSplit_add hN C a
  rw [hda] at hadd
  have h1 := siteSplit_fst_le hN C hs
  have h2 := siteSplit_snd_le hN C hs
  rw [hcard] at h1 h2
  have h3 : (siteSplit C a).1 = 2 ∧ (siteSplit C a).2 = 2 := by omega
  exact Prod.ext h3.1 h3.2

/-- **The `(3,3,2)` splits.** In a `(3,3,2)` quad each
degree-`3` site carries split `(2, 1)` or `(1, 2)`
(which of the two is decided by whether the site's
single, non-digon incident column is based there or
headed there — read off the split itself), and the
degree-`2` site carries one of `(2, 0)`, `(1, 1)`,
`(0, 2)`. -/
theorem pattern332_splits (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : HasPattern332 C) :
    ∃ a b c, a ∈ quadSupport C ∧ b ∈ quadSupport C
      ∧ c ∈ quadSupport C ∧ siteDegree C a = 3
      ∧ siteDegree C b = 3 ∧ siteDegree C c = 2
      ∧ (siteSplit C a = (2, 1) ∨ siteSplit C a = (1, 2))
      ∧ (siteSplit C b = (2, 1) ∨ siteSplit C b = (1, 2))
      ∧ (siteSplit C c = (2, 0) ∨ siteSplit C c = (1, 1)
        ∨ siteSplit C c = (0, 2)) := by
  obtain ⟨a, b, c, hab, hac, hbc, hsupp, hda, hdb, hdc⟩ := hC
  have hcard : (quadSupport C).card = 3 :=
    quadSupport_card_of_eq_insert3 hab hac hbc hsupp
  have ha_mem : a ∈ quadSupport C := by
    rw [hsupp]
    exact Finset.mem_insert_self a {b, c}
  have hb_mem : b ∈ quadSupport C := by
    rw [hsupp]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self b {c})
  have hc_mem : c ∈ quadSupport C := by
    rw [hsupp]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
  exact ⟨a, b, c, ha_mem, hb_mem, hc_mem, hda, hdb, hdc,
    siteSplit_of_degree_three hN C ha_mem hcard hda,
    siteSplit_of_degree_three hN C hb_mem hcard hdb,
    siteSplit_of_degree_two hN C hdc⟩

/-- Split `(2, 0)` at a degree-`2` site iff every
incident column is based there — the site is a **source**
of the cycle orientation (at the level of the split
data). -/
theorem siteSplit_eq_two_zero_iff (hN : Even N)
    (C : Finset (LayerColumn N)) {s : LayerSite N}
    (hdeg : siteDegree C s = 2) :
    siteSplit C s = (2, 0) ↔
      ∀ P ∈ C, s ∈ colSites P → P.1 = s := by
  classical
  constructor
  · intro hsplit P hP hsP
    have hfst : (C.filter fun P => P.1 = s).card = 2 :=
      congrArg Prod.fst hsplit
    have hsub : (C.filter fun P => P.1 = s)
        ⊆ (C.filter fun P => s ∈ colSites P) := by
      intro R hR
      rw [Finset.mem_filter] at hR ⊢
      exact ⟨hR.1, mem_colSites.mpr (Or.inl hR.2.symm)⟩
    have hcardle : (C.filter fun P => s ∈ colSites P).card
        ≤ (C.filter fun P => P.1 = s).card := by
      have hle : siteDegree C s
          ≤ (C.filter fun P => P.1 = s).card := by
        rw [hfst]
        exact hdeg.le
      exact hle
    have hEq := Finset.eq_of_subset_of_card_le hsub hcardle
    have hmem : P ∈ C.filter (fun P => P.1 = s) := by
      rw [hEq]
      exact Finset.mem_filter.mpr ⟨hP, hsP⟩
    exact (Finset.mem_filter.mp hmem).2
  · intro hall
    have hsub : (C.filter fun P => s ∈ colSites P)
        ⊆ (C.filter fun P => P.1 = s) := by
      intro R hR
      rw [Finset.mem_filter] at hR ⊢
      exact ⟨hR.1, hall R hR.1 hR.2⟩
    have hle : siteDegree C s ≤ (C.filter fun P => P.1 = s).card :=
      Finset.card_le_card hsub
    rw [hdeg] at hle
    have hadd := siteSplit_add hN C s
    rw [hdeg] at hadd
    have hle' : 2 ≤ (siteSplit C s).1 := hle
    have h3 : (siteSplit C s).1 = 2 ∧ (siteSplit C s).2 = 0 := by omega
    exact Prod.ext h3.1 h3.2

/-- Split `(0, 2)` at a degree-`2` site iff every
incident column is headed there — the site is a **sink**
of the cycle orientation (at the level of the split
data). -/
theorem siteSplit_eq_zero_two_iff (hN : Even N)
    (C : Finset (LayerColumn N)) {s : LayerSite N}
    (hdeg : siteDegree C s = 2) :
    siteSplit C s = (0, 2) ↔
      ∀ P ∈ C, s ∈ colSites P →
        layerShift P.2.1 P.2.2 P.1 = s := by
  classical
  constructor
  · intro hsplit P hP hsP
    have hsnd : (C.filter fun P =>
        layerShift P.2.1 P.2.2 P.1 = s).card = 2 :=
      congrArg Prod.snd hsplit
    have hsub : (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s)
        ⊆ (C.filter fun P => s ∈ colSites P) := by
      intro R hR
      rw [Finset.mem_filter] at hR ⊢
      exact ⟨hR.1, mem_colSites.mpr (Or.inr hR.2.symm)⟩
    have hcardle : (C.filter fun P => s ∈ colSites P).card
        ≤ (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s).card := by
      have hle : siteDegree C s
          ≤ (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s).card := by
        rw [hsnd]
        exact hdeg.le
      exact hle
    have hEq := Finset.eq_of_subset_of_card_le hsub hcardle
    have hmem : P ∈ C.filter
        (fun P => layerShift P.2.1 P.2.2 P.1 = s) := by
      rw [hEq]
      exact Finset.mem_filter.mpr ⟨hP, hsP⟩
    exact (Finset.mem_filter.mp hmem).2
  · intro hall
    have hsub : (C.filter fun P => s ∈ colSites P)
        ⊆ (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s) := by
      intro R hR
      rw [Finset.mem_filter] at hR ⊢
      exact ⟨hR.1, hall R hR.1 hR.2⟩
    have hle : siteDegree C s
        ≤ (C.filter fun P => layerShift P.2.1 P.2.2 P.1 = s).card :=
      Finset.card_le_card hsub
    rw [hdeg] at hle
    have hadd := siteSplit_add hN C s
    rw [hdeg] at hadd
    have hle' : 2 ≤ (siteSplit C s).2 := hle
    have h3 : (siteSplit C s).1 = 0 ∧ (siteSplit C s).2 = 2 := by omega
    exact Prod.ext h3.1 h3.2

/-- **Orientation trichotomy in a `C4`** (the split data
PW-4/PW-5 consume): every site of a `C4` quad is a
source (split `(2, 0)`, all incident columns based
there), a sink (split `(0, 2)`, all incident columns
headed there), or mixed (split `(1, 1)`). Only the
consistently oriented cycle is all-mixed. -/
theorem patternC4_site_orientation (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : HasPatternC4 C)
    {s : LayerSite N} (hs : s ∈ quadSupport C) :
    (siteSplit C s = (2, 0) ∧ ∀ P ∈ C, s ∈ colSites P → P.1 = s)
      ∨ (siteSplit C s = (0, 2) ∧ ∀ P ∈ C, s ∈ colSites P →
          layerShift P.2.1 P.2.2 P.1 = s)
      ∨ siteSplit C s = (1, 1) := by
  have hdeg : siteDegree C s = 2 := hC.1.2 s hs
  rcases siteSplit_of_degree_two hN C hdeg with h | h | h
  · exact Or.inl ⟨h, (siteSplit_eq_two_zero_iff hN C hdeg).mp h⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨h, (siteSplit_eq_zero_two_iff hN C hdeg).mp h⟩)

/-! ## The pattern split -/

/-- If the support has four sites, every degree is `2`:
the degrees sum to `8` and each is at least `2`. -/
theorem siteDegree_eq_two_of_card_four (hN : Even N)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C)
    (hk : (quadSupport C).card = 4) {s : LayerSite N}
    (hs : s ∈ quadSupport C) : siteDegree C s = 2 := by
  have hsum := sum_siteDegree_eq hN hC.1
  have hsplit : ∑ t ∈ quadSupport C, siteDegree C t
      = siteDegree C s
        + ∑ t ∈ (quadSupport C).erase s, siteDegree C t :=
    (Finset.add_sum_erase _ _ hs).symm
  have hge : 6 ≤ ∑ t ∈ (quadSupport C).erase s, siteDegree C t := by
    have h : (∑ _t ∈ (quadSupport C).erase s, (2 : ℕ))
        ≤ ∑ t ∈ (quadSupport C).erase s, siteDegree C t :=
      Finset.sum_le_sum
        (fun t ht => two_le_siteDegree hC (Finset.mem_of_mem_erase ht))
    have herase := Finset.card_erase_of_mem hs
    rw [hk] at herase
    rw [Finset.sum_const, herase, nsmul_eq_mul, Nat.cast_id] at h
    omega
  have hle : siteDegree C s ≤ 2 := by omega
  exact le_antisymm hle (two_le_siteDegree hC hs)

/-- **The pattern cases.** Every primitive quad has one
of the degree patterns `(2,2,2,2)`, `(3,3,2)`, `(4,2,2)`
— the support has `3` or `4` sites (never `2`, by the
`(4,4)` impossibility), and at `3` sites the degrees are
three numbers in `[2, 4]` summing to `8`. -/
theorem pattern_cases (hN : Even N) {C : Finset (LayerColumn N)}
    (hC : IsPrimitiveQuad C) :
    HasPattern2222 C ∨ HasPattern332 C ∨ HasPattern422 C := by
  have hk2 := quadSupport_card_ge_two hN hC
  have hk4 := quadSupport_card_le_four hN hC
  have hkne := quadSupport_card_ne_two hN hC
  have hk : (quadSupport C).card = 3 ∨ (quadSupport C).card = 4 := by
    omega
  rcases hk with hk | hk
  · obtain ⟨a, b, c, hab, hac, hbc, hsupp⟩ := Finset.card_eq_three.mp hk
    have ha_mem : a ∈ quadSupport C := by
      rw [hsupp]
      exact Finset.mem_insert_self _ _
    have hb_mem : b ∈ quadSupport C := by
      rw [hsupp]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hc_mem : c ∈ quadSupport C := by
      rw [hsupp]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have ha2 : 2 ≤ siteDegree C a := two_le_siteDegree hC ha_mem
    have hb2 : 2 ≤ siteDegree C b := two_le_siteDegree hC hb_mem
    have hc2 : 2 ≤ siteDegree C c := two_le_siteDegree hC hc_mem
    have ha4 : siteDegree C a ≤ 4 := siteDegree_le_four hC.1 a
    have hb4 : siteDegree C b ≤ 4 := siteDegree_le_four hC.1 b
    have hc4 : siteDegree C c ≤ 4 := siteDegree_le_four hC.1 c
    have hsum := sum_siteDegree_eq hN hC.1
    rw [hsupp, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac⟩), Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hbc), Finset.sum_singleton] at hsum
    have hsupp_cab : quadSupport C = {c, a, b} := by
      rw [hsupp]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hsupp_bac : quadSupport C = {b, a, c} := by
      rw [hsupp]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hsupp_acb : quadSupport C = {a, c, b} := by
      rw [hsupp]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hsupp_bca : quadSupport C = {b, c, a} := by
      rw [hsupp]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    interval_cases h1 : siteDegree C a <;>
      interval_cases h2 : siteDegree C b <;>
      interval_cases h3 : siteDegree C c <;> try omega
    · exact Or.inr (Or.inr ⟨c, a, b, Ne.symm hac, Ne.symm hbc, hab,
        hsupp_cab, h3, h1, h2⟩)
    · exact Or.inr (Or.inl ⟨b, c, a, hbc, Ne.symm hab, Ne.symm hac,
        hsupp_bca, h2, h3, h1⟩)
    · exact Or.inr (Or.inr ⟨b, a, c, Ne.symm hab, hbc, hac,
        hsupp_bac, h2, h1, h3⟩)
    · exact Or.inr (Or.inl ⟨a, c, b, hac, hab, Ne.symm hbc,
        hsupp_acb, h1, h3, h2⟩)
    · exact Or.inr (Or.inl ⟨a, b, c, hab, hac, hbc, hsupp, h1, h2, h3⟩)
    · exact Or.inr (Or.inr ⟨a, b, c, hab, hac, hbc, hsupp, h1, h2, h3⟩)
  · exact Or.inl ⟨hk, fun s hs =>
      siteDegree_eq_two_of_card_four hN hC hk hs⟩

/-- Membership in `primitiveQuads` is the primitivity
predicate. -/
theorem isPrimitiveQuad_of_mem {C : Finset (LayerColumn N)}
    (h : C ∈ primitiveQuads) : IsPrimitiveQuad C := by
  have h2 := Finset.mem_filter.mp h
  exact h2.2

/-- The support of a `(3,3,2)` quad has card `3`. -/
theorem quadSupport_card_of_pattern332 {C : Finset (LayerColumn N)}
    (hC : HasPattern332 C) : (quadSupport C).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hsupp, -, -, -⟩ := hC
  exact quadSupport_card_of_eq_insert3 hab hac hbc hsupp

/-- The support of a `(4,2,2)` quad has card `3`. -/
theorem quadSupport_card_of_pattern422 {C : Finset (LayerColumn N)}
    (hC : HasPattern422 C) : (quadSupport C).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hsupp, -, -, -⟩ := hC
  exact quadSupport_card_of_eq_insert3 hab hac hbc hsupp

/-- The four patterns are pairwise disjoint: `C4` and
`digon ⊔ digon` by the digon-pair dichotomy itself, the
`(2,2,2,2)` patterns against `(3,3,2)`/`(4,2,2)` by
support card (`4 ≠ 3`), and `(3,3,2)` against `(4,2,2)`
because the latter's hub has degree `4` while every
site of the former has degree `3` or `2`. -/
theorem pattern_disjoint (_hN : Even N) {C : Finset (LayerColumn N)} :
    (HasPatternC4 C → ¬ HasPatternDigonDigon C)
    ∧ (HasPatternC4 C → ¬ HasPattern332 C)
    ∧ (HasPatternC4 C → ¬ HasPattern422 C)
    ∧ (HasPatternDigonDigon C → ¬ HasPattern332 C)
    ∧ (HasPatternDigonDigon C → ¬ HasPattern422 C)
    ∧ (HasPattern332 C → ¬ HasPattern422 C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    exact h1.2 h2.2
  · intro h1 h2
    have e1 : (quadSupport C).card = 4 := h1.1.1
    have e2 := quadSupport_card_of_pattern332 h2
    omega
  · intro h1 h2
    have e1 : (quadSupport C).card = 4 := h1.1.1
    have e2 := quadSupport_card_of_pattern422 h2
    omega
  · intro h1 h2
    have e1 : (quadSupport C).card = 4 := h1.1.1
    have e2 := quadSupport_card_of_pattern332 h2
    omega
  · intro h1 h2
    have e1 : (quadSupport C).card = 4 := h1.1.1
    have e2 := quadSupport_card_of_pattern422 h2
    omega
  · intro h332 h422
    obtain ⟨a, b, c, -, -, -, hsupp, hda, hdb, hdc⟩ := h332
    obtain ⟨a2, b2, c2, -, -, -, hsupp2, hda2, -, -⟩ := h422
    have hmem : a2 ∈ quadSupport C := by
      rw [hsupp2]
      exact Finset.mem_insert_self _ _
    rw [hsupp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h] at hda2
      omega
    · rw [h] at hda2
      omega
    · rw [h] at hda2
      omega

/-- **THE PARTITION THEOREM (PQ-0 headline).** At every
even `N`, each primitive quad has **exactly one** of
the four patterns: `C4`, `digon ⊔ digon`, `(3,3,2)`,
`(4,2,2)`. The proof uses no `5 ≤ N` (nor any `3 ≤ N`)
hypothesis — so the pattern list is the same at `N = 4`,
where `N ∣ 4` wrap realizations occur (see §Wrap): no
new pattern appears there. -/
theorem primitive_pattern_partition (hN : Even N)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads) :
    (HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ HasPattern422 C) := by
  have hC : IsPrimitiveQuad C := isPrimitiveQuad_of_mem hCmem
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ := pattern_disjoint hN (C := C)
  rcases pattern_cases hN hC with h | h | h
  · by_cases hdig : ∃ P ∈ C, ∃ Q ∈ C, IsDigonPair P Q
    · exact Or.inr (Or.inl ⟨fun hC4 => hd1 hC4 ⟨h, hdig⟩, ⟨h, hdig⟩,
        fun h332 => hd4 ⟨h, hdig⟩ h332, fun h422 => hd5 ⟨h, hdig⟩ h422⟩)
    · exact Or.inl ⟨⟨h, hdig⟩, fun hDD => hd1 ⟨h, hdig⟩ hDD,
        fun h332 => hd2 ⟨h, hdig⟩ h332, fun h422 => hd3 ⟨h, hdig⟩ h422⟩
  · exact Or.inr (Or.inr (Or.inl ⟨fun hC4 => hd2 hC4 h,
      fun hDD => hd4 hDD h, h, fun h422 => hd6 h h422⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun hC4 => hd3 hC4 h,
      fun hDD => hd5 hDD h, fun h332 => hd6 h332 h, h⟩))

/-- **The sharp form at the assembly's `N`.** At
`Even N`, `3 ≤ N`, every primitive quad has pattern
`C4` and none of the other three: the support cannot
have `3` sites (the columns inject by `colSites` into
the `3` two-subsets of a `3`-site support — `4 > 3`),
and a digon pair would contradict `colSites_eq_imp`. -/
theorem primitive_pattern_eq_C4 (hN : Even N) (hN3 : 3 ≤ N)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads) :
    HasPatternC4 C ∧ ¬ HasPatternDigonDigon C
      ∧ ¬ HasPattern332 C ∧ ¬ HasPattern422 C := by
  have hC : IsPrimitiveQuad C := isPrimitiveQuad_of_mem hCmem
  have hk2 := quadSupport_card_ge_two hN hC
  have hk4 := quadSupport_card_le_four hN hC
  have hkne := quadSupport_card_ne_two hN hC
  have hk : (quadSupport C).card = 3 ∨ (quadSupport C).card = 4 := by
    omega
  have h2222 : HasPattern2222 C := by
    rcases hk with hk | hk
    · exfalso
      have hle := Finset.card_le_card_of_injOn colSites
        (s := C) (t := (quadSupport C).powersetCard 2)
        (by
          intro P hP
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          exact ⟨Finset.subset_biUnion_of_mem colSites hP,
            card_colSites_two hN P⟩)
        (by
          intro P _ Q _ hPQ
          exact colSites_eq_imp hN hN3 hPQ)
      rw [hC.1, Finset.card_powersetCard, hk] at hle
      have hchoose : Nat.choose 3 2 = 3 := rfl
      omega
    · exact ⟨hk, fun s hs =>
        siteDegree_eq_two_of_card_four hN hC hk hs⟩
  have hnodig : ¬ ∃ P ∈ C, ∃ Q ∈ C, IsDigonPair P Q := by
    rintro ⟨P, -, Q, -, hPQ, hsites⟩
    exact hPQ (colSites_eq_imp hN hN3 hsites)
  have hC4 : HasPatternC4 C := ⟨h2222, hnodig⟩
  obtain ⟨hd1, hd2, hd3, -, -, -⟩ := pattern_disjoint hN (C := C)
  exact ⟨hC4, hd1 hC4, hd2 hC4, hd3 hC4⟩

/-! ## §Wrap. The `N = 4` check

The partition theorem `primitive_pattern_partition` is
proved at every even `N` — no `5 ≤ N` hypothesis occurs
anywhere in its proof — so the pattern list at `N = 4`
(where `N ∣ 4` and straight-wrap cycles exist) is the
same four patterns: no new pattern appears. What
remains is to exhibit a straight-wrap realization: the
chain of columns along one spatial direction, closing
after four steps because `4 = 0` in `ZMod 4`. By the
sharp form `primitive_pattern_eq_C4` (which applies at
`N = 4`), its pattern is `C4`. -/

/-- The `k`-th site of the straight wrap at `N = 4`:
the site whose first spatial coordinate is `k`. -/
noncomputable def wrapSite (k : ℕ) : LayerSite 4 :=
  ⟨fun j => if j = 1 then (k : ZMod 4) else 0, by
    show (if (0 : Fin 4) = 1 then ((0 : ℕ) : ZMod 4) else 0).val = 0
    simp⟩

/-- The wrap direction: the first spatial direction. -/
def wrapDir : {ν : Fin 4 // ν ≠ 0} := ⟨1, by decide⟩

/-- The `k`-th column of the straight wrap: based at
`wrapSite k`, pointing in `wrapDir`. -/
noncomputable def wrapCol (k : ℕ) : LayerColumn 4 :=
  (wrapSite k, wrapDir)

/-- The straight-wrap quad at `N = 4`. -/
noncomputable def wrapQuad : Finset (LayerColumn 4) :=
  {wrapCol 0, wrapCol 1, wrapCol 2, wrapCol 3}

/-- Shifting a wrap site in the wrap direction advances
the chain. -/
theorem wrapSite_shift (k : ℕ) :
    layerShift wrapDir.1 wrapDir.2 (wrapSite k) = wrapSite (k + 1) := by
  apply Subtype.ext
  funext j
  show (torusShift 4 1 (wrapSite k).1) j = _
  rw [torusShift_apply, Pi.add_apply, Pi.single_apply]
  show (if j = 1 then (1 : ZMod 4) else 0)
      + (if j = 1 then (k : ZMod 4) else 0)
    = (if j = 1 then ((k + 1 : ℕ) : ZMod 4) else 0)
  by_cases hj : j = 1 <;> simp [hj, Nat.cast_add, add_comm]

/-- The chain closes after four steps: `4 = 0` in
`ZMod 4`. -/
theorem wrapSite_four : wrapSite 4 = wrapSite 0 := by
  have hcast : ((4 : ℕ) : ZMod 4) = ((0 : ℕ) : ZMod 4) := by decide
  apply Subtype.ext
  funext j
  show (if j = 1 then ((4 : ℕ) : ZMod 4) else 0)
    = (if j = 1 then ((0 : ℕ) : ZMod 4) else 0)
  by_cases hj : j = 1
  · subst hj
    exact hcast
  · rw [ite_eq_right hj, ite_eq_right hj]

/-- Wrap sites at positions `< 4` are pairwise
distinct: the first spatial coordinate separates them. -/
theorem wrapSite_inj {i j : ℕ} (hi : i < 4) (hj : j < 4)
    (h : wrapSite i = wrapSite j) : i = j := by
  have h1 : (i : ZMod 4) = (j : ZMod 4) :=
    congrFun (congrArg Subtype.val h) 1
  have h4 := congrArg ZMod.val h1
  rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at h4

/-- Wrap columns at positions `< 4` are pairwise
distinct. -/
theorem wrapCol_inj {i j : ℕ} (hi : i < 4) (hj : j < 4)
    (h : wrapCol i = wrapCol j) : i = j :=
  wrapSite_inj hi hj (congrArg Prod.fst h)

theorem wrapCol_ne_of_ne {i j : ℕ} (hi : i < 4) (hj : j < 4)
    (hne : i ≠ j) : wrapCol i ≠ wrapCol j :=
  fun h => hne (wrapCol_inj hi hj h)

/-- The two sites of a wrap column: its base and the
next site of the chain. -/
theorem colSites_wrapCol (k : ℕ) :
    colSites (wrapCol k) = {wrapSite k, wrapSite (k + 1)} := by
  have h : colSites (wrapCol k)
      = {wrapSite k, layerShift wrapDir.1 wrapDir.2 (wrapSite k)} := rfl
  rw [h, wrapSite_shift]

/-- The wrap quad has four columns. -/
theorem wrapQuad_card : wrapQuad.card = 4 := by
  have n0 : wrapCol 0 ∉ ({wrapCol 1, wrapCol 2, wrapCol 3}
      : Finset (LayerColumn 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
      wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
      wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num)⟩
  have n1 : wrapCol 1 ∉ ({wrapCol 2, wrapCol 3}
      : Finset (LayerColumn 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
      wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num)⟩
  have n2 : wrapCol 2 ∉ ({wrapCol 3} : Finset (LayerColumn 4)) := by
    simp only [Finset.mem_singleton]
    exact wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num)
  rw [wrapQuad, Finset.card_insert_of_notMem n0,
    Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
    Finset.card_singleton]

/-- The wrap quad is primitive: each site of the chain
is read by two consecutive columns of the chain (the
chain closes: `wrapSite 4 = wrapSite 0`). -/
theorem wrapQuad_primitive : IsPrimitiveQuad wrapQuad := by
  refine ⟨wrapQuad_card, ?_⟩
  intro P hP s hs
  simp only [wrapQuad, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · rw [colSites_wrapCol] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hs | hs
    · exact ⟨wrapCol 3, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inr (hs.trans wrapSite_four.symm)⟩
    · exact ⟨wrapCol 1, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inl hs⟩
  · rw [colSites_wrapCol] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hs | hs
    · exact ⟨wrapCol 0, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inr hs⟩
    · exact ⟨wrapCol 2, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inl hs⟩
  · rw [colSites_wrapCol] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hs | hs
    · exact ⟨wrapCol 1, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inr hs⟩
    · exact ⟨wrapCol 3, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inl hs⟩
  · rw [colSites_wrapCol] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hs | hs
    · exact ⟨wrapCol 2, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inr hs⟩
    · exact ⟨wrapCol 0, by simp [wrapQuad],
        wrapCol_ne_of_ne (by norm_num) (by norm_num) (by norm_num),
        by rw [colSites_wrapCol]
           simp only [Finset.mem_insert, Finset.mem_singleton]
           exact Or.inl (hs.trans wrapSite_four)⟩

set_option maxRecDepth 8192 in
/-- The wrap quad is a member of `primitiveQuads`.
(Stated as a standalone term-mode theorem: the
membership defeq at the concrete `N = 4` is deep.) -/
theorem wrapQuad_mem : wrapQuad ∈ primitiveQuads :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, wrapQuad_primitive⟩

set_option maxRecDepth 8192 in
/-- The wrap quad's pattern is `C4`, by the sharp form
at `N = 4`. -/
theorem wrapQuad_pattern : HasPatternC4 wrapQuad :=
  (primitive_pattern_eq_C4 (⟨2, rfl⟩ : Even 4) (by norm_num)
    wrapQuad_mem).1

set_option maxRecDepth 8192 in
/-- **The `N = 4` wrap check.** A straight-wrap
primitive quad exists at `N = 4`, and its pattern is
`C4` — the wrap realization lands inside the existing
pattern list, and (by `primitive_pattern_partition`,
whose proof never uses `5 ≤ N`) no other pattern can
occur at `N = 4` either. -/
theorem exists_wrap_quad :
    ∃ C ∈ primitiveQuads, HasPatternC4 C ∧ C = wrapQuad :=
  ⟨wrapQuad, wrapQuad_mem, wrapQuad_pattern, rfl⟩

set_option maxRecDepth 8192 in
/-- The partition theorem instantiated at `N = 4`: the
pattern list is unchanged when `N ∣ 4`. -/
theorem pattern_partition_at_four (C : Finset (LayerColumn 4))
    (hC : C ∈ primitiveQuads) :
    (HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ HasPattern332 C
        ∧ ¬ HasPattern422 C)
    ∨ (¬ HasPatternC4 C ∧ ¬ HasPatternDigonDigon C ∧ ¬ HasPattern332 C
        ∧ HasPattern422 C) :=
  primitive_pattern_partition (⟨2, rfl⟩ : Even 4) hC

