/-
# B7-0: order-7 selection (the β⁷ selection rule, Route A's
advance guard)

Selection combinatorics for a multiplicity function `m` on
columns with total multiplicity `∑ P, m P = 7`, fully shared
in the WEIGHTED sense (`WFullyShared`, owned by B6-0: every
support site has `wSiteDegree ≥ 2`), with no private column,
modulo the erasure recursion. This module proves which
multiplicity patterns survive, card by card, along the β⁷
scoping's claim-to-check list (`scoping-beta7-2026-10-29.md`
§1):

- card ≤ 3: a private column (the ≤ 3 distinct supports
  factor into constants at arbitrary exponents, owned).
- card 4: patterns `(4,1,1,1)`, `(3,2,1,1)`, `(2,2,2,1)`,
  all LIVE on a primitive quad support (or a private
  column, the corrected disjunctive form of B6-0);
  `(3,2,1,1)` splits into ADJACENT / OPPOSITE sub-shapes
  by whether its two heavy columns share a site.
- card 5: patterns `(3,1,1,1,1)` and `(2,2,1,1,1)`, and
  every such configuration has a private column —
  DIES-BY the private-column erasure recursion. This was
  the scoping's sharpest claim-to-check: an exceptional
  weighted-fully-shared card-5 shape with no private
  column would be a distinctly-shared 5-support, which
  the squeeze excludes (distinctly-shared cards are
  exactly `4`, `6`, `7` at this order). No exceptional
  shape exists; the prediction lands as stated.
- card 6: pattern `(2,1,1,1,1,1)`; the distinct support
  is a `C₆` pattern, a `Θ(2,2,2)` pattern, or has a
  private column — the two death certificates kept
  DISTINCT, as at B6-0: the `C4`+tail wrap type is
  weighted-fully-shared but its tail column is private,
  so it dies by ERASURE and is not a `C₆`/`Θ` support.
  LIVE: `(2,1,1,1,1,1)` on `C₆` and on `Θ(2,2,2)`.
- card 7: pattern `(1⁷)`; the distinct support has six
  sites with degree pattern `(3,3,2,2,2,2)` — the
  `Θ(1,3,3)` type (two unit plaquettes sharing one
  column), LIVE as a candidate channel. The `C₇` type
  (seven sites, all degrees `2`) is bipartite-dead and
  is excluded by the classification; `Θ(1,1,5)` carries
  a digon pair and is excluded by the multiplicity-≤-1
  fact (`colSites_eq_imp` at `3 ≤ N`): no digon pair
  exists in any distinct support. The remaining abstract
  types predicted dead by the pair-injection bound and
  lattice realizability are exactly the degree patterns
  the classification excludes: at card `7` the parity
  classes are forced to `(3,3)`, each side's degrees are
  forced to `(3,2,2)`, so no degree-`4` site and no
  `(3,3,3,·)` type survives.

Fences (binding on every statement in this file):
NO CLAIM. 0 parts of the Clay statement are closed by
this file. Dials 0/4. No sign is asserted for β⁷ or for
any other order; the general β⁷ sign remains FRONTIER.
K-K7 is pre-registered downstream (the probe, held
behind GD-PROBE); nothing here fires, discharges, or
prejudges K-K7. The selection asserts no sign.

Wrap sector at `N = 4`: fenced exactly as at β⁴/β⁵/β⁶ —
the characterization is proved at general (Even `N`,
`3 ≤ N`) and is instantiated at `N = 4` at the end of
this file; wrap realizations of `C₆`-type supports land
inside the same lists. No new fence is invented.
-/

import ThetLogos.OrderSixSelection

open Finset

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## Definitions introduced by B7-0 -/

/-- The `Θ(1,3,3)` degree pattern at card `7`: the support
reads six sites, two hubs `a, b` of distinct degree `3`,
and every other support site of distinct degree `2`.
(Two unit plaquettes sharing one column: cycles `4, 4, 6`,
degrees `(3,3,2,2,2,2)`.) -/
def HasSevenPatternTheta133 (S : Finset (LayerColumn N)) : Prop :=
  (quadSupport S).card = 6 ∧
  ∃ a b, a ≠ b ∧ a ∈ quadSupport S ∧ b ∈ quadSupport S ∧
    siteDegree S a = 3 ∧ siteDegree S b = 3 ∧
    ∀ s ∈ quadSupport S, s ≠ a → s ≠ b → siteDegree S s = 2

/-- The `C₇` degree pattern at card `7`: the support reads
seven sites, each of distinct degree `2` (a single
7-cycle). Bipartite-dead: no even cycle has length `7`,
and the card-7 classification excludes it. -/
def HasSevenPatternC7 (S : Finset (LayerColumn N)) : Prop :=
  (quadSupport S).card = 7 ∧ ∀ s ∈ quadSupport S, siteDegree S s = 2

/-! ## Support arithmetic at total multiplicity 7 -/

/-- The multiplicities over the distinct support sum to
the total multiplicity, here `7`. -/
theorem sum_multSupport_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) : ∑ P ∈ multSupport m, m P = 7 := by
  have h : ∑ P ∈ multSupport m, m P = ∑ P, m P := by
    unfold multSupport
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    by_cases hP : m P ≠ 0
    · simp [hP]
    · have hm0 : m P = 0 := not_ne_iff.mp hP
      simp [hP, hm0]
  rw [h, hm7]

/-- The distinct support of an order-7 multiplicity
function has at most `7` columns. -/
theorem card_multSupport_le_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) : (multSupport m).card ≤ 7 := by
  have h1 : (∑ _P ∈ multSupport m, (1 : ℕ))
      ≤ ∑ P ∈ multSupport m, m P :=
    Finset.sum_le_sum fun P hP => one_le_of_mem_multSupport m hP
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_one,
    sum_multSupport_seven m hm7] at h1
  exact h1

/-- Weighted parity bound, even side: in a weighted
fully-shared order-7 configuration, at most `3` even
support sites occur. -/
theorem even_filter_card_le_three_seven (hN : Even N)
    (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hW : WFullyShared m) :
    ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0)).card ≤ 3 := by
  classical
  have hmS : ∀ P : LayerColumn N, m P ≠ 0 → P ∈ multSupport m := by
    intro P hP
    unfold multSupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hP⟩
  have hEvenW : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0), wSiteDegree m s = 7 :=
    (sum_wSiteDegree_filter_eq m (multSupport m) hmS
      (fun P => (colSites_filter_parity_cards hN P).1)).trans
        (sum_multSupport_seven m hm7)
  have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s = 0), (2 : ℕ))
      ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s = 0), wSiteDegree m s :=
    Finset.sum_le_sum fun s hs => hW s (Finset.mem_filter.mp hs).1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
  omega

/-- Weighted parity bound, odd side: the twin of
`even_filter_card_le_three_seven`. -/
theorem odd_filter_card_le_three_seven (hN : Even N)
    (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hW : WFullyShared m) :
    ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0)).card ≤ 3 := by
  classical
  have hmS : ∀ P : LayerColumn N, m P ≠ 0 → P ∈ multSupport m := by
    intro P hP
    unfold multSupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hP⟩
  have hOddW : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0), wSiteDegree m s = 7 :=
    (sum_wSiteDegree_filter_eq m (multSupport m) hmS
      (fun P => (colSites_filter_parity_cards hN P).2)).trans
        (sum_multSupport_seven m hm7)
  have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s ≠ 0), (2 : ℕ))
      ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s ≠ 0), wSiteDegree m s :=
    Finset.sum_le_sum fun s hs => hW s (Finset.mem_filter.mp hs).1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
  omega

/-! ## The distinctly-shared squeeze at order 7 -/

/-- **The distinctly-shared squeeze at order 7.** If every
support site of an order-7 multiplicity function has
distinct degree at least `2`, the distinct support has
card `4`, `6`, or `7`. The parity balances give `2e ≤ card`
and `2o ≤ card` for the even and odd support-site counts
`e, o`; the total gives `card ≤ 7`, hence `e, o ≤ 3`; the
pair injection gives `card ≤ e * o`; and the support is
nonempty since the total multiplicity is `7`. The interval
squeeze on `e, o` then leaves only `4`, `6`, `7` — in
particular no distinctly-shared support has card `5`,
which is the combinatorial core of the card-5 erasure
death. -/
theorem card_eq_four_six_seven_of_distinctlyShared (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s) :
    (multSupport m).card = 4 ∨ (multSupport m).card = 6
      ∨ (multSupport m).card = 7 := by
  classical
  set e : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s = 0)).card with hedef
  set o : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s ≠ 0)).card with hodef
  have hEven : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0),
      siteDegree (multSupport m) s = (multSupport m).card :=
    sum_siteDegree_even_eq hN (multSupport m)
  have hOdd : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0),
      siteDegree (multSupport m) s = (multSupport m).card :=
    sum_siteDegree_odd_eq hN (multSupport m)
  have h2e : 2 * e ≤ (multSupport m).card := by
    have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s = 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s = 0),
          siteDegree (multSupport m) s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have h2o : 2 * o ≤ (multSupport m).card := by
    have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s ≠ 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s ≠ 0),
          siteDegree (multSupport m) s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have hk7 : (multSupport m).card ≤ 7 := card_multSupport_le_seven m hm7
  have he3 : e ≤ 3 := by omega
  have ho3 : o ≤ 3 := by omega
  have hprod : (multSupport m).card ≤ e * o := by
    have hinj := card_le_even_mul_odd hN hN3 (multSupport m)
    rw [← hedef, ← hodef] at hinj
    exact hinj
  have hpos : 1 ≤ (multSupport m).card := by
    by_contra hlt
    push_neg at hlt
    have h0 : (multSupport m).card = 0 := by omega
    have hempty : multSupport m = ∅ := Finset.card_eq_zero.mp h0
    have hsum := sum_multSupport_seven m hm7
    rw [hempty, Finset.sum_empty] at hsum
    omega
  interval_cases e <;> interval_cases o <;> omega

/-- If the distinct support of an order-7 multiplicity
function has card neither `4`, `6`, nor `7`, it has a
private column: otherwise distinct sharing would force
one of those cards by
`card_eq_four_six_seven_of_distinctlyShared`. In
particular this applies at cards `5`, `3`, `2`, `1`. -/
theorem hasPrivateColumn_of_card_ne_four_six_seven (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (h4 : (multSupport m).card ≠ 4) (h6 : (multSupport m).card ≠ 6)
    (h7 : (multSupport m).card ≠ 7) :
    HasPrivateColumn (multSupport m) := by
  classical
  by_cases hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s
  · rcases card_eq_four_six_seven_of_distinctlyShared hN hN3 m hm7 hDS
      with h | h | h
    · exact absurd h h4
    · exact absurd h h6
    · exact absurd h h7
  · exact hasPrivateColumn_of_not_distinctlyShared m hDS

/-! ## Weighted degree = distinct degree when all
multiplicities are 1 -/

/-- If every column of the distinct support has
multiplicity exactly `1`, the weighted site degree agrees
with the distinct site degree everywhere: every
contributing column has multiplicity `1`, and columns
outside the support contribute `0`. (The order-7 form of
B6-0's card-6 lemma, at the generality the card-7
classification needs.) -/
theorem wSiteDegree_eq_siteDegree_of_all_one
    (m : LayerColumn N → ℕ)
    (hall : ∀ P ∈ multSupport m, m P = 1) (s : LayerSite N) :
    wSiteDegree m s = siteDegree (multSupport m) s := by
  classical
  have hsub : (multSupport m).filter (fun P => s ∈ colSites P)
      ⊆ Finset.univ.filter (fun P => s ∈ colSites P) := by
    intro P hP
    obtain ⟨hPm, hsP⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hsP⟩
  have hzero : ∀ P ∈ Finset.univ.filter (fun P => s ∈ colSites P),
      P ∉ (multSupport m).filter (fun P => s ∈ colSites P) →
      m P = 0 := by
    intro P hP hnot
    by_contra hm0
    have hPm : P ∈ multSupport m := by
      unfold multSupport
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hm0⟩
    exact hnot (Finset.mem_filter.mpr
      ⟨hPm, (Finset.mem_filter.mp hP).2⟩)
  have hsum : ∑ P ∈ (multSupport m).filter (fun P => s ∈ colSites P),
        m P
      = ∑ P ∈ Finset.univ.filter (fun P => s ∈ colSites P), m P :=
    Finset.sum_subset hsub hzero
  have hone : ∑ P ∈ (multSupport m).filter (fun P => s ∈ colSites P),
        m P
      = ((multSupport m).filter (fun P => s ∈ colSites P)).card := by
    calc ∑ P ∈ (multSupport m).filter (fun P => s ∈ colSites P), m P
        = ∑ _P ∈ (multSupport m).filter (fun P => s ∈ colSites P),
            (1 : ℕ) :=
          Finset.sum_congr rfl fun P hP =>
            hall P (Finset.mem_filter.mp hP).1
      _ = ((multSupport m).filter (fun P => s ∈ colSites P)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  unfold wSiteDegree siteDegree
  rw [← hsum, hone]

/-! ## Digon exclusion and the adjacency dichotomy -/

/-- **No digon pair in any distinct support.** Two distinct
columns of a set cannot lie over the same unordered site
pair at `3 ≤ N`: a column is determined by its two sites
(`colSites_eq_imp`). This is the death of the `Θ(1,1,5)`
type at card `7`, whose two direct paths between its hubs
are a digon pair. -/
theorem not_digon_pair (hN : Even N) (hN3 : 3 ≤ N)
    (S : Finset (LayerColumn N)) {P Q : LayerColumn N}
    (hP : P ∈ S) (hQ : Q ∈ S) : ¬ IsDigonPair P Q := by
  rintro ⟨hne, hsites⟩
  exact hne (colSites_eq_imp hN hN3 hsites)

/-- The ADJACENT / OPPOSITE dichotomy for two columns: two
columns either share a site (ADJACENT) or have disjoint
site pairs (OPPOSITE). At card `4` this is the sub-shape
split of the `(3,2,1,1)` pattern by its heavy columns'
relative position. -/
theorem columns_adjacent_or_opposite (P Q : LayerColumn N) :
    (∃ s, s ∈ colSites P ∧ s ∈ colSites Q)
      ∨ (∀ s, s ∈ colSites P → s ∉ colSites Q) := by
  classical
  by_cases h : ∃ s, s ∈ colSites P ∧ s ∈ colSites Q
  · exact Or.inl h
  · refine Or.inr fun s hsP hsQ => h ⟨s, hsP, hsQ⟩

/-! ## Multiplicity patterns, cards 7, 6, 5 -/

/-- Helper: if the multiplicities over a finset `T` (each at
least `1`) sum to strictly more than `T.card`, some member
has multiplicity at least `2`. -/
theorem exists_two_le_of_card_lt_sum {m : LayerColumn N → ℕ}
    {T : Finset (LayerColumn N)} (h1 : ∀ P ∈ T, 1 ≤ m P)
    (hlt : T.card < ∑ P ∈ T, m P) : ∃ P₀ ∈ T, 2 ≤ m P₀ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hle : ∑ P ∈ T, m P ≤ ∑ _P ∈ T, (1 : ℕ) :=
    Finset.sum_le_sum fun P hP => by
      have hltP : m P < 2 := hcon P hP
      omega
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
  omega

/-- Helper: the multiplicities over `T.erase P₀` sum to at
least `(T.erase P₀).card` — each member contributes at
least `1`. -/
theorem card_erase_le_sum_erase {m : LayerColumn N → ℕ}
    {T : Finset (LayerColumn N)} (h1 : ∀ P ∈ T, 1 ≤ m P)
    {P₀ : LayerColumn N} (hP₀ : P₀ ∈ T) :
    (T.erase P₀).card ≤ ∑ P ∈ T.erase P₀, m P := by
  classical
  have hle : (∑ _Q ∈ T.erase P₀, (1 : ℕ))
      ≤ ∑ Q ∈ T.erase P₀, m Q :=
    Finset.sum_le_sum fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)
  rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle

/-- Card-7 pattern: an order-7 multiplicity function whose
distinct support has `7` columns has pattern `(1⁷)`: every
multiplicity is `1`. -/
theorem eq_one_of_card_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) (hcard : (multSupport m).card = 7) :
    ∀ P ∈ multSupport m, m P = 1 := by
  intro P hP
  apply eq_one_of_sum_eq_card
    (fun Q hQ => one_le_of_mem_multSupport m hQ) _ hP
  rw [sum_multSupport_seven m hm7, hcard]

/-- Card-6 pattern: an order-7 multiplicity function whose
distinct support has `6` columns has pattern
`(2,1,1,1,1,1)`: one column of multiplicity `2` and the
rest of multiplicity `1`. -/
theorem pattern_of_card_six_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) (hcard : (multSupport m).card = 6) :
    ∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1 := by
  classical
  have hsumS : ∑ P ∈ multSupport m, m P = 7 :=
    sum_multSupport_seven m hm7
  have h1 : ∀ P ∈ multSupport m, 1 ≤ m P :=
    fun P hP => one_le_of_mem_multSupport m hP
  obtain ⟨P₀, hP₀S, hP₀ge⟩ : ∃ P₀ ∈ multSupport m, 2 ≤ m P₀ :=
    exists_two_le_of_card_lt_sum h1 (by omega)
  have hsplit : ∑ P ∈ multSupport m, m P
      = m P₀ + ∑ P ∈ (multSupport m).erase P₀, m P :=
    (Finset.add_sum_erase _ m hP₀S).symm
  have herase := card_erase_le_sum_erase h1 hP₀S
  have hcarderase : ((multSupport m).erase P₀).card = 5 := by
    have h := Finset.card_erase_of_mem hP₀S
    omega
  have hP₀eq : m P₀ = 2 := by omega
  have hsumErase : ∑ P ∈ (multSupport m).erase P₀, m P
      = ((multSupport m).erase P₀).card := by omega
  refine ⟨P₀, hP₀S, hP₀eq, ?_⟩
  intro P hPS hne
  have hPerase : P ∈ (multSupport m).erase P₀ :=
    Finset.mem_erase.mpr ⟨hne, hPS⟩
  exact eq_one_of_sum_eq_card
    (fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)) hsumErase hPerase

/-- Card-5 patterns: an order-7 multiplicity function whose
distinct support has `5` columns has pattern `(3,1,1,1,1)`
or `(2,2,1,1,1)`. -/
theorem patterns_of_card_five_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) (hcard : (multSupport m).card = 5) :
    (∃ P₀ ∈ multSupport m, m P₀ = 3 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
    (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
      m P₀ = 2 ∧ m P₁ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1) := by
  classical
  have hsumS : ∑ P ∈ multSupport m, m P = 7 :=
    sum_multSupport_seven m hm7
  have h1 : ∀ P ∈ multSupport m, 1 ≤ m P :=
    fun P hP => one_le_of_mem_multSupport m hP
  obtain ⟨P₀, hP₀S, hP₀ge⟩ : ∃ P₀ ∈ multSupport m, 2 ≤ m P₀ :=
    exists_two_le_of_card_lt_sum h1 (by omega)
  have hsplit : ∑ P ∈ multSupport m, m P
      = m P₀ + ∑ P ∈ (multSupport m).erase P₀, m P :=
    (Finset.add_sum_erase _ m hP₀S).symm
  have herase := card_erase_le_sum_erase h1 hP₀S
  have hcarderase : ((multSupport m).erase P₀).card = 4 := by
    have h := Finset.card_erase_of_mem hP₀S
    omega
  have hP₀le : m P₀ ≤ 3 := by omega
  by_cases h3 : m P₀ = 3
  · left
    have hsumErase : ∑ P ∈ (multSupport m).erase P₀, m P
        = ((multSupport m).erase P₀).card := by omega
    refine ⟨P₀, hP₀S, h3, ?_⟩
    intro P hPS hne
    have hPerase : P ∈ (multSupport m).erase P₀ :=
      Finset.mem_erase.mpr ⟨hne, hPS⟩
    exact eq_one_of_sum_eq_card
      (fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)) hsumErase hPerase
  · have hP₀eq : m P₀ = 2 := by omega
    have hsumT : ∑ P ∈ (multSupport m).erase P₀, m P = 5 := by omega
    have h1T : ∀ P ∈ (multSupport m).erase P₀, 1 ≤ m P :=
      fun P hP => h1 P (Finset.mem_of_mem_erase hP)
    obtain ⟨P₁, hP₁T, hP₁ge⟩ :
        ∃ P₁ ∈ (multSupport m).erase P₀, 2 ≤ m P₁ :=
      exists_two_le_of_card_lt_sum h1T (by omega)
    have hP₁S : P₁ ∈ multSupport m := Finset.mem_of_mem_erase hP₁T
    have hne₁₀ : P₁ ≠ P₀ := (Finset.mem_erase.mp hP₁T).1
    have hsplitT : ∑ P ∈ (multSupport m).erase P₀, m P
        = m P₁ + ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P :=
      (Finset.add_sum_erase _ m hP₁T).symm
    have heraseU := card_erase_le_sum_erase h1T hP₁T
    have hcardU : (((multSupport m).erase P₀).erase P₁).card = 3 := by
      have h := Finset.card_erase_of_mem hP₁T
      omega
    have hP₁eq : m P₁ = 2 := by omega
    have hsumU : ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P
        = (((multSupport m).erase P₀).erase P₁).card := by omega
    right
    refine ⟨P₀, hP₀S, P₁, hP₁S, hne₁₀.symm, hP₀eq, hP₁eq, ?_⟩
    intro P hPS hne0 hne1
    have hPT : P ∈ (multSupport m).erase P₀ :=
      Finset.mem_erase.mpr ⟨hne0, hPS⟩
    have hPU : P ∈ ((multSupport m).erase P₀).erase P₁ :=
      Finset.mem_erase.mpr ⟨hne1, hPT⟩
    exact eq_one_of_sum_eq_card
      (fun Q hQ => h1T Q (Finset.mem_of_mem_erase hQ)) hsumU hPU

/-! ## Multiplicity patterns at card 4 -/

/-- Card-4 patterns: an order-7 multiplicity function whose
distinct support has `4` columns has pattern `(4,1,1,1)`,
`(3,2,1,1)`, or `(2,2,2,1)`. -/
theorem patterns_of_card_four_seven (m : LayerColumn N → ℕ)
    (hm7 : ∑ P, m P = 7) (hcard : (multSupport m).card = 4) :
    (∃ P₀ ∈ multSupport m, m P₀ = 4 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
    (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
      m P₀ = 3 ∧ m P₁ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1) ∨
    (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m,
      ∃ P₂ ∈ multSupport m, P₀ ≠ P₁ ∧ P₀ ≠ P₂ ∧ P₁ ≠ P₂ ∧
      m P₀ = 2 ∧ m P₁ = 2 ∧ m P₂ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → P ≠ P₂ →
        m P = 1) := by
  classical
  have hsumS : ∑ P ∈ multSupport m, m P = 7 :=
    sum_multSupport_seven m hm7
  have h1 : ∀ P ∈ multSupport m, 1 ≤ m P :=
    fun P hP => one_le_of_mem_multSupport m hP
  obtain ⟨P₀, hP₀S, hP₀ge⟩ : ∃ P₀ ∈ multSupport m, 2 ≤ m P₀ :=
    exists_two_le_of_card_lt_sum h1 (by omega)
  have hsplit : ∑ P ∈ multSupport m, m P
      = m P₀ + ∑ P ∈ (multSupport m).erase P₀, m P :=
    (Finset.add_sum_erase _ m hP₀S).symm
  have herase := card_erase_le_sum_erase h1 hP₀S
  have hcarderase : ((multSupport m).erase P₀).card = 3 := by
    have h := Finset.card_erase_of_mem hP₀S
    omega
  have hP₀le : m P₀ ≤ 4 := by omega
  have h1T : ∀ P ∈ (multSupport m).erase P₀, 1 ≤ m P :=
    fun P hP => h1 P (Finset.mem_of_mem_erase hP)
  by_cases h4 : m P₀ = 4
  · left
    have hsumErase : ∑ P ∈ (multSupport m).erase P₀, m P
        = ((multSupport m).erase P₀).card := by omega
    refine ⟨P₀, hP₀S, h4, ?_⟩
    intro P hPS hne
    have hPerase : P ∈ (multSupport m).erase P₀ :=
      Finset.mem_erase.mpr ⟨hne, hPS⟩
    exact eq_one_of_sum_eq_card
      (fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)) hsumErase hPerase
  by_cases h3 : m P₀ = 3
  · have hsumT : ∑ P ∈ (multSupport m).erase P₀, m P = 4 := by omega
    obtain ⟨P₁, hP₁T, hP₁ge⟩ :
        ∃ P₁ ∈ (multSupport m).erase P₀, 2 ≤ m P₁ :=
      exists_two_le_of_card_lt_sum h1T (by omega)
    have hP₁S : P₁ ∈ multSupport m := Finset.mem_of_mem_erase hP₁T
    have hne₁₀ : P₁ ≠ P₀ := (Finset.mem_erase.mp hP₁T).1
    have hsplitT : ∑ P ∈ (multSupport m).erase P₀, m P
        = m P₁ + ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P :=
      (Finset.add_sum_erase _ m hP₁T).symm
    have heraseU := card_erase_le_sum_erase h1T hP₁T
    have hcardU : (((multSupport m).erase P₀).erase P₁).card = 2 := by
      have h := Finset.card_erase_of_mem hP₁T
      omega
    have hP₁eq : m P₁ = 2 := by omega
    have hsumU : ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P
        = (((multSupport m).erase P₀).erase P₁).card := by omega
    refine Or.inr (Or.inl ⟨P₀, hP₀S, P₁, hP₁S, hne₁₀.symm, h3,
      hP₁eq, ?_⟩)
    intro P hPS hne0 hne1
    have hPT : P ∈ (multSupport m).erase P₀ :=
      Finset.mem_erase.mpr ⟨hne0, hPS⟩
    have hPU : P ∈ ((multSupport m).erase P₀).erase P₁ :=
      Finset.mem_erase.mpr ⟨hne1, hPT⟩
    exact eq_one_of_sum_eq_card
      (fun Q hQ => h1T Q (Finset.mem_of_mem_erase hQ)) hsumU hPU
  · have hP₀eq : m P₀ = 2 := by omega
    have hsumT : ∑ P ∈ (multSupport m).erase P₀, m P = 5 := by omega
    obtain ⟨P₁, hP₁T, hP₁ge⟩ :
        ∃ P₁ ∈ (multSupport m).erase P₀, 2 ≤ m P₁ :=
      exists_two_le_of_card_lt_sum h1T (by omega)
    have hP₁S : P₁ ∈ multSupport m := Finset.mem_of_mem_erase hP₁T
    have hne₁₀ : P₁ ≠ P₀ := (Finset.mem_erase.mp hP₁T).1
    have hsplitT : ∑ P ∈ (multSupport m).erase P₀, m P
        = m P₁ + ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P :=
      (Finset.add_sum_erase _ m hP₁T).symm
    have heraseU := card_erase_le_sum_erase h1T hP₁T
    have hcardU : (((multSupport m).erase P₀).erase P₁).card = 2 := by
      have h := Finset.card_erase_of_mem hP₁T
      omega
    have hP₁le : m P₁ ≤ 3 := by omega
    have h1U : ∀ P ∈ ((multSupport m).erase P₀).erase P₁, 1 ≤ m P :=
      fun P hP => h1T P (Finset.mem_of_mem_erase hP)
    by_cases hP₁3 : m P₁ = 3
    · have hsumU : ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P
          = (((multSupport m).erase P₀).erase P₁).card := by omega
      refine Or.inr (Or.inl ⟨P₁, hP₁S, P₀, hP₀S, hne₁₀, hP₁3,
        hP₀eq, ?_⟩)
      intro P hPS hne1 hne0
      have hPT : P ∈ (multSupport m).erase P₀ :=
        Finset.mem_erase.mpr ⟨hne0, hPS⟩
      have hPU : P ∈ ((multSupport m).erase P₀).erase P₁ :=
        Finset.mem_erase.mpr ⟨hne1, hPT⟩
      exact eq_one_of_sum_eq_card
        (fun Q hQ => h1T Q (Finset.mem_of_mem_erase hQ)) hsumU hPU
    · have hP₁eq : m P₁ = 2 := by omega
      have hsumU : ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P
          = 3 := by omega
      obtain ⟨P₂, hP₂U, hP₂ge⟩ :
          ∃ P₂ ∈ ((multSupport m).erase P₀).erase P₁, 2 ≤ m P₂ :=
        exists_two_le_of_card_lt_sum h1U (by omega)
      have hP₂T : P₂ ∈ (multSupport m).erase P₀ :=
        Finset.mem_of_mem_erase hP₂U
      have hP₂S : P₂ ∈ multSupport m :=
        Finset.mem_of_mem_erase hP₂T
      have hne₂₁ : P₂ ≠ P₁ := (Finset.mem_erase.mp hP₂U).1
      have hne₂₀ : P₂ ≠ P₀ := (Finset.mem_erase.mp hP₂T).1
      have hsplitU : ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P
          = m P₂
            + ∑ P ∈ (((multSupport m).erase P₀).erase P₁).erase P₂,
              m P :=
        (Finset.add_sum_erase _ m hP₂U).symm
      have heraseV := card_erase_le_sum_erase h1U hP₂U
      have hcardV :
          ((((multSupport m).erase P₀).erase P₁).erase P₂).card
            = 1 := by
        have h := Finset.card_erase_of_mem hP₂U
        omega
      have hP₂eq : m P₂ = 2 := by omega
      have hsumV :
          ∑ P ∈ (((multSupport m).erase P₀).erase P₁).erase P₂, m P
            = ((((multSupport m).erase P₀).erase P₁).erase P₂).card :=
        by omega
      refine Or.inr (Or.inr ⟨P₀, hP₀S, P₁, hP₁S, P₂, hP₂S,
        hne₁₀.symm, hne₂₀.symm, hne₂₁.symm, hP₀eq, hP₁eq, hP₂eq, ?_⟩)
      intro P hPS hne0 hne1 hne2
      have hPT : P ∈ (multSupport m).erase P₀ :=
        Finset.mem_erase.mpr ⟨hne0, hPS⟩
      have hPU : P ∈ ((multSupport m).erase P₀).erase P₁ :=
        Finset.mem_erase.mpr ⟨hne1, hPT⟩
      have hPV : P ∈ (((multSupport m).erase P₀).erase P₁).erase P₂ :=
        Finset.mem_erase.mpr ⟨hne2, hPU⟩
      exact eq_one_of_sum_eq_card
        (fun Q hQ => h1U Q (Finset.mem_of_mem_erase hQ)) hsumV hPV

/-! ## Card-6 distinct-support classification -/

/-- **Distinct card-6 classification.** A set of `6` distinct
columns, every support site of distinct degree at least
`2`, is a `C₆` pattern (six sites, all degrees `2`) or a
`Θ(2,2,2)` pattern (five sites, two hubs of degree `3`,
the rest `2`). This is B6-0's card-6 classification read
off the distinct support alone — it is the statement the
order-7 card-6 case consumes, where the support carries
one doubled column and weighted sharing does not by
itself give distinct sharing. -/
theorem card_six_distinct_classification (hN : Even N)
    (hN3 : 3 ≤ N) (S : Finset (LayerColumn N)) (hcard : S.card = 6)
    (hDS : ∀ s ∈ quadSupport S, 2 ≤ siteDegree S s) :
    HasSixPatternC6 S ∨ HasSixPatternTheta S := by
  classical
  have hEvenSum : ∑ s ∈ (quadSupport S).filter
        (fun s => siteParity hN s = 0), siteDegree S s = 6 := by
    rw [sum_siteDegree_even_eq hN S, hcard]
  have hOddSum : ∑ s ∈ (quadSupport S).filter
        (fun s => siteParity hN s ≠ 0), siteDegree S s = 6 := by
    rw [sum_siteDegree_odd_eq hN S, hcard]
  set e : ℕ := ((quadSupport S).filter
    (fun s => siteParity hN s = 0)).card with hedef
  set o : ℕ := ((quadSupport S).filter
    (fun s => siteParity hN s ≠ 0)).card with hodef
  have h2e : 2 * e ≤ 6 := by
    have h1 : (∑ s ∈ (quadSupport S).filter
            (fun s => siteParity hN s = 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport S).filter
            (fun s => siteParity hN s = 0), siteDegree S s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have h2o : 2 * o ≤ 6 := by
    have h1 : (∑ s ∈ (quadSupport S).filter
            (fun s => siteParity hN s ≠ 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport S).filter
            (fun s => siteParity hN s ≠ 0), siteDegree S s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have he3 : e ≤ 3 := by omega
  have ho3 : o ≤ 3 := by omega
  have hprod : 6 ≤ e * o := by
    have h := card_le_even_mul_odd hN hN3 S
    rwa [hcard, ← hedef, ← hodef] at h
  have hEO : e + o = (quadSupport S).card :=
    Finset.card_filter_add_card_filter_not _
  have hge_ef : ∀ t ∈ (quadSupport S).filter
      (fun s => siteParity hN s = 0), 2 ≤ siteDegree S t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have hge_of : ∀ t ∈ (quadSupport S).filter
      (fun s => siteParity hN s ≠ 0), 2 ≤ siteDegree S t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have even_two : ∀ (s : LayerSite N),
      s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0) →
      e = 3 → siteDegree S s = 2 := by
    intro s hs he
    refine siteDegree_eq_two_of_card_three hEvenSum ?_ hge_ef hs
    rw [← hedef]; exact he
  have odd_two : ∀ (s : LayerSite N),
      s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0) →
      o = 3 → siteDegree S s = 2 := by
    intro s hs ho
    refine siteDegree_eq_two_of_card_three hOddSum ?_ hge_of hs
    rw [← hodef]; exact ho
  have even_three : ∀ (s : LayerSite N),
      s ∈ (quadSupport S).filter (fun s => siteParity hN s = 0) →
      e = 2 → o = 3 → siteDegree S s = 3 := by
    intro s hs he ho
    refine siteDegree_eq_three_of_card_two hEvenSum ?_ hge_ef ?_ hs
    · rw [← hedef]; exact he
    · intro t ht
      have hle := siteDegree_le_odd_filter_card hN hN3 S
        (s := t) (Finset.mem_filter.mp ht).2
      rw [← hodef] at hle
      omega
  have odd_three : ∀ (s : LayerSite N),
      s ∈ (quadSupport S).filter (fun s => siteParity hN s ≠ 0) →
      o = 2 → e = 3 → siteDegree S s = 3 := by
    intro s hs ho he
    refine siteDegree_eq_three_of_card_two hOddSum ?_ hge_of ?_ hs
    · rw [← hodef]; exact ho
    · intro t ht
      have hle := siteDegree_le_even_filter_card hN hN3 S
        (s := t) (Finset.mem_filter.mp ht).2
      rw [← hedef] at hle
      omega
  have hcases : (e = 3 ∧ o = 3) ∨ (e = 2 ∧ o = 3) ∨ (e = 3 ∧ o = 2) := by
    interval_cases e <;> interval_cases o <;> omega
  rcases hcases with ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩
  · refine Or.inl ⟨by omega, ?_⟩
    intro s hs
    by_cases hpar : siteParity hN s = 0
    · exact even_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) he
    · exact odd_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) ho
  · have hef2 : ((quadSupport S).filter
        (fun s => siteParity hN s = 0)).card = 2 := by
      rw [← hedef]; exact he
    obtain ⟨a, b, hab, hef_eq⟩ := Finset.card_eq_two.mp hef2
    have ha_ef : a ∈ (quadSupport S).filter
        (fun s => siteParity hN s = 0) := by
      rw [hef_eq]; exact Finset.mem_insert_self a {b}
    have hb_ef : b ∈ (quadSupport S).filter
        (fun s => siteParity hN s = 0) := by
      rw [hef_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    refine Or.inr ⟨by omega, a, b, hab,
      (Finset.mem_filter.mp ha_ef).1, (Finset.mem_filter.mp hb_ef).1,
      even_three a ha_ef he ho, even_three b hb_ef he ho, ?_⟩
    intro s hs hsa hsb
    have hpar : siteParity hN s ≠ 0 := by
      by_contra hpar0
      have heq0 : siteParity hN s = 0 := hpar0
      have hs_ef : s ∈ (quadSupport S).filter
          (fun s => siteParity hN s = 0) :=
        Finset.mem_filter.mpr ⟨hs, heq0⟩
      rw [hef_eq] at hs_ef
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs_ef
      rcases hs_ef with h | h
      · exact hsa h
      · exact hsb h
    exact odd_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) ho
  · have hof2 : ((quadSupport S).filter
        (fun s => siteParity hN s ≠ 0)).card = 2 := by
      rw [← hodef]; exact ho
    obtain ⟨a, b, hab, hof_eq⟩ := Finset.card_eq_two.mp hof2
    have ha_of : a ∈ (quadSupport S).filter
        (fun s => siteParity hN s ≠ 0) := by
      rw [hof_eq]; exact Finset.mem_insert_self a {b}
    have hb_of : b ∈ (quadSupport S).filter
        (fun s => siteParity hN s ≠ 0) := by
      rw [hof_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    refine Or.inr ⟨by omega, a, b, hab,
      (Finset.mem_filter.mp ha_of).1, (Finset.mem_filter.mp hb_of).1,
      odd_three a ha_of ho he, odd_three b hb_of ho he, ?_⟩
    intro s hs hsa hsb
    have hpar : siteParity hN s = 0 := by
      by_contra hpar0
      have hs_of : s ∈ (quadSupport S).filter
          (fun s => siteParity hN s ≠ 0) :=
        Finset.mem_filter.mpr ⟨hs, hpar0⟩
      rw [hof_eq] at hs_of
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs_of
      rcases hs_of with h | h
      · exact hsa h
      · exact hsb h
    exact even_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) he

/-! ## Card-7 classification: the Θ(1,3,3) pattern -/

/-- Squeeze helper: three sites, degrees between `2` and
`3`, degrees summing to `7` — some site has degree
exactly `3` (otherwise every degree is `2` and the sum
is `6`). -/
theorem exists_siteDegree_three_of_sum_seven
    {S : Finset (LayerColumn N)} {F : Finset (LayerSite N)}
    (hsum : ∑ t ∈ F, siteDegree S t = 7) (hcard : F.card = 3)
    (hge : ∀ t ∈ F, 2 ≤ siteDegree S t)
    (hle : ∀ t ∈ F, siteDegree S t ≤ 3) :
    ∃ a ∈ F, siteDegree S a = 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  have h2 : ∀ t ∈ F, siteDegree S t = 2 := by
    intro t ht
    have hne := hcon t ht
    have hge' := hge t ht
    have hle' := hle t ht
    omega
  have hle : ∑ t ∈ F, siteDegree S t ≤ ∑ _t ∈ F, (2 : ℕ) :=
    Finset.sum_le_sum fun t ht => le_of_eq (h2 t ht)
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hcard] at hle
  omega

/-- Squeeze helper: three sites, degrees between `2` and
`3`, degrees summing to `7`, one site a hub of degree
`3` — every other site has degree exactly `2` (a second
degree-`3` site would push the side's sum past `7`). -/
theorem siteDegree_eq_two_of_sum_seven_of_hub
    {S : Finset (LayerColumn N)} {F : Finset (LayerSite N)}
    (hsum : ∑ t ∈ F, siteDegree S t = 7) (hcard : F.card = 3)
    (hge : ∀ t ∈ F, 2 ≤ siteDegree S t)
    (hle : ∀ t ∈ F, siteDegree S t ≤ 3)
    {a s : LayerSite N} (ha : a ∈ F) (hda : siteDegree S a = 3)
    (hs : s ∈ F) (hne : s ≠ a) : siteDegree S s = 2 := by
  classical
  have hsplit : ∑ t ∈ F, siteDegree S t
      = siteDegree S a + ∑ t ∈ F.erase a, siteDegree S t :=
    (Finset.add_sum_erase F (fun t => siteDegree S t) ha).symm
  have hcarderase : (F.erase a).card = 2 := by
    have h := Finset.card_erase_of_mem ha
    omega
  have hsumE : ∑ t ∈ F.erase a, siteDegree S t = 4 := by omega
  have hsE : s ∈ F.erase a := Finset.mem_erase.mpr ⟨hne, hs⟩
  have hsplitE : ∑ t ∈ F.erase a, siteDegree S t
      = siteDegree S s + ∑ t ∈ (F.erase a).erase s, siteDegree S t :=
    (Finset.add_sum_erase _ (fun t => siteDegree S t) hsE).symm
  have hcardEE : ((F.erase a).erase s).card = 1 := by
    have h := Finset.card_erase_of_mem hsE
    omega
  have hrem_lo : 2 ≤ ∑ t ∈ (F.erase a).erase s, siteDegree S t := by
    have hle : (∑ _t ∈ (F.erase a).erase s, (2 : ℕ))
        ≤ ∑ t ∈ (F.erase a).erase s, siteDegree S t :=
      Finset.sum_le_sum fun t ht =>
        hge t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hcardEE] at hle
  have hge_s : 2 ≤ siteDegree S s := hge s hs
  omega

/-- **Card-7 classification.** A weighted fully-shared
order-7 configuration whose distinct support has `7`
columns has the `Θ(1,3,3)` degree pattern: six support
sites, two hubs of distinct degree `3` (one on each
parity side), every other support site of degree `2`.
At card `7` every multiplicity is `1`, so weighted
sharing is distinct sharing; the parity classes are
forced to `(3,3)` by the pair injection (`7 ≤ e * o`
with `e, o ≤ 3`); and each side's degrees sum to `7`
over `3` sites of degree between `2` and `3`, forcing
`(3,2,2)` per side. The `C₇` pattern (seven sites, all
degrees `2`) and every degree-`4`-site or `(3,3,3,·)`
abstract type are excluded by the same squeeze. -/
theorem card_seven_classification (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hW : WFullyShared m) (hcard : (multSupport m).card = 7) :
    HasSevenPatternTheta133 (multSupport m) := by
  classical
  have hall : ∀ P ∈ multSupport m, m P = 1 :=
    eq_one_of_card_seven m hm7 hcard
  have hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s := by
    intro s hs
    have hw := hW s hs
    rwa [wSiteDegree_eq_siteDegree_of_all_one m hall s] at hw
  have hEvenSum : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0),
      siteDegree (multSupport m) s = 7 := by
    rw [sum_siteDegree_even_eq hN (multSupport m), hcard]
  have hOddSum : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0),
      siteDegree (multSupport m) s = 7 := by
    rw [sum_siteDegree_odd_eq hN (multSupport m), hcard]
  set e : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s = 0)).card with hedef
  set o : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s ≠ 0)).card with hodef
  have h2e : 2 * e ≤ 7 := by
    have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s = 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s = 0),
          siteDegree (multSupport m) s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have h2o : 2 * o ≤ 7 := by
    have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s ≠ 0), (2 : ℕ))
        ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
            (fun s => siteParity hN s ≠ 0),
          siteDegree (multSupport m) s :=
      Finset.sum_le_sum fun s hs => hDS s (Finset.mem_filter.mp hs).1
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
    omega
  have he3 : e ≤ 3 := by omega
  have ho3 : o ≤ 3 := by omega
  have hprod : 7 ≤ e * o := by
    have h := card_le_even_mul_odd hN hN3 (multSupport m)
    rwa [hcard, ← hedef, ← hodef] at h
  have hEO33 : e = 3 ∧ o = 3 := by
    interval_cases e <;> interval_cases o <;> omega
  obtain ⟨he, ho⟩ := hEO33
  have hEO : e + o = (quadSupport (multSupport m)).card :=
    Finset.card_filter_add_card_filter_not _
  have hsuppCard : (quadSupport (multSupport m)).card = 6 := by omega
  have hge_ef : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0),
      2 ≤ siteDegree (multSupport m) t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have hge_of : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0),
      2 ≤ siteDegree (multSupport m) t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have hle_ef : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0),
      siteDegree (multSupport m) t ≤ 3 := by
    intro t ht
    have hle := siteDegree_le_odd_filter_card hN hN3 (multSupport m)
      (s := t) (Finset.mem_filter.mp ht).2
    rw [← hodef] at hle
    omega
  have hle_of : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0),
      siteDegree (multSupport m) t ≤ 3 := by
    intro t ht
    have hle := siteDegree_le_even_filter_card hN hN3 (multSupport m)
      (s := t) (Finset.mem_filter.mp ht).2
    rw [← hedef] at hle
    omega
  have hefCard : ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0)).card = 3 := by
    rw [← hedef]; exact he
  have hofCard : ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0)).card = 3 := by
    rw [← hodef]; exact ho
  obtain ⟨a, ha_ef, hda⟩ := exists_siteDegree_three_of_sum_seven
    hEvenSum hefCard hge_ef hle_ef
  obtain ⟨b, hb_of, hdb⟩ := exists_siteDegree_three_of_sum_seven
    hOddSum hofCard hge_of hle_of
  have ha : a ∈ quadSupport (multSupport m) :=
    (Finset.mem_filter.mp ha_ef).1
  have hb : b ∈ quadSupport (multSupport m) :=
    (Finset.mem_filter.mp hb_of).1
  have hab : a ≠ b := by
    intro h
    have hpa : siteParity hN a = 0 := (Finset.mem_filter.mp ha_ef).2
    have hpb : siteParity hN b ≠ 0 := (Finset.mem_filter.mp hb_of).2
    rw [h] at hpa
    exact hpb hpa
  refine ⟨hsuppCard, a, b, hab, ha, hb, hda, hdb, ?_⟩
  intro s hs hsa hsb
  by_cases hpar : siteParity hN s = 0
  · exact siteDegree_eq_two_of_sum_seven_of_hub hEvenSum hefCard
      hge_ef hle_ef ha_ef hda (Finset.mem_filter.mpr ⟨hs, hpar⟩) hsa
  · exact siteDegree_eq_two_of_sum_seven_of_hub hOddSum hofCard
      hge_of hle_of hb_of hdb (Finset.mem_filter.mpr ⟨hs, hpar⟩) hsb

/-- **The `C₇` death at card 7.** A weighted fully-shared
order-7 configuration of distinct support card `7` does
not have the `C₇` pattern: its support has six sites, not
seven, and two of its sites have degree `3`, not `2`. -/
theorem not_hasSevenPatternC7_of_card_seven (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hW : WFullyShared m) (hcard : (multSupport m).card = 7) :
    ¬ HasSevenPatternC7 (multSupport m) := by
  have hTheta := card_seven_classification hN hN3 m hm7 hW hcard
  obtain ⟨h6, -⟩ := hTheta
  rintro ⟨hsupp7, -⟩
  omega

/-! ## The card-5 erasure death, card-6 and card-4
combined statements -/

/-- **The card-5 erasure death (the scoping's sharpest
claim-to-check, landed as predicted).** An order-7
configuration of distinct support card `5` has pattern
`(3,1,1,1,1)` or `(2,2,1,1,1)`, and it has a private
column — so its fiber dies by the private-column erasure
recursion. The mechanism is the squeeze: a card-5
configuration with no private column would be
distinctly shared, forcing card `4`, `6`, or `7` by
`card_eq_four_six_seven_of_distinctlyShared` — the
underlying 5-set is never primitive (B5-0), and no
exceptional weighted-fully-shared shape with no private
column exists at this order. -/
theorem card_five_erasure_death (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hcard : (multSupport m).card = 5) :
    ((∃ P₀ ∈ multSupport m, m P₀ = 3 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
    (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
      m P₀ = 2 ∧ m P₁ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1)) ∧
    HasPrivateColumn (multSupport m) :=
  ⟨patterns_of_card_five_seven m hm7 hcard,
    hasPrivateColumn_of_card_ne_four_six_seven hN hN3 m hm7
      (by omega) (by omega) (by omega)⟩

/-- **Card 6 combined.** An order-7 configuration of
distinct support card `6` has pattern `(2,1,1,1,1,1)`,
and its distinct support is a `C₆` pattern, a `Θ(2,2,2)`
pattern, or has a private column. The disjunction is the
point (B6-0's discipline): a weighted-fully-shared
support that is not distinctly shared — the `C4`+tail
wrap type, whose doubled tail column is private — dies
by ERASURE, a different certificate from the `C₆`/`Θ`
classification, and it is not silently absorbed into
either. LIVE: `(2,1,1,1,1,1)` on `C₆` and on `Θ(2,2,2)`,
in the distinctly-shared case. -/
theorem card_six_live_or_private (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hcard : (multSupport m).card = 6) :
    (∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∧
    (HasSixPatternC6 (multSupport m) ∨
      HasSixPatternTheta (multSupport m) ∨
      HasPrivateColumn (multSupport m)) := by
  classical
  refine ⟨pattern_of_card_six_seven m hm7 hcard, ?_⟩
  by_cases hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s
  · rcases card_six_distinct_classification hN hN3 (multSupport m)
      hcard hDS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr
      (hasPrivateColumn_of_not_distinctlyShared m hDS))

/-- At card `4` the distinct support is a primitive quad
or has a private column (the order-7 form of B6-0's
corrected card-4 conclusion). -/
theorem card_four_primitive_or_private_seven (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ)
    (hcard : (multSupport m).card = 4) :
    IsPrimitiveQuad (multSupport m) ∨
      HasPrivateColumn (multSupport m) := by
  classical
  by_cases hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s
  · refine Or.inl ⟨hcard, ?_⟩
    intro P hP s hsP
    have hs : s ∈ quadSupport (multSupport m) :=
      Finset.mem_biUnion.mpr ⟨P, hP, hsP⟩
    have hlt : 1 < ((multSupport m).filter
        (fun R => s ∈ colSites R)).card := hDS s hs
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
    by_cases haP : a ≠ P
    · exact ⟨a, (Finset.mem_filter.mp ha).1, haP,
        (Finset.mem_filter.mp ha).2⟩
    · have hbP : b ≠ P :=
        fun h => hab ((not_ne_iff.mp haP).trans h.symm)
      exact ⟨b, (Finset.mem_filter.mp hb).1, hbP,
        (Finset.mem_filter.mp hb).2⟩
  · exact Or.inr (hasPrivateColumn_of_not_distinctlyShared m hDS)

/-! ## Main theorem -/

/-- **Main: the seven-column channel characterization
(B7-0 headline).** A weighted fully-shared order-7
multiplicity function has distinct support of card `7`,
`6`, `5`, `4`, or at most `3`, and:
at card `7` all multiplicities are `1` and the support
has the `Θ(1,3,3)` degree pattern — LIVE (candidate);
at card `6` the pattern is `(2,1,1,1,1,1)` and the
support is a `C₆` pattern, a `Θ(2,2,2)` pattern, or has
a private column — LIVE on `C₆` and on `Θ(2,2,2)`;
at card `5` the pattern is `(3,1,1,1,1)` or
`(2,2,1,1,1)` with a private column — DIES-BY erasure;
at card `4` the pattern is `(4,1,1,1)`, `(3,2,1,1)`, or
`(2,2,2,1)` and the support is a primitive quad or has
a private column — LIVE on primitive quads;
at card at most `3` there is a private column (the
≤ 3-support factorization, owned). -/
theorem seven_column_channel_characterization (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm7 : ∑ P, m P = 7)
    (hW : WFullyShared m) :
    ((multSupport m).card = 7 ∧ (∀ P ∈ multSupport m, m P = 1) ∧
      HasSevenPatternTheta133 (multSupport m)) ∨
    ((multSupport m).card = 6 ∧
      (∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
        ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∧
      (HasSixPatternC6 (multSupport m) ∨
        HasSixPatternTheta (multSupport m) ∨
        HasPrivateColumn (multSupport m))) ∨
    ((multSupport m).card = 5 ∧
      ((∃ P₀ ∈ multSupport m, m P₀ = 3 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
        (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
          m P₀ = 2 ∧ m P₁ = 2 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1)) ∧
      HasPrivateColumn (multSupport m)) ∨
    ((multSupport m).card = 4 ∧
      ((∃ P₀ ∈ multSupport m, m P₀ = 4 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
        (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
          m P₀ = 3 ∧ m P₁ = 2 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1) ∨
        (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m,
          ∃ P₂ ∈ multSupport m, P₀ ≠ P₁ ∧ P₀ ≠ P₂ ∧ P₁ ≠ P₂ ∧
          m P₀ = 2 ∧ m P₁ = 2 ∧ m P₂ = 2 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → P ≠ P₂ →
            m P = 1)) ∧
      (IsPrimitiveQuad (multSupport m) ∨
        HasPrivateColumn (multSupport m))) ∨
    ((multSupport m).card ≤ 3 ∧ HasPrivateColumn (multSupport m)) := by
  classical
  have hk : (multSupport m).card ≤ 7 := card_multSupport_le_seven m hm7
  by_cases h7 : (multSupport m).card = 7
  · exact Or.inl ⟨h7, eq_one_of_card_seven m hm7 h7,
      card_seven_classification hN hN3 m hm7 hW h7⟩
  · by_cases h6 : (multSupport m).card = 6
    · exact Or.inr (Or.inl ⟨h6,
        card_six_live_or_private hN hN3 m hm7 h6⟩)
    · by_cases h5 : (multSupport m).card = 5
      · exact Or.inr (Or.inr (Or.inl ⟨h5,
          card_five_erasure_death hN hN3 m hm7 h5⟩))
      · by_cases h4 : (multSupport m).card = 4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4,
            patterns_of_card_four_seven m hm7 h4,
            card_four_primitive_or_private_seven hN hN3 m h4⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,
            hasPrivateColumn_of_card_ne_four_six_seven hN hN3 m hm7
              (by omega) (by omega) (by omega)⟩)))

/-! ## Wrap fence at `N = 4`

The characterization above is proved at general
(Even `N`, `3 ≤ N`); its proofs use no `5 ≤ N`
hypothesis. Instantiated at `N = 4` — where wrap
realizations of `C₆`-type supports occur — the lists are
the same: no new pattern, no new fence, exactly as at
β⁴/β⁵/β⁶. -/

/-- Wrap fence, card `6` at `N = 4`: an order-7
configuration of distinct support card `6` at `N = 4`
(including wrap realizations of `C₆`-type supports) has
pattern `(2,1,1,1,1,1)` and its support is a `C₆`
pattern, a `Θ(2,2,2)` pattern, or has a private column. -/
theorem wrap_card_six_at_four (m : LayerColumn 4 → ℕ)
    (hm7 : ∑ P, m P = 7) (hcard : (multSupport m).card = 6) :
    (∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∧
    (HasSixPatternC6 (multSupport m) ∨
      HasSixPatternTheta (multSupport m) ∨
      HasPrivateColumn (multSupport m)) :=
  card_six_live_or_private (⟨2, rfl⟩ : Even 4) (by norm_num) m hm7 hcard

/-- Wrap fence, card `7` at `N = 4`: a weighted
fully-shared order-7 configuration of distinct support
card `7` at `N = 4` has the `Θ(1,3,3)` degree pattern —
the same candidate channel as at general `N`. -/
theorem wrap_card_seven_at_four (m : LayerColumn 4 → ℕ)
    (hm7 : ∑ P, m P = 7) (hW : WFullyShared m)
    (hcard : (multSupport m).card = 7) :
    HasSevenPatternTheta133 (multSupport m) :=
  card_seven_classification (⟨2, rfl⟩ : Even 4) (by norm_num) m hm7
    hW hcard

end ThetLogos
