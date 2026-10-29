/-
# B6-0: order-6 selection (Brick A: support, parity bounds, and the
# distinctly-shared card squeeze)

Selection combinatorics for a multiplicity function `m` on columns
with total multiplicity `∑ P, m P = 6`. This brick introduces the
distinct support `multSupport m`, the weighted fully-shared
hypothesis `WFullyShared`, and the private-column predicate
`HasPrivateColumn`, and proves: the parity-side bounds for a
weighted fully-shared configuration, the support-card bound
`(multSupport m).card ≤ 6`, the squeeze that a distinctly-shared
support has card `4` or `6`, and that any other support card
forces a private column.

Fences (verbatim in spirit, binding on every statement in this
file): NO CLAIM. 0 parts of the Clay statement are closed by
this file. Dials 0/4. No sign is asserted for β⁶ or for any
other order. The general β⁶ sign remains FRONTIER. K-K6 is
pre-registered and belongs to B6-PROBE, not to this brick;
nothing here fires, discharges, or prejudges K-K6.

Correction note (against the β⁶ scoping): the scoping's card-4
line is corrected. Under WEIGHTED sharing a `(2,2,1,1)` support
need not be a primitive quad. Counterexample (exact, grid-realizable
at `N = 4`): columns over the sites `E0 = (0,0,0)`, `O0 = (1,0,0)`,
`O1 = (0,1,0)`, `E1 = (2,0,0)`, `O2 = (2,1,0)` (spatial triples),
with edges `E0–O0 ×1`, `E0–O1 ×2`, `E1–O0 ×1`, `E1–O2 ×2`; all
weighted degrees are `≥ 2`, while `O1` and `O2` have distinct
degree `1`. The eventual card-4 theorem (a later brick) therefore
concludes primitive-quad OR private-column at card 4, not
primitive-quad alone.
-/

import ThetLogos.OrderFiveSelection

open Finset

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## Definitions introduced by B6-0 -/

/-- The distinct support of a multiplicity function: the columns
of positive multiplicity. -/
def multSupport (m : LayerColumn N → ℕ) : Finset (LayerColumn N) :=
  Finset.univ.filter (fun P => m P ≠ 0)

/-- Weighted full sharing: every site of the distinct support is
read, counted with multiplicity, by columns of total multiplicity
at least `2`. -/
def WFullyShared (m : LayerColumn N → ℕ) : Prop :=
  ∀ s ∈ quadSupport (multSupport m), 2 ≤ wSiteDegree m s

/-- A private column of a set `S` of columns: a column of `S`
one of whose sites is read by no other column of `S`
(its site degree in `S` is exactly `1`). -/
def HasPrivateColumn (S : Finset (LayerColumn N)) : Prop :=
  ∃ P ∈ S, ∃ s ∈ colSites P, siteDegree S s = 1

/-! ## First lemmas -/

/-- Every site of the support of a set of columns has distinct
degree at least `1`: the column witnessing membership already
contributes. -/
theorem one_le_siteDegree_of_mem_quadSupport {S : Finset (LayerColumn N)}
    {s : LayerSite N} (hs : s ∈ quadSupport S) : 1 ≤ siteDegree S s := by
  obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs
  have hmem : P ∈ S.filter (fun P => s ∈ colSites P) :=
    Finset.mem_filter.mpr ⟨hP, hsP⟩
  exact Finset.card_pos.mpr ⟨P, hmem⟩

/-- If distinct sharing fails at some support site, that site
has distinct degree exactly `1` (it is at least `1` by
`one_le_siteDegree_of_mem_quadSupport`), and the column through
it is private. No total-multiplicity hypothesis is needed. -/
theorem hasPrivateColumn_of_not_distinctlyShared
    (m : LayerColumn N → ℕ)
    (hnd : ¬ ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s) :
    HasPrivateColumn (multSupport m) := by
  push_neg at hnd
  obtain ⟨s, hs, hlt⟩ := hnd
  have h1 : 1 ≤ siteDegree (multSupport m) s :=
    one_le_siteDegree_of_mem_quadSupport hs
  have heq : siteDegree (multSupport m) s = 1 := by omega
  obtain ⟨P, hP, hsP⟩ := Finset.mem_biUnion.mp hs
  exact ⟨P, hP, s, hsP, heq⟩

/-- The multiplicities over the distinct support sum to the
total multiplicity, here `6`: columns outside the support
contribute `0`. -/
theorem sum_multSupport (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) : ∑ P ∈ multSupport m, m P = 6 := by
  have h : ∑ P ∈ multSupport m, m P = ∑ P, m P := by
    unfold multSupport
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    by_cases hP : m P ≠ 0
    · simp [hP]
    · have hm0 : m P = 0 := not_ne_iff.mp hP
      simp [hP, hm0]
  rw [h, hm6]

/-- A column of the distinct support has multiplicity at
least `1`, by definition of the support. -/
theorem one_le_of_mem_multSupport (m : LayerColumn N → ℕ)
    {P : LayerColumn N} (hP : P ∈ multSupport m) : 1 ≤ m P := by
  have hne : m P ≠ 0 := by
    have hP' := hP
    unfold multSupport at hP'
    exact (Finset.mem_filter.mp hP').2
  omega

/-- Weighted parity bound, even side: in a weighted
fully-shared order-6 configuration, at most `3` even support
sites occur. Each such site carries weighted degree at least
`2`, and the even weighted degrees sum to `6`
(`sum_wSiteDegree_filter_eq`). -/
theorem even_filter_card_le_three (hN : Even N)
    (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (hW : WFullyShared m) :
    ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0)).card ≤ 3 := by
  classical
  have hmS : ∀ P : LayerColumn N, m P ≠ 0 → P ∈ multSupport m := by
    intro P hP
    unfold multSupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hP⟩
  have hEvenW : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0), wSiteDegree m s = 6 :=
    (sum_wSiteDegree_filter_eq m (multSupport m) hmS
      (fun P => (colSites_filter_parity_cards hN P).1)).trans
        (sum_multSupport m hm6)
  have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s = 0), (2 : ℕ))
      ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s = 0), wSiteDegree m s :=
    Finset.sum_le_sum fun s hs => hW s (Finset.mem_filter.mp hs).1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
  omega

/-- Weighted parity bound, odd side: the twin of
`even_filter_card_le_three` for the odd support sites. -/
theorem odd_filter_card_le_three (hN : Even N)
    (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (hW : WFullyShared m) :
    ((quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0)).card ≤ 3 := by
  classical
  have hmS : ∀ P : LayerColumn N, m P ≠ 0 → P ∈ multSupport m := by
    intro P hP
    unfold multSupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hP⟩
  have hOddW : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0), wSiteDegree m s = 6 :=
    (sum_wSiteDegree_filter_eq m (multSupport m) hmS
      (fun P => (colSites_filter_parity_cards hN P).2)).trans
        (sum_multSupport m hm6)
  have h1 : (∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s ≠ 0), (2 : ℕ))
      ≤ ∑ s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s ≠ 0), wSiteDegree m s :=
    Finset.sum_le_sum fun s hs => hW s (Finset.mem_filter.mp hs).1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] at h1
  omega

/-- The distinct support of an order-6 multiplicity function
has at most `6` columns: each contributes at least `1` to the
total multiplicity `6`. -/
theorem card_multSupport_le_six (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) : (multSupport m).card ≤ 6 := by
  have h1 : (∑ _P ∈ multSupport m, (1 : ℕ))
      ≤ ∑ P ∈ multSupport m, m P :=
    Finset.sum_le_sum fun P hP => one_le_of_mem_multSupport m hP
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_one,
    sum_multSupport m hm6] at h1
  exact h1

/-- **The distinctly-shared squeeze.** If every support site
of an order-6 multiplicity function has distinct degree at
least `2`, the distinct support has card `4` or `6`. The
parity balances give `2e ≤ card` and `2o ≤ card` for the even
and odd support-site counts `e, o`; the support bound gives
`e, o ≤ 3`; the pair injection gives `card ≤ e * o`; and the
support is nonempty since the total multiplicity is `6`.
The interval squeeze on `e, o` then leaves only `4` and `6`. -/
theorem card_eq_four_or_six_of_distinctlyShared (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s) :
    (multSupport m).card = 4 ∨ (multSupport m).card = 6 := by
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
  have hk6 : (multSupport m).card ≤ 6 := card_multSupport_le_six m hm6
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
    have hsum := sum_multSupport m hm6
    rw [hempty, Finset.sum_empty] at hsum
    omega
  interval_cases e <;> interval_cases o <;> omega

/-- If the distinct support of an order-6 multiplicity
function has card neither `4` nor `6`, it has a private
column: otherwise distinct sharing would force card `4`
or `6` by `card_eq_four_or_six_of_distinctlyShared`. -/
theorem hasPrivateColumn_of_card_ne (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (h4 : (multSupport m).card ≠ 4) (h6 : (multSupport m).card ≠ 6) :
    HasPrivateColumn (multSupport m) := by
  classical
  by_cases hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s
  · rcases card_eq_four_or_six_of_distinctlyShared hN hN3 m hm6 hDS
      with h | h
    · exact absurd h h4
    · exact absurd h h6
  · exact hasPrivateColumn_of_not_distinctlyShared m hDS

/-- Helper: if every member of `T` has multiplicity at least
`1` and the multiplicities over `T` sum to exactly `T.card`,
then every member has multiplicity exactly `1` — a member of
multiplicity at least `2` would push the sum past the card,
since the remaining members still contribute at least `1`
each. -/
theorem eq_one_of_sum_eq_card {m : LayerColumn N → ℕ}
    {T : Finset (LayerColumn N)} (h1 : ∀ P ∈ T, 1 ≤ m P)
    (hsum : ∑ P ∈ T, m P = T.card) {P : LayerColumn N}
    (hP : P ∈ T) : m P = 1 := by
  classical
  by_contra hne
  have h1P : 1 ≤ m P := h1 P hP
  have hsplit : ∑ Q ∈ T, m Q = m P + ∑ Q ∈ T.erase P, m Q :=
    (Finset.add_sum_erase T m hP).symm
  have herase : (T.erase P).card ≤ ∑ Q ∈ T.erase P, m Q := by
    have hle : (∑ _Q ∈ T.erase P, (1 : ℕ)) ≤ ∑ Q ∈ T.erase P, m Q :=
      Finset.sum_le_sum fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
  have hcard : (T.erase P).card = T.card - 1 :=
    Finset.card_erase_of_mem hP
  omega

/-- Card-5 pattern: an order-6 multiplicity function whose
distinct support has `5` columns has pattern `(2,1,1,1,1)`:
one column of multiplicity `2` and the rest of multiplicity
`1`. -/
theorem pattern_of_card_five (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) (hcard : (multSupport m).card = 5) :
    ∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1 := by
  classical
  have hsumS : ∑ P ∈ multSupport m, m P = 6 := sum_multSupport m hm6
  have h1 : ∀ P ∈ multSupport m, 1 ≤ m P :=
    fun P hP => one_le_of_mem_multSupport m hP
  obtain ⟨P₀, hP₀S, hP₀ge⟩ : ∃ P₀ ∈ multSupport m, 2 ≤ m P₀ := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ P ∈ multSupport m, m P
        ≤ ∑ _P ∈ multSupport m, (1 : ℕ) :=
      Finset.sum_le_sum fun P hP => by
        have hlt : m P < 2 := hcon P hP
        omega
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
    omega
  have hsplit : ∑ P ∈ multSupport m, m P
      = m P₀ + ∑ P ∈ (multSupport m).erase P₀, m P :=
    (Finset.add_sum_erase _ m hP₀S).symm
  have herase : ((multSupport m).erase P₀).card
      ≤ ∑ P ∈ (multSupport m).erase P₀, m P := by
    have hle : (∑ _Q ∈ (multSupport m).erase P₀, (1 : ℕ))
        ≤ ∑ Q ∈ (multSupport m).erase P₀, m Q :=
      Finset.sum_le_sum fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
  have hcarderase : ((multSupport m).erase P₀).card = 4 := by
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

/-- Card-4 patterns: an order-6 multiplicity function whose
distinct support has `4` columns has pattern `(3,1,1,1)` or
`(2,2,1,1)`. -/
theorem patterns_of_card_four (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) (hcard : (multSupport m).card = 4) :
    (∃ P₀ ∈ multSupport m, m P₀ = 3 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
    (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
      m P₀ = 2 ∧ m P₁ = 2 ∧
      ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1) := by
  classical
  have hsumS : ∑ P ∈ multSupport m, m P = 6 := sum_multSupport m hm6
  have h1 : ∀ P ∈ multSupport m, 1 ≤ m P :=
    fun P hP => one_le_of_mem_multSupport m hP
  obtain ⟨P₀, hP₀S, hP₀ge⟩ : ∃ P₀ ∈ multSupport m, 2 ≤ m P₀ := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ P ∈ multSupport m, m P
        ≤ ∑ _P ∈ multSupport m, (1 : ℕ) :=
      Finset.sum_le_sum fun P hP => by
        have hlt : m P < 2 := hcon P hP
        omega
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
    omega
  have hsplit : ∑ P ∈ multSupport m, m P
      = m P₀ + ∑ P ∈ (multSupport m).erase P₀, m P :=
    (Finset.add_sum_erase _ m hP₀S).symm
  have herase : ((multSupport m).erase P₀).card
      ≤ ∑ P ∈ (multSupport m).erase P₀, m P := by
    have hle : (∑ _Q ∈ (multSupport m).erase P₀, (1 : ℕ))
        ≤ ∑ Q ∈ (multSupport m).erase P₀, m Q :=
      Finset.sum_le_sum fun Q hQ => h1 Q (Finset.mem_of_mem_erase hQ)
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
  have hcarderase : ((multSupport m).erase P₀).card = 3 := by
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
    have hsumT : ∑ P ∈ (multSupport m).erase P₀, m P = 4 := by omega
    have h1T : ∀ P ∈ (multSupport m).erase P₀, 1 ≤ m P :=
      fun P hP => h1 P (Finset.mem_of_mem_erase hP)
    obtain ⟨P₁, hP₁T, hP₁ge⟩ :
        ∃ P₁ ∈ (multSupport m).erase P₀, 2 ≤ m P₁ := by
      by_contra hcon
      push_neg at hcon
      have hle : ∑ P ∈ (multSupport m).erase P₀, m P
          ≤ ∑ _P ∈ (multSupport m).erase P₀, (1 : ℕ) :=
        Finset.sum_le_sum fun P hP => by
          have hlt : m P < 2 := hcon P hP
          omega
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
      omega
    have hP₁S : P₁ ∈ multSupport m := Finset.mem_of_mem_erase hP₁T
    have hne₁₀ : P₁ ≠ P₀ := (Finset.mem_erase.mp hP₁T).1
    have hsplitT : ∑ P ∈ (multSupport m).erase P₀, m P
        = m P₁ + ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P :=
      (Finset.add_sum_erase _ m hP₁T).symm
    have heraseU : (((multSupport m).erase P₀).erase P₁).card
        ≤ ∑ P ∈ ((multSupport m).erase P₀).erase P₁, m P := by
      have hle : (∑ _Q ∈ ((multSupport m).erase P₀).erase P₁, (1 : ℕ))
          ≤ ∑ Q ∈ ((multSupport m).erase P₀).erase P₁, m Q :=
        Finset.sum_le_sum fun Q hQ => h1T Q (Finset.mem_of_mem_erase hQ)
      rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hle
    have hcardU : (((multSupport m).erase P₀).erase P₁).card = 2 := by
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

/-! ## Brick C: patterns at card 6, opposite-parity bounds, and the
main six-column channel characterization -/

/-- The `C₆` pattern at card `6`: the support reads six sites,
each of distinct degree exactly `2`. -/
def HasSixPatternC6 (S : Finset (LayerColumn N)) : Prop :=
  (quadSupport S).card = 6 ∧ ∀ s ∈ quadSupport S, siteDegree S s = 2

/-- The `Θ(2,2,2)`-type pattern at card `6`: the support reads
five sites, two hubs `a, b` of distinct degree `3`, and every
other support site of distinct degree `2`. -/
def HasSixPatternTheta (S : Finset (LayerColumn N)) : Prop :=
  (quadSupport S).card = 5 ∧
  ∃ a b, a ≠ b ∧ a ∈ quadSupport S ∧ b ∈ quadSupport S ∧
    siteDegree S a = 3 ∧ siteDegree S b = 3 ∧
    ∀ s ∈ quadSupport S, s ≠ a → s ≠ b → siteDegree S s = 2

/-- Opposite-parity degree bound, even site: the distinct
degree of an even site `s` is at most the number of odd
support sites. The columns through `s` inject into the odd
support sites by sending each column to its other site
(the site of the column opposite to `s`), and a column is
determined by its two sites (`colSites_eq_imp`). -/
theorem siteDegree_le_odd_filter_card (hN : Even N) (hN3 : 3 ≤ N)
    (S : Finset (LayerColumn N)) {s : LayerSite N}
    (hs0 : siteParity hN s = 0) :
    siteDegree S s ≤
      ((quadSupport S).filter (fun t => siteParity hN t ≠ 0)).card := by
  classical
  unfold siteDegree
  refine Finset.card_le_card_of_injOn
    (fun P => if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1) ?_ ?_
  · intro P hP
    obtain ⟨hPS, hsP⟩ := Finset.mem_filter.mp hP
    have hf_mem : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ∈ colSites P := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase]; exact mem_colSites.mpr (Or.inr rfl)
      · rw [if_neg hcase]; exact mem_colSites.mpr (Or.inl rfl)
    have hf_ne : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ≠ s := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase, ← hcase]
        exact layerShift_ne_self hN P.2.1 P.2.2 P.1
      · rw [if_neg hcase]; exact hcase
    have hf_par_ne : siteParity hN
          (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ≠ siteParity hN s := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase]
        have hpp := siteParity_head_ne hN P
        rw [show siteParity hN P.1 = siteParity hN s from
          congrArg (siteParity hN) hcase] at hpp
        exact hpp
      · rw [if_neg hcase]
        rcases mem_colSites.mp hsP with h | h
        · exact absurd h.symm hcase
        · have hps : siteParity hN s
              = siteParity hN (layerShift P.2.1 P.2.2 P.1) :=
            congrArg (siteParity hN) h
          rw [hps]
          exact Ne.symm (siteParity_head_ne hN P)
    have hf_par : siteParity hN
          (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1) ≠ 0 :=
      fun hc => hf_par_ne (hc.trans hs0.symm)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨P, hPS, hf_mem⟩, hf_par⟩
  · intro P hP Q hQ hf
    have hset : ∀ R ∈ S.filter (fun P => s ∈ colSites P),
        ({s, if R.1 = s then layerShift R.2.1 R.2.2 R.1 else R.1}
          : Finset (LayerSite N)) = colSites R := by
      intro R hR
      obtain ⟨-, hsR⟩ := Finset.mem_filter.mp hR
      by_cases hcase : R.1 = s
      · rw [if_pos hcase, ← hcase]
        rfl
      · rw [if_neg hcase]
        rcases mem_colSites.mp hsR with h | h
        · exact absurd h.symm hcase
        · rw [h]
          show ({layerShift R.2.1 R.2.2 R.1, R.1} : Finset (LayerSite N))
            = {R.1, layerShift R.2.1 R.2.2 R.1}
          exact Finset.pair_comm _ _
    have hf' : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        = (if Q.1 = s then layerShift Q.2.1 Q.2.2 Q.1 else Q.1) := hf
    have hcol : colSites P = colSites Q := by
      calc colSites P
          = {s, if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1} :=
            (hset P hP).symm
        _ = {s, if Q.1 = s then layerShift Q.2.1 Q.2.2 Q.1 else Q.1} := by
            rw [hf']
        _ = colSites Q := hset Q hQ
    exact colSites_eq_imp hN hN3 hcol

/-- Opposite-parity degree bound, odd site: the twin of
`siteDegree_le_odd_filter_card`. The distinct degree of an
odd site `s` is at most the number of even support sites. -/
theorem siteDegree_le_even_filter_card (hN : Even N) (hN3 : 3 ≤ N)
    (S : Finset (LayerColumn N)) {s : LayerSite N}
    (hs0 : siteParity hN s ≠ 0) :
    siteDegree S s ≤
      ((quadSupport S).filter (fun t => siteParity hN t = 0)).card := by
  classical
  unfold siteDegree
  refine Finset.card_le_card_of_injOn
    (fun P => if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1) ?_ ?_
  · intro P hP
    obtain ⟨hPS, hsP⟩ := Finset.mem_filter.mp hP
    have hf_mem : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ∈ colSites P := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase]; exact mem_colSites.mpr (Or.inr rfl)
      · rw [if_neg hcase]; exact mem_colSites.mpr (Or.inl rfl)
    have hf_ne : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ≠ s := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase, ← hcase]
        exact layerShift_ne_self hN P.2.1 P.2.2 P.1
      · rw [if_neg hcase]; exact hcase
    have hf_par_ne : siteParity hN
          (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        ≠ siteParity hN s := by
      by_cases hcase : P.1 = s
      · rw [if_pos hcase]
        have hpp := siteParity_head_ne hN P
        rw [show siteParity hN P.1 = siteParity hN s from
          congrArg (siteParity hN) hcase] at hpp
        exact hpp
      · rw [if_neg hcase]
        rcases mem_colSites.mp hsP with h | h
        · exact absurd h.symm hcase
        · have hps : siteParity hN s
              = siteParity hN (layerShift P.2.1 P.2.2 P.1) :=
            congrArg (siteParity hN) h
          rw [hps]
          exact Ne.symm (siteParity_head_ne hN P)
    have hf_par : siteParity hN
          (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1) = 0 := by
      rcases zmod_two_eq_zero_or_one (siteParity hN
          (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)) with h0 | h1
      · exact h0
      · exfalso
        rcases zmod_two_eq_zero_or_one (siteParity hN s) with g0 | g1
        · exact hs0 g0
        · exact hf_par_ne (h1.trans g1.symm)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨P, hPS, hf_mem⟩, hf_par⟩
  · intro P hP Q hQ hf
    have hset : ∀ R ∈ S.filter (fun P => s ∈ colSites P),
        ({s, if R.1 = s then layerShift R.2.1 R.2.2 R.1 else R.1}
          : Finset (LayerSite N)) = colSites R := by
      intro R hR
      obtain ⟨-, hsR⟩ := Finset.mem_filter.mp hR
      by_cases hcase : R.1 = s
      · rw [if_pos hcase, ← hcase]
        rfl
      · rw [if_neg hcase]
        rcases mem_colSites.mp hsR with h | h
        · exact absurd h.symm hcase
        · rw [h]
          show ({layerShift R.2.1 R.2.2 R.1, R.1} : Finset (LayerSite N))
            = {R.1, layerShift R.2.1 R.2.2 R.1}
          exact Finset.pair_comm _ _
    have hf' : (if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1)
        = (if Q.1 = s then layerShift Q.2.1 Q.2.2 Q.1 else Q.1) := hf
    have hcol : colSites P = colSites Q := by
      calc colSites P
          = {s, if P.1 = s then layerShift P.2.1 P.2.2 P.1 else P.1} :=
            (hset P hP).symm
        _ = {s, if Q.1 = s then layerShift Q.2.1 Q.2.2 Q.1 else Q.1} := by
            rw [hf']
        _ = colSites Q := hset Q hQ
    exact colSites_eq_imp hN hN3 hcol

/-- Squeeze helper: three sites, degrees at least `2`,
degrees summing to `6` — every degree is exactly `2`. -/
theorem siteDegree_eq_two_of_card_three {S : Finset (LayerColumn N)}
    {F : Finset (LayerSite N)}
    (hsum : ∑ t ∈ F, siteDegree S t = 6) (hcard : F.card = 3)
    (hge : ∀ t ∈ F, 2 ≤ siteDegree S t) {s : LayerSite N}
    (hs : s ∈ F) : siteDegree S s = 2 := by
  classical
  have hsplit : ∑ t ∈ F, siteDegree S t
      = siteDegree S s + ∑ t ∈ F.erase s, siteDegree S t :=
    (Finset.add_sum_erase F (fun t => siteDegree S t) hs).symm
  have herase : (F.erase s).card * 2
      ≤ ∑ t ∈ F.erase s, siteDegree S t := by
    have hle : (∑ _t ∈ F.erase s, (2 : ℕ))
        ≤ ∑ t ∈ F.erase s, siteDegree S t :=
      Finset.sum_le_sum fun t ht =>
        hge t (Finset.mem_of_mem_erase ht)
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hle
  have hcarderase : (F.erase s).card = 2 := by
    have h := Finset.card_erase_of_mem hs
    omega
  have hge_s : 2 ≤ siteDegree S s := hge s hs
  omega

/-- Squeeze helper: two sites, degrees between `2` and `3`,
degrees summing to `6` — every degree is exactly `3`. -/
theorem siteDegree_eq_three_of_card_two {S : Finset (LayerColumn N)}
    {F : Finset (LayerSite N)}
    (hsum : ∑ t ∈ F, siteDegree S t = 6) (hcard : F.card = 2)
    (hge : ∀ t ∈ F, 2 ≤ siteDegree S t)
    (hle : ∀ t ∈ F, siteDegree S t ≤ 3) {s : LayerSite N}
    (hs : s ∈ F) : siteDegree S s = 3 := by
  classical
  have hsplit : ∑ t ∈ F, siteDegree S t
      = siteDegree S s + ∑ t ∈ F.erase s, siteDegree S t :=
    (Finset.add_sum_erase F (fun t => siteDegree S t) hs).symm
  have herase : ∑ t ∈ F.erase s, siteDegree S t
      ≤ (F.erase s).card * 3 := by
    have hle' : ∑ t ∈ F.erase s, siteDegree S t
        ≤ (∑ _t ∈ F.erase s, (3 : ℕ)) :=
      Finset.sum_le_sum fun t ht =>
        hle t (Finset.mem_of_mem_erase ht)
    rwa [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hle'
  have hcarderase : (F.erase s).card = 1 := by
    have h := Finset.card_erase_of_mem hs
    omega
  have hle_s : siteDegree S s ≤ 3 := hle s hs
  omega

/-- At card `6` every column of the distinct support has
multiplicity exactly `1`: the multiplicities sum to `6`
over a `6`-element support of multiplicities at least `1`. -/
theorem eq_one_of_card_six (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) (hcard : (multSupport m).card = 6) :
    ∀ P ∈ multSupport m, m P = 1 := by
  intro P hP
  apply eq_one_of_sum_eq_card
    (fun Q hQ => one_le_of_mem_multSupport m hQ) _ hP
  rw [sum_multSupport m hm6, hcard]

/-- At card `6` the weighted site degree agrees with the
distinct site degree on the support: every contributing
column has multiplicity `1`, and columns outside the
support contribute `0` to the weighted degree. -/
theorem wSiteDegree_eq_siteDegree_of_card_six (m : LayerColumn N → ℕ)
    (hm6 : ∑ P, m P = 6) (hcard : (multSupport m).card = 6)
    (s : LayerSite N) :
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
            eq_one_of_card_six m hm6 hcard P
              (Finset.mem_filter.mp hP).1
      _ = ((multSupport m).filter (fun P => s ∈ colSites P)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  unfold wSiteDegree siteDegree
  rw [← hsum, hone]

/-- **Card-6 classification.** A weighted fully-shared
order-6 configuration whose distinct support has `6`
columns is a `C₆` pattern (six sites, all of distinct
degree `2`) or a `Θ` pattern (five sites, two hubs of
distinct degree `3`, the rest of degree `2`). The parity
class sizes `e, o` satisfy `e, o ≤ 3` and `6 ≤ e * o`,
leaving `(3,3)`, `(2,3)`, `(3,2)`; the class degree sums
are both `6`, and the squeeze helpers finish each case. -/
theorem card_six_classification (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (hW : WFullyShared m) (hcard : (multSupport m).card = 6) :
    HasSixPatternC6 (multSupport m) ∨
      HasSixPatternTheta (multSupport m) := by
  classical
  have hDS : ∀ s ∈ quadSupport (multSupport m),
      2 ≤ siteDegree (multSupport m) s := by
    intro s hs
    have hw := hW s hs
    rwa [wSiteDegree_eq_siteDegree_of_card_six m hm6 hcard s] at hw
  have hEvenSum : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0), siteDegree (multSupport m) s
      = 6 := by
    rw [sum_siteDegree_even_eq hN (multSupport m), hcard]
  have hOddSum : ∑ s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0), siteDegree (multSupport m) s
      = 6 := by
    rw [sum_siteDegree_odd_eq hN (multSupport m), hcard]
  set e : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s = 0)).card with hedef
  set o : ℕ := ((quadSupport (multSupport m)).filter
    (fun s => siteParity hN s ≠ 0)).card with hodef
  have he3 : e ≤ 3 := by
    rw [hedef]; exact even_filter_card_le_three hN m hm6 hW
  have ho3 : o ≤ 3 := by
    rw [hodef]; exact odd_filter_card_le_three hN m hm6 hW
  have hprod : 6 ≤ e * o := by
    have h := card_le_even_mul_odd hN hN3 (multSupport m)
    rwa [hcard, ← hedef, ← hodef] at h
  have hEO : e + o = (quadSupport (multSupport m)).card :=
    Finset.card_filter_add_card_filter_not _
  have hge_ef : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s = 0), 2 ≤ siteDegree (multSupport m) t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have hge_of : ∀ t ∈ (quadSupport (multSupport m)).filter
      (fun s => siteParity hN s ≠ 0), 2 ≤ siteDegree (multSupport m) t :=
    fun t ht => hDS t (Finset.mem_filter.mp ht).1
  have even_two : ∀ (s : LayerSite N),
      s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0) → e = 3 →
      siteDegree (multSupport m) s = 2 := by
    intro s hs he
    refine siteDegree_eq_two_of_card_three hEvenSum ?_ hge_ef hs
    rw [← hedef]; exact he
  have odd_two : ∀ (s : LayerSite N),
      s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0) → o = 3 →
      siteDegree (multSupport m) s = 2 := by
    intro s hs ho
    refine siteDegree_eq_two_of_card_three hOddSum ?_ hge_of hs
    rw [← hodef]; exact ho
  have even_three : ∀ (s : LayerSite N),
      s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0) → e = 2 → o = 3 →
      siteDegree (multSupport m) s = 3 := by
    intro s hs he ho
    refine siteDegree_eq_three_of_card_two hEvenSum ?_ hge_ef ?_ hs
    · rw [← hedef]; exact he
    · intro t ht
      have hle := siteDegree_le_odd_filter_card hN hN3 (multSupport m)
        (s := t) (Finset.mem_filter.mp ht).2
      rw [← hodef] at hle
      omega
  have odd_three : ∀ (s : LayerSite N),
      s ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0) → o = 2 → e = 3 →
      siteDegree (multSupport m) s = 3 := by
    intro s hs ho he
    refine siteDegree_eq_three_of_card_two hOddSum ?_ hge_of ?_ hs
    · rw [← hodef]; exact ho
    · intro t ht
      have hle := siteDegree_le_even_filter_card hN hN3 (multSupport m)
        (s := t) (Finset.mem_filter.mp ht).2
      rw [← hedef] at hle
      omega
  have hcases : (e = 3 ∧ o = 3) ∨ (e = 2 ∧ o = 3) ∨ (e = 3 ∧ o = 2) := by
    interval_cases e <;> interval_cases o <;> omega
  rcases hcases with ⟨he, ho⟩ | ⟨he, ho⟩ | ⟨he, ho⟩
  · -- (3,3): six sites, all of degree 2 — the C₆ pattern.
    refine Or.inl ⟨by omega, ?_⟩
    intro s hs
    by_cases hpar : siteParity hN s = 0
    · exact even_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) he
    · exact odd_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) ho
  · -- (2,3): five sites, even hubs of degree 3 — the Θ pattern.
    have hef2 : ((quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0)).card = 2 := by
      rw [← hedef]; exact he
    obtain ⟨a, b, hab, hef_eq⟩ := Finset.card_eq_two.mp hef2
    have ha_ef : a ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s = 0) := by
      rw [hef_eq]; exact Finset.mem_insert_self a {b}
    have hb_ef : b ∈ (quadSupport (multSupport m)).filter
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
      have hs_ef : s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s = 0) :=
        Finset.mem_filter.mpr ⟨hs, heq0⟩
      rw [hef_eq] at hs_ef
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs_ef
      rcases hs_ef with h | h
      · exact hsa h
      · exact hsb h
    exact odd_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) ho
  · -- (3,2): five sites, odd hubs of degree 3 — the Θ pattern.
    have hof2 : ((quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0)).card = 2 := by
      rw [← hodef]; exact ho
    obtain ⟨a, b, hab, hof_eq⟩ := Finset.card_eq_two.mp hof2
    have ha_of : a ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0) := by
      rw [hof_eq]; exact Finset.mem_insert_self a {b}
    have hb_of : b ∈ (quadSupport (multSupport m)).filter
        (fun s => siteParity hN s ≠ 0) := by
      rw [hof_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    refine Or.inr ⟨by omega, a, b, hab,
      (Finset.mem_filter.mp ha_of).1, (Finset.mem_filter.mp hb_of).1,
      odd_three a ha_of ho he, odd_three b hb_of ho he, ?_⟩
    intro s hs hsa hsb
    have hpar : siteParity hN s = 0 := by
      by_contra hpar0
      have hs_of : s ∈ (quadSupport (multSupport m)).filter
          (fun s => siteParity hN s ≠ 0) :=
        Finset.mem_filter.mpr ⟨hs, hpar0⟩
      rw [hof_eq] at hs_of
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs_of
      rcases hs_of with h | h
      · exact hsa h
      · exact hsb h
    exact even_two s (Finset.mem_filter.mpr ⟨hs, hpar⟩) he

/-- At card `4` the distinct support is a primitive quad or
has a private column: if distinct sharing holds everywhere,
the sharing property is exactly the primitive-quad sharing
clause; if it fails somewhere, that site's column is
private. (The corrected card-4 conclusion: under weighted
sharing, `(2,2,1,1)` need not be primitive.) -/
theorem card_four_primitive_or_private (hN : Even N) (hN3 : 3 ≤ N)
    (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
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

/-- **Main: the six-column channel characterization.**
A weighted fully-shared order-6 multiplicity function has
distinct support of card `6`, `5`, `4`, or at most `3`, and:
at card `6` all multiplicities are `1` and the support is a
`C₆` or `Θ` pattern; at card `5` the pattern is `(2,1,1,1,1)`
with a private column; at card `4` the pattern is `(3,1,1,1)`
or `(2,2,1,1)` and the support is a primitive quad or has a
private column; at card at most `3` there is a private
column. -/
theorem six_column_channel_characterization (hN : Even N)
    (hN3 : 3 ≤ N) (m : LayerColumn N → ℕ) (hm6 : ∑ P, m P = 6)
    (hW : WFullyShared m) :
    ((multSupport m).card = 6 ∧ (∀ P ∈ multSupport m, m P = 1) ∧
      (HasSixPatternC6 (multSupport m) ∨
        HasSixPatternTheta (multSupport m))) ∨
    ((multSupport m).card = 5 ∧
      (∃ P₀ ∈ multSupport m, m P₀ = 2 ∧
        ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∧
      HasPrivateColumn (multSupport m)) ∨
    ((multSupport m).card = 4 ∧
      ((∃ P₀ ∈ multSupport m, m P₀ = 3 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → m P = 1) ∨
        (∃ P₀ ∈ multSupport m, ∃ P₁ ∈ multSupport m, P₀ ≠ P₁ ∧
          m P₀ = 2 ∧ m P₁ = 2 ∧
          ∀ P ∈ multSupport m, P ≠ P₀ → P ≠ P₁ → m P = 1)) ∧
      (IsPrimitiveQuad (multSupport m) ∨
        HasPrivateColumn (multSupport m))) ∨
    ((multSupport m).card ≤ 3 ∧ HasPrivateColumn (multSupport m)) := by
  classical
  have hk : (multSupport m).card ≤ 6 := card_multSupport_le_six m hm6
  by_cases h6 : (multSupport m).card = 6
  · exact Or.inl ⟨h6, eq_one_of_card_six m hm6 h6,
      card_six_classification hN hN3 m hm6 hW h6⟩
  · by_cases h5 : (multSupport m).card = 5
    · exact Or.inr (Or.inl ⟨h5, pattern_of_card_five m hm6 h5,
        hasPrivateColumn_of_card_ne hN hN3 m hm6 (by omega) (by omega)⟩)
    · by_cases h4 : (multSupport m).card = 4
      · exact Or.inr (Or.inr (Or.inl ⟨h4,
          patterns_of_card_four m hm6 h4,
          card_four_primitive_or_private hN hN3 m hm6 h4⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,
          hasPrivateColumn_of_card_ne hN hN3 m hm6 (by omega)
            (by omega)⟩))

end ThetLogos
