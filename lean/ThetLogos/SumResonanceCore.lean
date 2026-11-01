import Mathlib.Tactic
import ThetLogos.SumResonance

/-!
# Sum resonance: the shared-gap core (RES-1)

Headline brick of the resonance line, per the coordinator pack
`routeb-general-scratch/pack-res-1.md` and the ratified scoping memo
`routeb-general-scratch/scoping-resonance-2026-10-30.md` (§2(a), §3).
RES-0's vocabulary (`ThetLogos.SumResonance`: `collCount`, `diffCount`,
`diffRange`, `collCount3`, …) is cited, never forked.

**Content (the memo's §2(a), statements registered verbatim in
substance).**
- (a1) The collision inner-product identity:
  `collCount a b = ∑ d ∈ diffRange a, diffCount a d * diffCount b d`.
- (a2) The shared-gap criterion, sharp, with its equality case:
  `collCount a b = m * n` iff
  `diffCount a 0 * diffCount b 0 = m * n` (the memo's exact conjunct
  form) AND no `d ≠ 0` has `diffCount a d > 0 ∧ diffCount b d > 0`;
  plus the corollary under within-factor distinctness: a nontrivial
  coincidence exists iff the two gap sets share a nonzero element.
- (a3) The ternary identity: `collCount3 a b c` as the finite sum
  over difference triples `(d, e, f)` in the three difference ranges
  with `d + e + f = 0` of `diffCount a d * diffCount b e *
  diffCount c f`.

(a4) is RES-2b's optional content — NOT this brick.

**K-RES-1 (pre-registered framing kill), noted on the face:** raw
coincidence counts at any seat are bookkeeping; the theorems of this
line are the criterion and the identity, never the raw counts. The
count band for this brick is 28–42 strict (memo §5, RES-1: M).

NO CLAIM beyond the abstract finite-ℚ statements proved below.
"Harmonic / sympathetic / octave" name only the pinned mathematics
of the memo's §2: no acoustics, no physical-world claim, no measured
number derived or fitted. Dial 1 untouched; dials 0/4.
-/

namespace ThetLogos

open Finset

variable {m n l : ℕ}

-- ============================================================================
-- Support API for `diffCount` / `diffRange`
-- ============================================================================

/-- Support characterisation: `diffCount a d` is positive iff `d`
lies in the difference range of `a`. -/
theorem diffCount_pos_iff_mem_diffRange (a : Fin m → ℚ) (d : ℚ) :
    0 < diffCount a d ↔ d ∈ diffRange a := by
  constructor
  · intro h
    rw [diffCount, Finset.card_pos] at h
    obtain ⟨p, hp⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [diffRange, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨p, hp⟩
  · intro h
    simp only [diffRange, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨p, hp⟩ := h
    rw [diffCount, Finset.card_pos]
    exact ⟨p, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp⟩

/-- `diffCount a d = 0` iff `d` lies outside the difference range. -/
theorem diffCount_eq_zero_iff_not_mem_diffRange (a : Fin m → ℚ) (d : ℚ) :
    diffCount a d = 0 ↔ d ∉ diffRange a := by
  constructor
  · intro h hmem
    have hpos : 0 < diffCount a d := (diffCount_pos_iff_mem_diffRange a d).mpr hmem
    omega
  · intro h
    by_contra hne
    exact h ((diffCount_pos_iff_mem_diffRange a d).mp (Nat.pos_of_ne_zero hne))

/-- `diffCount` vanishes off its own range (the support argument
behind (a1)'s indexing over `diffRange a`). -/
theorem diffCount_eq_zero_of_not_mem_diffRange {a : Fin m → ℚ} {d : ℚ}
    (h : d ∉ diffRange a) : diffCount a d = 0 :=
  (diffCount_eq_zero_iff_not_mem_diffRange a d).mpr h

/-- Membership in the difference range, unfolded: `d` is a
difference of two tones of `a`. -/
theorem mem_diffRange_iff (a : Fin m → ℚ) (d : ℚ) :
    d ∈ diffRange a ↔ ∃ i j : Fin m, a i - a j = d := by
  simp only [diffRange, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, j⟩, h⟩
    exact ⟨i, j, h⟩
  · rintro ⟨i, j, h⟩
    exact ⟨(i, j), h⟩

/-- `0` is always a difference when the family is inhabited
(the diagonal pairs). -/
theorem zero_mem_diffRange [Nonempty (Fin m)] (a : Fin m → ℚ) :
    (0 : ℚ) ∈ diffRange a := by
  obtain ⟨i⟩ := ‹Nonempty (Fin m)›
  rw [mem_diffRange_iff]
  exact ⟨i, i, sub_self _⟩

/-- The diagonal pairs give `m ≤ diffCount a 0`. -/
theorem diffCount_zero_ge (a : Fin m → ℚ) : m ≤ diffCount a 0 := by
  have hinj : Function.Injective (fun i : Fin m => (i, i)) := by
    intro i j h
    simpa using congrArg Prod.fst h
  have hcard : (Finset.univ.image (fun i : Fin m => (i, i))).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.univ.image (fun i : Fin m => (i, i)) ⊆
      Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = 0) := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨i, rfl⟩ := hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sub_self _
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

/-- Every difference count is at most the total number of pairs. -/
theorem diffCount_le (a : Fin m → ℚ) (d : ℚ) : diffCount a d ≤ m * m := by
  unfold diffCount
  calc (Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = d)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = m * m := by simp [Fintype.card_prod]

/-- The difference counts exhaust the pairs:
`∑ d ∈ diffRange a, diffCount a d = m * m`. -/
theorem sum_diffCount (a : Fin m → ℚ) :
    ∑ d ∈ diffRange a, diffCount a d = m * m := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin m × Fin m))) (t := diffRange a)
    (f := fun p : Fin m × Fin m => a p.1 - a p.2) (by
      intro p _
      show a p.1 - a p.2 ∈ diffRange a
      rw [mem_diffRange_iff]
      exact ⟨p.1, p.2, rfl⟩)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  calc ∑ d ∈ diffRange a, diffCount a d
      = ∑ d ∈ diffRange a, (Finset.univ.filter
          (fun p : Fin m × Fin m => a p.1 - a p.2 = d)).card :=
        Finset.sum_congr rfl (fun d _ => rfl)
    _ = m * m := h.symm

/-- Within-factor distinctness, in count form: `diffCount a 0 = m`
iff the tones of `a` are pairwise distinct (injective). The forward
direction is the equality case of the diagonal bound
`diffCount_zero_ge`; the backward direction says the zero-difference
pairs are exactly the diagonal. -/
theorem diffCount_zero_eq_iff_injective (a : Fin m → ℚ) :
    diffCount a 0 = m ↔ Function.Injective a := by
  constructor
  · intro h i j hij
    have hsub : Finset.univ.image (fun i : Fin m => (i, i)) ⊆
        Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = 0) := by
      intro q hq
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨k, rfl⟩ := hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact sub_self _
    have hinj : Function.Injective (fun i : Fin m => (i, i)) := by
      intro x y hxy
      simpa using congrArg Prod.fst hxy
    have hcard : (Finset.univ.image (fun i : Fin m => (i, i))).card = m := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have heq : Finset.univ.image (fun i : Fin m => (i, i))
        = Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = 0) := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard]
      exact h.le
    have hmem : (i, j) ∈ Finset.univ.filter
        (fun p : Fin m × Fin m => a p.1 - a p.2 = 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sub_eq_zero]
      exact hij
    rw [← heq] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    have h1 : k = i := congrArg Prod.fst hk
    have h2 : k = j := congrArg Prod.snd hk
    exact h1.symm.trans h2
  · intro hinj
    have heq : Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = 0)
        = Finset.univ.image (fun i : Fin m => (i, i)) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · intro h
        rw [sub_eq_zero] at h
        exact ⟨i, rfl, hinj h⟩
      · rintro ⟨k, rfl, rfl⟩
        exact sub_self _
    have hcard : (Finset.univ.image (fun i : Fin m => (i, i))).card = m := by
      have hinj' : Function.Injective (fun i : Fin m => (i, i)) := by
        intro x y hxy
        simpa using congrArg Prod.fst hxy
      rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_fin]
    unfold diffCount
    rw [heq, hcard]

-- ============================================================================
-- (a1) The collision inner-product identity
-- ============================================================================

/-- Fiber count for (a1): the collision pairs whose `a`-difference
is `d` are exactly the pairs of an `a`-pair of difference `d` and a
`b`-pair of difference `-d` (collision forces the two differences
to be negatives of each other). Counted against `diffCount b d`
via RES-0's symmetry `diffCount_neg`. -/
theorem collFiber_card (a : Fin m → ℚ) (b : Fin n → ℚ) (d : ℚ) :
    ((Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2)).filter
      (fun p => a p.1.1 - a p.2.1 = d)).card
      = diffCount a d * diffCount b d := by
  rw [← diffCount_neg b d]
  unfold diffCount
  rw [← Finset.card_product]
  apply Finset.card_bij (fun q _ => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      at hq ⊢
    obtain ⟨hcoll, hd⟩ := hq
    have hcoll' : a q.1.1 + b q.1.2 = a q.2.1 + b q.2.2 := hcoll
    exact ⟨hd, by linarith⟩
  · intro q₁ _ q₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.1 h.2.1) (Prod.ext h.1.2 h.2.2)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      at hr
    obtain ⟨hda, hdb⟩ := hr
    refine ⟨((r.1.1, r.2.1), (r.1.2, r.2.2)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · show a r.1.1 + b r.2.1 = a r.1.2 + b r.2.2
        linarith
      · exact hda
    · exact Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl rfl)

/-- **(a1) The collision inner-product identity** (memo §2 (a1),
the resonance line's headline): every coincidence in the sum is
paid for by a shared difference of the factors, and the total
count is exactly the inner product of the two difference-count
functions, summed over the first factor's difference range
(the summand vanishes off either range, by the support lemma). -/
theorem collCount_eq_sum_diffCount (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount a b = ∑ d ∈ diffRange a, diffCount a d * diffCount b d := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2))
    (t := diffRange a)
    (f := fun p : (Fin m × Fin n) × (Fin m × Fin n) => a p.1.1 - a p.2.1) (by
      intro p _
      show a p.1.1 - a p.2.1 ∈ diffRange a
      rw [mem_diffRange_iff]
      exact ⟨p.1.1, p.2.1, rfl⟩)
  unfold collCount
  rw [h]
  apply Finset.sum_congr rfl
  intro d _
  exact collFiber_card a b d

/-- (a1), union form: the inner product may be summed over the
union of the two difference ranges — the summand vanishes off
each factor's own range. -/
theorem sum_diffCount_mul_union (a : Fin m → ℚ) (b : Fin n → ℚ) :
    ∑ d ∈ diffRange a ∪ diffRange b, diffCount a d * diffCount b d
      = ∑ d ∈ diffRange a, diffCount a d * diffCount b d := by
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro d _ hd
  rw [diffCount_eq_zero_of_not_mem_diffRange hd]
  exact Nat.zero_mul _

/-- (a1), second-range form: the inner product may equally be
summed over `diffRange b`. -/
theorem collCount_eq_sum_diffRange_snd (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount a b = ∑ d ∈ diffRange b, diffCount a d * diffCount b d := by
  rw [collCount_eq_sum_diffCount a b, ← sum_diffCount_mul_union a b]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro d _ hd
  rw [diffCount_eq_zero_of_not_mem_diffRange hd]
  exact Nat.mul_zero _

/-- Every single summand of (a1)'s inner product is bounded by
the collision count: each shared difference contributes its
product of multiplicities, and nothing cancels. -/
theorem diffCount_mul_le_collCount {a : Fin m → ℚ} {b : Fin n → ℚ} {d : ℚ}
    (hd : d ∈ diffRange a) : diffCount a d * diffCount b d ≤ collCount a b := by
  rw [collCount_eq_sum_diffCount a b]
  exact Finset.single_le_sum (f := fun d => diffCount a d * diffCount b d)
    (fun i _ => Nat.zero_le _) hd

/-- (a1) at coincident factors: the self-collision count is the
sum of squared difference counts. -/
theorem collCount_self_eq_sum_sq (a : Fin m → ℚ) :
    collCount a a = ∑ d ∈ diffRange a, (diffCount a d) ^ 2 := by
  rw [collCount_eq_sum_diffCount a a]
  apply Finset.sum_congr rfl
  intro d _
  rw [pow_two]

/-- Collision counting is symmetric in the two factors, by
swapping the two coordinates of every index pair. -/
theorem collCount_symm (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount a b = collCount b a := by
  unfold collCount
  apply Finset.card_bij (fun q _ => ((q.1.2, q.1.1), (q.2.2, q.2.1)))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have hq' : a q.1.1 + b q.1.2 = a q.2.1 + b q.2.2 := hq
    show b q.1.2 + a q.1.1 = b q.2.2 + a q.2.1
    linarith
  · intro q₁ _ q₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.2 h.1.1) (Prod.ext h.2.2 h.2.1)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine ⟨((r.1.2, r.1.1), (r.2.2, r.2.1)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show a r.1.2 + b r.1.1 = a r.2.2 + b r.2.1
      have hr' : b r.1.1 + a r.1.2 = b r.2.1 + a r.2.2 := hr
      linarith
    · exact Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl rfl)

-- ============================================================================
-- (a2) The shared-gap criterion, sharp, with its equality case
-- ============================================================================

/-- Two distinct terms of a finite sum of naturals are bounded by
the whole sum. -/
theorem add_le_sum_of_mem_of_ne {s : Finset ℚ} {f : ℚ → ℕ} {x y : ℚ}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    f x + f y ≤ ∑ d ∈ s, f d := by
  have hsub : ({x, y} : Finset ℚ) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  calc f x + f y = ∑ d ∈ ({x, y} : Finset ℚ), f d := by
        rw [Finset.sum_pair hxy]
    _ ≤ ∑ d ∈ s, f d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)

/-- **(a2) The shared-gap criterion, sharp** (memo §2 (a2)):
`collCount a b = m * n` — no coincidence beyond the diagonal —
iff the memo's exact distinctness conjunct
`diffCount a 0 * diffCount b 0 = m * n` holds AND no nonzero
difference is shared: there is no `d ≠ 0` with
`diffCount a d > 0 ∧ diffCount b d > 0`. -/
theorem collCount_eq_mul_iff (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount a b = m * n ↔
      diffCount a 0 * diffCount b 0 = m * n ∧
        ¬ ∃ d : ℚ, d ≠ 0 ∧ 0 < diffCount a d ∧ 0 < diffCount b d := by
  constructor
  · intro h
    constructor
    · -- The `d = 0` summand of (a1) is at least `m * n` (diagonal
      -- pairs in each factor) and at most `collCount a b = m * n`.
      by_cases hm : m = 0
      · subst hm
        have h0 : diffCount a 0 = 0 := by
          have hle := diffCount_le a 0
          simp only [Nat.zero_mul] at hle
          exact Nat.eq_zero_of_le_zero hle
        simp [h0]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have h0mem : (0 : ℚ) ∈ diffRange a := by
          haveI : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
          exact zero_mem_diffRange a
        have hle1 : diffCount a 0 * diffCount b 0 ≤ collCount a b := by
          rw [collCount_eq_sum_diffCount a b]
          exact Finset.single_le_sum (f := fun d => diffCount a d * diffCount b d)
            (fun i _ => Nat.zero_le _) h0mem
        have hle2 : m * n ≤ diffCount a 0 * diffCount b 0 :=
          Nat.mul_le_mul (diffCount_zero_ge a) (diffCount_zero_ge b)
        exact le_antisymm (by rw [← h]; exact hle1) hle2
    · -- A shared nonzero difference would contribute a positive
      -- summand on top of the `d = 0` summand's `m * n`.
      rintro ⟨d, hd0, hda, hdb⟩
      have hdmem : d ∈ diffRange a := (diffCount_pos_iff_mem_diffRange a d).mp hda
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          have hle := diffCount_le a d
          simp only [Nat.zero_mul] at hle
          omega
        · exact hm
      have h0mem : (0 : ℚ) ∈ diffRange a := by
        haveI : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
        exact zero_mem_diffRange a
      have hsum := add_le_sum_of_mem_of_ne
        (f := fun d => diffCount a d * diffCount b d) h0mem hdmem (Ne.symm hd0)
      rw [← collCount_eq_sum_diffCount a b] at hsum
      have hterm0 : m * n ≤ diffCount a 0 * diffCount b 0 :=
        Nat.mul_le_mul (diffCount_zero_ge a) (diffCount_zero_ge b)
      have htermd : 0 < diffCount a d * diffCount b d := Nat.mul_pos hda hdb
      omega
  · rintro ⟨hprod, hno⟩
    by_cases hm : m = 0
    · subst hm
      rw [collCount_eq_sum_diffCount, Finset.sum_eq_zero]
      · simp
      · intro d _
        have hle := diffCount_le a d
        simp only [Nat.zero_mul] at hle
        rw [Nat.eq_zero_of_le_zero hle]
        exact Nat.zero_mul _
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have h0mem : (0 : ℚ) ∈ diffRange a := by
        haveI : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
        exact zero_mem_diffRange a
      have h₀ : ∀ d ∈ diffRange a, d ≠ 0 →
          diffCount a d * diffCount b d = 0 := by
        intro d _ hd0
        rcases Nat.eq_zero_or_pos (diffCount a d) with ha | ha
        · rw [ha]; exact Nat.zero_mul _
        · rcases Nat.eq_zero_or_pos (diffCount b d) with hb | hb
          · rw [hb]; exact Nat.mul_zero _
          · exact absurd ⟨d, hd0, ha, hb⟩ hno
      have h₁ : (0 : ℚ) ∉ diffRange a →
          diffCount a 0 * diffCount b 0 = 0 := by
        intro hcon
        exact absurd h0mem hcon
      rw [collCount_eq_sum_diffCount a b, Finset.sum_eq_single 0 h₀ h₁]
      exact hprod

/-- (a2) under within-factor distinctness, stated with the
distinctness hypotheses in count form: no coincidence beyond
the diagonal iff no nonzero difference is shared. -/
theorem collCount_eq_mul_iff_of_distinct (a : Fin m → ℚ) (b : Fin n → ℚ)
    (ha : diffCount a 0 = m) (hb : diffCount b 0 = n) :
    collCount a b = m * n ↔
      ¬ ∃ d : ℚ, d ≠ 0 ∧ 0 < diffCount a d ∧ 0 < diffCount b d := by
  rw [collCount_eq_mul_iff]
  constructor
  · intro h
    exact h.2
  · intro hno
    exact ⟨by rw [ha, hb], hno⟩

/-- **(a2), corollary** (memo §2 (a2)): under within-factor
distinctness, a nontrivial coincidence exists iff the two gap
sets share a nonzero element — iff the factors' resonance
spectra (gap sets, in `ResonanceSpectrum`'s sense) intersect
off `0`. Here "nontrivial coincidence" is `m * n < collCount a b`,
which by RES-0's `collCount_diag_le` is the only way the
collision count can differ from `m * n`. -/
theorem nontrivial_coincidence_iff_shared_gap (a : Fin m → ℚ) (b : Fin n → ℚ)
    (ha : diffCount a 0 = m) (hb : diffCount b 0 = n) :
    m * n < collCount a b ↔
      ∃ d : ℚ, d ≠ 0 ∧ 0 < diffCount a d ∧ 0 < diffCount b d := by
  constructor
  · intro hlt
    by_contra hcon
    have heq : collCount a b = m * n :=
      (collCount_eq_mul_iff a b).mpr ⟨by rw [ha, hb], hcon⟩
    omega
  · intro hex
    have hge : m * n ≤ collCount a b := collCount_diag_le a b
    have hne : collCount a b ≠ m * n := by
      intro heq
      exact ((collCount_eq_mul_iff a b).mp heq).2 hex
    omega

-- ============================================================================
-- The value-fiber form of the collision count
-- ============================================================================

/-- Fiber count over a sum value: the collision pairs landing on
the value `v` are the square of the fiber of `v` — a pair of
indices with equal sums over `v` is a pair of indices over `v`. -/
theorem collValueFiber_card (a : Fin m → ℚ) (b : Fin n → ℚ) (v : ℚ) :
    ((Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2)).filter
      (fun p => sumFam a b p.1 = v)).card
      = ((Finset.univ.filter (fun p : Fin m × Fin n =>
          sumFam a b p = v)).card) ^ 2 := by
  have heq : (Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2)).filter
        (fun p => sumFam a b p.1 = v)
      = (Finset.univ.filter (fun p : Fin m × Fin n => sumFam a b p = v)) ×ˢ
        (Finset.univ.filter (fun p : Fin m × Fin n => sumFam a b p = v)) := by
    ext ⟨p, p'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hcoll, hv⟩
      exact ⟨hv, hcoll.symm.trans hv⟩
    · rintro ⟨hv, hv'⟩
      exact ⟨hv.trans hv'.symm, hv⟩
  rw [heq, Finset.card_product, pow_two]

/-- The collision count is the sum of squared sum-multiplicities:
`collCount a b = ∑ v, (#{p | sumFam a b p = v}) ^ 2`, the
value-side companion of (a1)'s difference-side inner product.
By RES-0's `count_sumSpec`, the fibers are the multiplicities
of the sum spectrum `sumSpec a b`. -/
theorem collCount_eq_sum_sq_fibers (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount a b = ∑ v ∈ Finset.univ.image (sumFam a b),
      ((Finset.univ.filter (fun p : Fin m × Fin n =>
        sumFam a b p = v)).card) ^ 2 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2))
    (t := Finset.univ.image (sumFam a b))
    (f := fun p : (Fin m × Fin n) × (Fin m × Fin n) => sumFam a b p.1) (by
      intro p _
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩)
  unfold collCount
  rw [h]
  apply Finset.sum_congr rfl
  intro v _
  exact collValueFiber_card a b v

-- ============================================================================
-- (a3) The ternary identity
-- ============================================================================

/-- Fiber count for (a3): the ternary collision pairs whose
difference triple is `t` are the product of the three factors'
difference fibers — given `t.1 + t.2.1 + t.2.2 = 0`, the three
difference equations already force the sum coincidence. -/
theorem collFiber3_card (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ)
    (t : ℚ × ℚ × ℚ) (ht : t.1 + t.2.1 + t.2.2 = 0) :
    ((Finset.univ.filter (fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
        sumFam3 a b c p.1 = sumFam3 a b c p.2)).filter
      (fun p => (a p.1.1 - a p.2.1, b p.1.2.1 - b p.2.2.1,
        c p.1.2.2 - c p.2.2.2) = t)).card
      = diffCount a t.1 * diffCount b t.2.1 * diffCount c t.2.2 := by
  rw [show diffCount a t.1 * diffCount b t.2.1 * diffCount c t.2.2
      = ((Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = t.1)) ×ˢ
          (Finset.univ.filter (fun p : Fin n × Fin n => b p.1 - b p.2 = t.2.1)) ×ˢ
          (Finset.univ.filter (fun p : Fin l × Fin l =>
            c p.1 - c p.2 = t.2.2))).card by
    simp only [diffCount, Finset.card_product, mul_assoc]]
  apply Finset.card_bij
    (fun q _ => ((q.1.1, q.2.1), (q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      at hq ⊢
    obtain ⟨hcoll, hdeq⟩ := hq
    simp only [Prod.ext_iff] at hdeq
    obtain ⟨hda, hdb, hdc⟩ := hdeq
    exact ⟨hda, hdb, hdc⟩
  · intro q₁ _ q₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1.1 h.2.2.1))
      (Prod.ext h.1.2 (Prod.ext h.2.1.2 h.2.2.2))
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      at hr
    obtain ⟨hda, hdb, hdc⟩ := hr
    refine ⟨((r.1.1, r.2.1.1, r.2.2.1), (r.1.2, r.2.1.2, r.2.2.2)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · show a r.1.1 + b r.2.1.1 + c r.2.2.1
          = a r.1.2 + b r.2.1.2 + c r.2.2.2
        linarith
      · exact Prod.ext hda (Prod.ext hdb hdc)
    · exact Prod.ext (Prod.ext rfl rfl)
        (Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl rfl))

/-- **(a3) The ternary identity** (memo §2 (a3)): coincidences of
the triple sum are indexed by difference triples summing to
zero — pairwise shared gaps give the two-factor faces of this,
the genuinely ternary coincidences are the interior. Stated as
the finite sum over the three difference ranges, filtered to
`d + e + f = 0`. -/
theorem collCount3_eq_sum (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) :
    collCount3 a b c
      = ∑ t ∈ (diffRange a ×ˢ diffRange b ×ˢ diffRange c).filter
          (fun t => t.1 + t.2.1 + t.2.2 = 0),
        diffCount a t.1 * diffCount b t.2.1 * diffCount c t.2.2 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
        sumFam3 a b c p.1 = sumFam3 a b c p.2))
    (t := (diffRange a ×ˢ diffRange b ×ˢ diffRange c).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 0))
    (f := fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
      (a p.1.1 - a p.2.1, b p.1.2.1 - b p.2.2.1, c p.1.2.2 - c p.2.2.2)) (by
      intro p hp
      have hcoll : sumFam3 a b c p.1 = sumFam3 a b c p.2 := by
        have hp' : p ∈ Finset.univ.filter
            (fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
              sumFam3 a b c p.1 = sumFam3 a b c p.2) := hp
        exact (Finset.mem_filter.mp hp').2
      show (a p.1.1 - a p.2.1, b p.1.2.1 - b p.2.2.1, c p.1.2.2 - c p.2.2.2) ∈
        (diffRange a ×ˢ diffRange b ×ˢ diffRange c).filter
          (fun t => t.1 + t.2.1 + t.2.2 = 0)
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · exact ⟨(mem_diffRange_iff a _).mpr ⟨p.1.1, p.2.1, rfl⟩,
          (mem_diffRange_iff b _).mpr ⟨p.1.2.1, p.2.2.1, rfl⟩,
          (mem_diffRange_iff c _).mpr ⟨p.1.2.2, p.2.2.2, rfl⟩⟩
      · have hp' : a p.1.1 + b p.1.2.1 + c p.1.2.2
            = a p.2.1 + b p.2.2.1 + c p.2.2.2 := hcoll
        linarith)
  unfold collCount3
  rw [h]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_filter] at ht
  exact collFiber3_card a b c t ht.2

/-- The ternary diagonal contributes exactly `m * n * l` collision
pairs, so `m * n * l ≤ collCount3 a b c`. -/
theorem collCount3_diag_le (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) :
    m * n * l ≤ collCount3 a b c := by
  have hinj : Function.Injective
      (fun p : Fin m × Fin n × Fin l => (p, p)) := by
    intro p₁ p₂ h
    simpa using congrArg Prod.fst h
  have hcard : (Finset.univ.image
      (fun p : Fin m × Fin n × Fin l => (p, p))).card = m * n * l := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp [Fintype.card_prod, mul_assoc]
  have hsub : Finset.univ.image (fun p : Fin m × Fin n × Fin l => (p, p)) ⊆
      Finset.univ.filter (fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
        sumFam3 a b c p.1 = sumFam3 a b c p.2) := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨p, rfl⟩ := hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  unfold collCount3
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Every single summand of (a3)'s ternary inner product is
bounded by the ternary collision count. -/
theorem diffCount_triple_le_collCount3 {a : Fin m → ℚ} {b : Fin n → ℚ}
    {c : Fin l → ℚ} {t : ℚ × ℚ × ℚ}
    (ht : t ∈ (diffRange a ×ˢ diffRange b ×ˢ diffRange c).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 0)) :
    diffCount a t.1 * diffCount b t.2.1 * diffCount c t.2.2
      ≤ collCount3 a b c := by
  rw [collCount3_eq_sum a b c]
  exact Finset.single_le_sum
    (f := fun t => diffCount a t.1 * diffCount b t.2.1 * diffCount c t.2.2)
    (fun i _ => Nat.zero_le _) ht

-- ============================================================================
-- Read-backs at RES-0's named examples
-- ============================================================================

/-- Read-back: `exA = {0, 1}` against `exB = {1, 2}` has sum
values `1, 2, 2, 3`, hence `1 + 4 + 1 = 6` collision pairs. -/
theorem rb_collCount : collCount exA exB = 6 := by
  simp only [collCount, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [sumFam, exA, exB]

/-- Read-back, (a1) at the examples: the inner product of the
difference counts is `4 + 1 + 1 = 6`. -/
theorem rb_collCount_eq_sum :
    ∑ d ∈ diffRange exA, diffCount exA d * diffCount exB d = 6 := by
  rw [← collCount_eq_sum_diffCount exA exB, rb_collCount]

/-- Read-back: the ternary self-sum of `exA = {0, 1}` has sum
values `0, 1, 1, 1, 2, 2, 2, 3`, hence `1 + 9 + 9 + 1 = 20`
collision pairs. -/
theorem rb_collCount3 : collCount3 exA exA exA = 20 := by
  simp only [collCount3, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [sumFam3, exA]

end ThetLogos

#print axioms ThetLogos.collCount_eq_sum_diffCount
#print axioms ThetLogos.collCount_eq_mul_iff
#print axioms ThetLogos.nontrivial_coincidence_iff_shared_gap
#print axioms ThetLogos.collCount3_eq_sum
#print axioms ThetLogos.collFiber_card
#print axioms ThetLogos.collFiber3_card
#print axioms ThetLogos.diffCount_zero_eq_iff_injective
#print axioms ThetLogos.collCount_eq_sum_sq_fibers
