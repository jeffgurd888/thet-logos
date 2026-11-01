import Mathlib.Tactic
import ThetLogos.SumResonance
import ThetLogos.SumResonanceCore

/-!
# Sum resonance: forcing and extremality (RES-2)

Third brick of the resonance line, per the coordinator pack
`routeb-general-scratch/pack-res-2.md` and the ratified scoping memo
`routeb-general-scratch/scoping-resonance-2026-10-30.md` (§3, the
interest test). RES-0's vocabulary (`ThetLogos.SumResonance`:
`sumFam`, `sumSpec`, `diffCount`, `diffRange`, `collCount`, `excess`)
and RES-1's core (`ThetLogos.SumResonanceCore`) are cited, never
forked.

**Content (memo §3, statements registered in substance).**
- (1) Denominator clearing as a stated transport: any finite
  ℚ-spectrum scales into ℤ by a positive integer scale, and the
  (a)-family quantities of §2 — `collCount`, the `diffCount`
  pattern, `excess` — are invariant under a common nonzero scaling
  of both factors (the scale is a symmetry of these Props; the
  named-ratio counts of §2(b), which are only scale-covariant, are
  RES-3's, not this brick's).
- (2) The pigeonhole floor: if the `m * n` sums land in a value set
  of size `K`, then `excess a b ≥ m * n − K` and some sum value has
  multiplicity `≥ ⌈m * n / K⌉`. Coincidences past that floor are
  arithmetic rent, not findings (memo §3).
- (3) The distinct-sums range bound: if all `m * n` sums of two
  integer spectra are distinct, the sum range is `≥ m * n − 1`.
- (4) The extremal witness: the base-`(2L+1)` family
  `A = [0, L]`, `B = (2L+1) • B'` (with `B' j = j`) has all sums
  distinct, with range of the registered shape
  `L + (2L+1) * (n − 1)` — the bound's shape is achieved.

RES-2b / memo §2 (a4) (single-tone perturbation finiteness) is NOT
this brick.

**K-RES-1 (pre-registered framing kill), noted on the face:** raw
coincidence counts at any seat are bookkeeping; a seat's content is
its excess OVER the floor proved here, or the pattern of which
differences carry the coincidences (RES-1's (a1)–(a2)). These
theorems price every future seat report.

NO CLAIM beyond the abstract finite-ℚ / finite-ℤ statements proved
below. "Harmonic / sympathetic / octave" name only the pinned
mathematics of the memo's §2: no acoustics, no physical-world
claim, no measured number derived or fitted. Dial 1 untouched;
dials 0/4.
-/

namespace ThetLogos

open Finset

variable {m n : ℕ}

-- ============================================================================
-- (1) Denominator clearing and the scaling transport
-- ============================================================================

/-- The scaled family: every tone multiplied by `D`. -/
def scaleFam (D : ℚ) (a : Fin m → ℚ) : Fin m → ℚ :=
  fun i => D * a i

/-- The sum-multiplicity function: the number of tone pairs whose
sum is `v`. This is the multiplicity function of `sumSpec a b`
(RES-0's `count_sumSpec`), named here for the floor statements. -/
def sumMult (a : Fin m → ℚ) (b : Fin n → ℚ) (v : ℚ) : ℕ :=
  (Finset.univ.filter (fun p => sumFam a b p = v)).card

/-- Denominator clearing, single family: any finite ℚ-spectrum
scales into ℤ — there is a positive integer scale `D` and an
integer family taking the scaled values. The scale is the product
of the tones' denominators. -/
theorem exists_scale_int (a : Fin m → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ aZ : Fin m → ℤ, ∀ i, (D : ℚ) * a i = (aZ i : ℚ) := by
  have hDpos : 0 < ∏ i, (a i).den := by
    apply Nat.pos_of_ne_zero
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (a i).den_pos.ne'
  refine ⟨∏ i, (a i).den, hDpos,
    fun i => ((∏ j, (a j).den) / (a i).den : ℕ) * (a i).num, ?_⟩
  intro i
  dsimp only
  set D := ∏ j, (a j).den with hD
  have hdvd : (a i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hfactor : (a i).den * (D / (a i).den) = D := Nat.mul_div_cancel' hdvd
  have hden : ((a i).den : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (a i).den_pos.ne'
  have hfactorQ : (D : ℚ) = (a i).den * ((D / (a i).den : ℕ) : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hfactor
    simpa [Nat.cast_mul] using h.symm
  have hnum : ((a i).den : ℚ) * a i = (a i).num := by
    nth_rewrite 2 [← (a i).num_div_den]
    rw [mul_comm, div_mul_cancel₀ _ hden]
  calc (D : ℚ) * a i = ((D / (a i).den : ℕ) : ℚ) * (((a i).den : ℚ) * a i) := by
          rw [hfactorQ]; ring
    _ = ((((D / (a i).den : ℕ) : ℤ) * (a i).num : ℤ) : ℚ) := by
          rw [hnum, Int.cast_mul, Int.cast_natCast]

/-- Denominator clearing, common scale for two families: one
positive integer scale clears both spectra at once — the form the
transport and the integer seats use. -/
theorem exists_common_scale_int (a : Fin m → ℚ) (b : Fin n → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ aZ : Fin m → ℤ, ∃ bZ : Fin n → ℤ,
      (∀ i, (D : ℚ) * a i = (aZ i : ℚ)) ∧ (∀ j, (D : ℚ) * b j = (bZ j : ℚ)) := by
  obtain ⟨Da, hDa, aZ, haZ⟩ := exists_scale_int a
  obtain ⟨Db, hDb, bZ, hbZ⟩ := exists_scale_int b
  refine ⟨Da * Db, Nat.mul_pos hDa hDb, fun i => (Db : ℤ) * aZ i,
    fun j => (Da : ℤ) * bZ j, ?_, ?_⟩
  · intro i
    dsimp only
    calc ((Da * Db : ℕ) : ℚ) * a i = (Db : ℚ) * ((Da : ℚ) * a i) := by push_cast; ring
      _ = (((Db : ℤ) * aZ i : ℤ) : ℚ) := by
          rw [haZ i, Int.cast_mul, Int.cast_natCast]
  · intro j
    dsimp only
    calc ((Da * Db : ℕ) : ℚ) * b j = (Da : ℚ) * ((Db : ℚ) * b j) := by push_cast; ring
      _ = (((Da : ℤ) * bZ j : ℤ) : ℚ) := by
          rw [hbZ j, Int.cast_mul, Int.cast_natCast]

/-- The sum family of the scaled factors is the scale of the sum
family. -/
theorem sumFam_scale (D : ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (p : Fin m × Fin n) :
    sumFam (scaleFam D a) (scaleFam D b) p = D * sumFam a b p := by
  simp [sumFam, scaleFam]; ring

/-- Transport: `collCount` is invariant under a common nonzero
scaling of both factors. -/
theorem collCount_scale {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    collCount (scaleFam D a) (scaleFam D b) = collCount a b := by
  unfold collCount
  congr 1
  apply Finset.filter_congr
  intro p _
  rw [sumFam_scale, sumFam_scale]
  constructor
  · intro h; exact mul_left_cancel₀ hD h
  · intro h; rw [h]

/-- Transport: the `diffCount` pattern is invariant under scaling —
the count at the scaled difference `D * d` of the scaled family is
the count at `d`. -/
theorem diffCount_scale {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) (d : ℚ) :
    diffCount (scaleFam D a) (D * d) = diffCount a d := by
  unfold diffCount
  congr 1
  apply Finset.filter_congr
  intro p _
  have h1 : scaleFam D a p.1 - scaleFam D a p.2 = D * (a p.1 - a p.2) := by
    simp [scaleFam]; ring
  rw [h1]
  constructor
  · intro h; exact mul_left_cancel₀ hD h
  · intro h; rw [h]

/-- Transport at `0`: the zero-difference count (the distinctness
count of (a2)) is scaling-invariant. -/
theorem diffCount_scale_zero {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) :
    diffCount (scaleFam D a) 0 = diffCount a 0 := by
  have h := diffCount_scale hD a 0
  rwa [mul_zero] at h

/-- Transport: the difference-range pattern is scaling-covariant —
`D * d` is a difference of the scaled family iff `d` is a
difference of the original. -/
theorem mem_diffRange_scale {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) (d : ℚ) :
    D * d ∈ diffRange (scaleFam D a) ↔ d ∈ diffRange a := by
  rw [← diffCount_pos_iff_mem_diffRange, diffCount_scale hD,
    diffCount_pos_iff_mem_diffRange]

/-- Transport: `excess` is invariant under a common nonzero scaling
of both factors — scaling neither creates nor destroys degeneracy
beyond distinctness. -/
theorem excess_scale {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    excess (scaleFam D a) (scaleFam D b) = excess a b := by
  have hinj : Function.Injective (fun v : ℚ => D * v) :=
    fun x y h => mul_left_cancel₀ hD h
  have htoFin : ∀ (x : Fin m → ℚ) (y : Fin n → ℚ),
      (sumSpec x y).toFinset = Finset.univ.image (sumFam x y) := by
    intro x y
    ext v
    simp only [Multiset.mem_toFinset, mem_sumSpec, Finset.mem_image,
      Finset.mem_univ, true_and]
  have himg : Finset.univ.image (sumFam (scaleFam D a) (scaleFam D b))
      = (Finset.univ.image (sumFam a b)).image (fun v => D * v) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p _
    exact sumFam_scale D a b p
  have hcard : (sumSpec (scaleFam D a) (scaleFam D b)).dedup.card
      = (sumSpec a b).dedup.card := by
    rw [← Multiset.card_toFinset, ← Multiset.card_toFinset, htoFin, htoFin,
      himg, Finset.card_image_of_injective _ hinj]
  unfold excess
  rw [hcard]

/-- Transport: the sum-multiplicity pattern is invariant under a
common nonzero scaling — the multiplicity at the scaled value
`D * v` of the scaled sum is the multiplicity at `v`. -/
theorem sumMult_scale {D : ℚ} (hD : D ≠ 0) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (v : ℚ) :
    sumMult (scaleFam D a) (scaleFam D b) (D * v) = sumMult a b v := by
  unfold sumMult
  congr 1
  apply Finset.filter_congr
  intro p _
  rw [sumFam_scale]
  constructor
  · intro h; exact mul_left_cancel₀ hD h
  · intro h; rw [h]

-- ============================================================================
-- (2) The pigeonhole floor
-- ============================================================================

/-- The sum-multiplicity function is the multiset multiplicity of
the sum spectrum (RES-0's `count_sumSpec`, read backwards). -/
theorem sumMult_eq_count (a : Fin m → ℚ) (b : Fin n → ℚ) (v : ℚ) :
    sumMult a b v = (sumSpec a b).count v :=
  (count_sumSpec a b v).symm

/-- The multiplicities over a value set containing all sums
exhaust the pairs: `∑ v ∈ S, sumMult a b v = m * n`. -/
theorem sum_sumMult (a : Fin m → ℚ) (b : Fin n → ℚ) (S : Finset ℚ)
    (hS : ∀ p, sumFam a b p ∈ S) :
    ∑ v ∈ S, sumMult a b v = m * n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin m × Fin n))) (t := S)
    (f := sumFam a b) (by intro p _; exact hS p)
  have h2 : (Finset.univ : Finset (Fin m × Fin n)).card = m * n := by
    simp [Fintype.card_prod]
  rw [h2] at h
  exact h.symm

/-- **The pigeonhole floor, excess form** (memo §3): if the
`m * n` sums land in a value set `S` of size `K`, then
`excess a b ≥ m * n − K`. Coincidences up to this floor are
arithmetic rent. -/
theorem excess_ge_floor (a : Fin m → ℚ) (b : Fin n → ℚ) (S : Finset ℚ)
    (hS : ∀ p, sumFam a b p ∈ S) :
    m * n - S.card ≤ excess a b := by
  have hsub : (sumSpec a b).toFinset ⊆ S := by
    intro v hv
    rw [Multiset.mem_toFinset, mem_sumSpec] at hv
    obtain ⟨p, hp⟩ := hv
    rw [← hp]
    exact hS p
  have hle : (sumSpec a b).dedup.card ≤ S.card := by
    rw [← Multiset.card_toFinset]
    exact Finset.card_le_card hsub
  have hex := excess_add_dedup_card a b
  omega

/-- **The pigeonhole floor, multiplicity form** (memo §3): if the
sums land in a nonempty value set `S`, some sum value in `S` has
multiplicity at least the average, in cross-multiplied form:
`S.card * sumMult a b v ≥ m * n` for some `v ∈ S`. -/
theorem exists_sumMult_mul_ge (a : Fin m → ℚ) (b : Fin n → ℚ) (S : Finset ℚ)
    (hS : ∀ p, sumFam a b p ∈ S) (hne : S.Nonempty) :
    ∃ v ∈ S, S.card * sumMult a b v ≥ m * n := by
  obtain ⟨v, hvS, hmax⟩ := Finset.exists_max_image S (sumMult a b) hne
  refine ⟨v, hvS, ?_⟩
  have hsum := sum_sumMult a b S hS
  have hle := Finset.sum_le_card_nsmul S (sumMult a b) (sumMult a b v)
    (fun w hw => hmax w hw)
  rw [hsum] at hle
  simpa [smul_eq_mul] using hle

/-- **The pigeonhole floor, ceiling form** (memo §3): some sum
value has multiplicity `≥ ⌈m * n / K⌉`, where `K = S.card > 0` and
the ceiling is written `(m * n + K − 1) / K` in natural division. -/
theorem exists_sumMult_ceil_ge (a : Fin m → ℚ) (b : Fin n → ℚ) (S : Finset ℚ)
    (hS : ∀ p, sumFam a b p ∈ S) (hne : S.Nonempty) :
    ∃ v ∈ S, (m * n + S.card - 1) / S.card ≤ sumMult a b v := by
  have hK : 0 < S.card := Finset.card_pos.mpr hne
  obtain ⟨v, hvS, hv⟩ := exists_sumMult_mul_ge a b S hS hne
  refine ⟨v, hvS, ?_⟩
  rw [Nat.div_le_iff_le_mul_add_pred hK]
  have hvm : m * n ≤ sumMult a b v * S.card := by
    rw [mul_comm] at hv; exact hv
  omega

-- ============================================================================
-- Integer seats: families over ℤ, cast into the ℚ vocabulary
-- ============================================================================

/-- The sum family of two integer tone families. -/
def sumFamZ (a : Fin m → ℤ) (b : Fin n → ℤ) : Fin m × Fin n → ℤ :=
  fun p => a p.1 + b p.2

/-- The cast bridge: the ℚ sum family of the cast integer families
is the cast of the integer sum family. -/
theorem sumFam_cast (a : Fin m → ℤ) (b : Fin n → ℤ) (p : Fin m × Fin n) :
    sumFam (fun i => (a i : ℚ)) (fun j => (b j : ℚ)) p
      = ((sumFamZ a b p : ℤ) : ℚ) := by
  simp [sumFam, sumFamZ]

/-- The pigeonhole floor at an integer seat, excess form: if the
integer sums land in an integer value set `T`, the excess of the
cast families is at least `m * n − T.card`. -/
theorem excess_int_ge_floor (a : Fin m → ℤ) (b : Fin n → ℤ) (T : Finset ℤ)
    (hT : ∀ p, sumFamZ a b p ∈ T) :
    m * n - T.card ≤ excess (fun i => (a i : ℚ)) (fun j => (b j : ℚ)) := by
  have hcard : (T.image (fun z : ℤ => (z : ℚ))).card = T.card :=
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h)
  rw [← hcard]
  apply excess_ge_floor
  intro p
  rw [sumFam_cast]
  exact Finset.mem_image.mpr ⟨sumFamZ a b p, hT p, rfl⟩

/-- The pigeonhole floor at an integer seat, multiplicity form:
some integer sum value in `T` carries multiplicity at least the
average, in cross-multiplied form, read through the cast. -/
theorem exists_sumMult_int_mul_ge (a : Fin m → ℤ) (b : Fin n → ℤ)
    (T : Finset ℤ) (hT : ∀ p, sumFamZ a b p ∈ T) (hne : T.Nonempty) :
    ∃ v ∈ T, T.card * sumMult (fun i => (a i : ℚ)) (fun j => (b j : ℚ))
      ((v : ℤ) : ℚ) ≥ m * n := by
  have hcard : (T.image (fun z : ℤ => (z : ℚ))).card = T.card :=
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h)
  have hne' : (T.image (fun z : ℤ => (z : ℚ))).Nonempty :=
    Finset.Nonempty.image hne _
  obtain ⟨w, hw, hge⟩ := exists_sumMult_mul_ge (fun i => (a i : ℚ))
    (fun j => (b j : ℚ)) (T.image (fun z : ℤ => (z : ℚ)))
    (by
      intro p
      rw [sumFam_cast]
      exact Finset.mem_image.mpr ⟨sumFamZ a b p, hT p, rfl⟩) hne'
  rw [Finset.mem_image] at hw
  obtain ⟨v, hvT, rfl⟩ := hw
  exact ⟨v, hvT, by rwa [hcard] at hge⟩

-- ============================================================================
-- (3) The distinct-sums range bound
-- ============================================================================

/-- The set of integer sum values. -/
def sumSetZ (a : Fin m → ℤ) (b : Fin n → ℤ) : Finset ℤ :=
  Finset.univ.image (sumFamZ a b)

/-- If the integer sums are all distinct, the sum-value set has
exactly `m * n` elements. -/
theorem sumSetZ_card_of_injective (a : Fin m → ℤ) (b : Fin n → ℤ)
    (hinj : Function.Injective (sumFamZ a b)) :
    (sumSetZ a b).card = m * n := by
  unfold sumSetZ
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- A finite set of integers spans at least its cardinality minus
one: `S.card − 1 ≤ max S − min S`. -/
theorem int_card_sub_one_le_max_sub_min (S : Finset ℤ) (hne : S.Nonempty) :
    (S.card : ℤ) - 1 ≤ S.max' hne - S.min' hne := by
  have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
  have hcard := Finset.card_le_card hsub
  have hIcc : ((Finset.Icc (S.min' hne) (S.max' hne)).card : ℤ)
      = S.max' hne + 1 - S.min' hne :=
    Int.card_Icc_of_le _ _ (by have := S.min'_le _ (S.max'_mem hne); omega)
  have hcast : (S.card : ℤ) ≤ ((Finset.Icc (S.min' hne) (S.max' hne)).card : ℤ) := by
    exact_mod_cast hcard
  omega

/-- **The distinct-sums range bound** (memo §3): if all `m * n`
sums of two integer spectra are distinct, the sum range —
`max − min` of the sum-value set — is `≥ m * n − 1`. -/
theorem distinct_sums_range_bound (a : Fin m → ℤ) (b : Fin n → ℤ)
    (hinj : Function.Injective (sumFamZ a b)) (hm : 0 < m) (hn : 0 < n) :
    (m * n : ℤ) - 1 ≤ (sumSetZ a b).max' (by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have : (sumSetZ a b).card = 0 := Finset.card_eq_zero.mpr hempty
      rw [sumSetZ_card_of_injective a b hinj] at this
      have hpos : 0 < m * n := Nat.mul_pos hm hn
      omega) - (sumSetZ a b).min' (by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have : (sumSetZ a b).card = 0 := Finset.card_eq_zero.mpr hempty
      rw [sumSetZ_card_of_injective a b hinj] at this
      have hpos : 0 < m * n := Nat.mul_pos hm hn
      omega) := by
  have hne : (sumSetZ a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : (sumSetZ a b).card = 0 := Finset.card_eq_zero.mpr hempty
    rw [sumSetZ_card_of_injective a b hinj] at this
    have hpos : 0 < m * n := Nat.mul_pos hm hn
    omega
  have h := int_card_sub_one_le_max_sub_min (sumSetZ a b) hne
  rw [sumSetZ_card_of_injective a b hinj] at h
  exact h

/-- The distinct-sums range bound, attained form: two sum indices
realise a difference of at least `m * n − 1`. -/
theorem distinct_sums_range_bound_exists (a : Fin m → ℤ) (b : Fin n → ℤ)
    (hinj : Function.Injective (sumFamZ a b)) (hm : 0 < m) (hn : 0 < n) :
    ∃ p q : Fin m × Fin n, (m * n : ℤ) - 1 ≤ sumFamZ a b q - sumFamZ a b p := by
  have hne : (sumSetZ a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : (sumSetZ a b).card = 0 := Finset.card_eq_zero.mpr hempty
    rw [sumSetZ_card_of_injective a b hinj] at this
    have hpos : 0 < m * n := Nat.mul_pos hm hn
    omega
  have hmax : (sumSetZ a b).max' hne ∈ sumSetZ a b := (sumSetZ a b).max'_mem hne
  have hmin : (sumSetZ a b).min' hne ∈ sumSetZ a b := (sumSetZ a b).min'_mem hne
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmax
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hmin
  refine ⟨p, q, ?_⟩
  have h := distinct_sums_range_bound a b hinj hm hn
  rw [hq, hp]
  exact h

-- ============================================================================
-- (4) The extremal witness: the base-(2L+1) construction
-- ============================================================================

/-- The first extremal factor: the arithmetic family `A = [0, L]`,
as `Fin (L+1) → ℤ`, `A i = i`. -/
def baseA (L : ℕ) : Fin (L + 1) → ℤ :=
  fun i => (i.val : ℤ)

/-- The identity family `B' j = j`, before the base scaling. -/
def baseId (n : ℕ) : Fin n → ℤ :=
  fun j => (j.val : ℤ)

/-- The second extremal factor: `B = (2L+1) • B'`, the base-scaled
identity family. -/
def baseB (L n : ℕ) : Fin n → ℤ :=
  fun j => (2 * (L : ℤ) + 1) * baseId n j

/-- The `A`-values lie in `[0, L]`. -/
theorem baseA_bounds (L : ℕ) (i : Fin (L + 1)) :
    0 ≤ baseA L i ∧ baseA L i ≤ (L : ℤ) := by
  unfold baseA
  constructor
  · exact_mod_cast Nat.zero_le _
  · have h : i.val ≤ L := Nat.lt_succ_iff.mp i.isLt
    exact_mod_cast h

/-- The `B`-values are the base multiples: `B j = (2L+1) * j`. -/
theorem baseB_apply (L n : ℕ) (j : Fin n) :
    baseB L n j = (2 * (L : ℤ) + 1) * (j.val : ℤ) :=
  rfl

/-- **The extremal witness: distinctness** (memo §3). The
base-`(2L+1)` sums are all distinct: a collision would force two
`A`-values in `[0, L]` to agree modulo `2L+1`, hence to agree, and
then the `B'`-values agree. -/
theorem sumFamZ_base_injective (L n : ℕ) :
    Function.Injective (sumFamZ (baseA L) (baseB L n)) := by
  intro p q h
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  have hM : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  have hval : ∀ k : Fin (L + 1), ((k.val : ℤ)) < 2 * (L : ℤ) + 1 := by
    intro k
    have hk : k.val ≤ L := Nat.lt_succ_iff.mp k.isLt
    have : (k.val : ℤ) ≤ (L : ℤ) := by exact_mod_cast hk
    omega
  have hsum : (i.val : ℤ) + (2 * (L : ℤ) + 1) * (j.val : ℤ)
      = (i'.val : ℤ) + (2 * (L : ℤ) + 1) * (j'.val : ℤ) := h
  have hmod : (i.val : ℤ) % (2 * (L : ℤ) + 1)
      = (i'.val : ℤ) % (2 * (L : ℤ) + 1) := by
    have e1 : ((i.val : ℤ) + (2 * (L : ℤ) + 1) * (j.val : ℤ)) % (2 * (L : ℤ) + 1)
        = (i.val : ℤ) % (2 * (L : ℤ) + 1) := Int.add_mul_emod_self_left _ _ _
    have e2 : ((i'.val : ℤ) + (2 * (L : ℤ) + 1) * (j'.val : ℤ)) % (2 * (L : ℤ) + 1)
        = (i'.val : ℤ) % (2 * (L : ℤ) + 1) := Int.add_mul_emod_self_left _ _ _
    rw [hsum] at e1
    rw [e1] at e2
    exact e2
  have hij : (i.val : ℤ) = (i'.val : ℤ) := by
    rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _) (hval i),
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _) (hval i')] at hmod
    exact hmod
  have hi : i = i' := by
    apply Fin.ext
    exact_mod_cast hij
  have hjj : (j.val : ℤ) = (j'.val : ℤ) := by
    have h2 : (2 * (L : ℤ) + 1) * (j.val : ℤ)
        = (2 * (L : ℤ) + 1) * (j'.val : ℤ) := by linarith
    have := mul_left_cancel₀ (ne_of_gt hM) h2
    exact this
  have hj : j = j' := by
    apply Fin.ext
    exact_mod_cast hjj
  exact Prod.ext hi hj

/-- The extremal sums are nonnegative. -/
theorem sumFamZ_base_nonneg (L n : ℕ) (p : Fin (L + 1) × Fin n) :
    0 ≤ sumFamZ (baseA L) (baseB L n) p := by
  obtain ⟨i, j⟩ := p
  have hi := (baseA_bounds L i).1
  have hj : 0 ≤ baseB L n j := by
    unfold baseB baseId
    positivity
  exact add_nonneg hi hj

/-- The extremal sums lie below the registered range shape:
every sum is `≤ L + (2L+1) * (n − 1)` (for `0 < n`). -/
theorem sumFamZ_base_le (L n : ℕ) (hn : 0 < n) (p : Fin (L + 1) × Fin n) :
    sumFamZ (baseA L) (baseB L n) p ≤ (L : ℤ) + (2 * (L : ℤ) + 1) * ((n : ℤ) - 1) := by
  obtain ⟨i, j⟩ := p
  have hi := (baseA_bounds L i).2
  have hj : (j.val : ℤ) ≤ (n : ℤ) - 1 := by
    have hjn : j.val < n := j.isLt
    have h1 : (j.val : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hjn
    omega
  have hM : (0 : ℤ) ≤ 2 * (L : ℤ) + 1 := by positivity
  have hBj : baseB L n j ≤ (2 * (L : ℤ) + 1) * ((n : ℤ) - 1) := by
    rw [baseB_apply]
    exact mul_le_mul_of_nonneg_left hj hM
  show baseA L i + baseB L n j ≤ _
  linarith

/-- The extremal range is achieved: the bottom sum is `0` and the
top sum is exactly `L + (2L+1) * (n − 1)` — the bound's shape
`~ (2L+1) * n`, attained by explicit indices. -/
theorem sumFamZ_base_range_achieved (L n : ℕ) (hn : 0 < n) :
    ∃ p q : Fin (L + 1) × Fin n,
      sumFamZ (baseA L) (baseB L n) q = 0 ∧
      sumFamZ (baseA L) (baseB L n) p - sumFamZ (baseA L) (baseB L n) q
        = (L : ℤ) + (2 * (L : ℤ) + 1) * ((n : ℤ) - 1) := by
  refine ⟨(⟨L, by omega⟩, ⟨n - 1, by omega⟩), (⟨0, by omega⟩, ⟨0, hn⟩), ?_, ?_⟩
  · simp [sumFamZ, baseA, baseB, baseId]
  · have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    simp only [sumFamZ, baseA, baseB, baseId, Nat.cast_zero, mul_zero, add_zero,
      sub_zero]
    rw [hcast]

/-- The extremal witness meets the distinct-sums bound: its
attained difference range is at least `(L+1) * n − 1` — combined
with `sumFamZ_base_le`, the witness's range is exactly of the
registered shape. -/
theorem sumFamZ_base_range_bound (L n : ℕ) (hn : 0 < n) :
    ∃ p q : Fin (L + 1) × Fin n,
      ((L + 1) * n : ℤ) - 1 ≤ sumFamZ (baseA L) (baseB L n) q
        - sumFamZ (baseA L) (baseB L n) p :=
  distinct_sums_range_bound_exists (baseA L) (baseB L n)
    (sumFamZ_base_injective L n) (by omega) hn

-- ============================================================================
-- Read-backs
-- ============================================================================

/-- Read-back, denominator clearing at RES-0's example: doubling
`exA = {0, 1}` clears it to the integer family `{0, 2}`-values,
here checked through the `diffCount` transport at `d = 1`. -/
theorem rb_diffCount_scale_exA : diffCount (scaleFam 2 exA) 2 = diffCount exA 1 := by
  have h := diffCount_scale (D := (2 : ℚ)) (by norm_num) exA 1
  norm_num at h
  exact h

/-- Read-back, the extremal witness at `L = 2`, `n = 3`: the
`3 * 3 = 9` base-`5` sums `i + 5j` are all distinct. -/
theorem rb_base_injective : Function.Injective (sumFamZ (baseA 2) (baseB 2 3)) :=
  sumFamZ_base_injective 2 3

end ThetLogos

#print axioms ThetLogos.exists_common_scale_int
#print axioms ThetLogos.collCount_scale
#print axioms ThetLogos.diffCount_scale
#print axioms ThetLogos.excess_scale
#print axioms ThetLogos.excess_ge_floor
#print axioms ThetLogos.exists_sumMult_ceil_ge
#print axioms ThetLogos.excess_int_ge_floor
#print axioms ThetLogos.distinct_sums_range_bound
#print axioms ThetLogos.sumFamZ_base_injective
#print axioms ThetLogos.sumFamZ_base_range_achieved
