/-
# MQ3-1: the Kolmogorov extension theorem, library-side

Rung MQ3-1 of the M-Q3 continuum ladder
(`m-q3-scope-2026-11-08.md` §4). The pin (Mathlib v4.35.0-rc3)
carries the definitions of `IsProjectiveMeasureFamily` /
`IsProjectiveLimit`, the uniqueness theorem, and the additive
content `projectiveFamilyContent` on the measurable cylinders —
but its own header records that the *existence* half, the
Kolmogorov extension theorem itself, is "not yet in Mathlib"
(`ProjectiveFamilyContent.lean`). This module assembles it, at
the generality the scoping pins: a countable index type and
Polish (standard-Borel) factor spaces.

**Statement (frozen by the scoping).** For a countable `ι`,
Polish spaces `α i`, and a projective family `P` of probability
measures, there exists a measure `μ` on `Π i, α i` which is the
projective limit of `P`.

**Route.** `projectiveFamilyContent` (in-pin) is shown
σ-subadditive: by the pin's own reduction
(`isSigmaSubadditive_of_addContent_iUnion_eq_tsum` +
`addContent_iUnion_eq_sum_of_tendsto_zero`) this is the
statement that a decreasing sequence of measurable cylinders
with empty intersection has content tending to 0, proved by
the classical compactness argument — inner regularity by
closed compact cylinders (`ClosedCompactCylinders.lean`) plus
a finite-intersection estimate plus Tychonoff extraction over
the countable coordinate union. The content is then promoted
by Carathéodory (`AddContent.measure`), agrees with `P` on
cylinders (`AddContent.measure_eq` +
`projectiveFamilyContent_cylinder`), and agreement on
cylinders is exactly `IsProjectiveLimit` after
`Measure.map_apply`.

NO CLAIM. This is library infrastructure: it constructs a
limit *measure* over the cylinder seats. It is not the M-Q3
event (MQ3-6), it is not a scaling limit of the corpus's
lattice seats, and it moves no dial (K-MQ3-PROXY stands over
any summary that says otherwise).
-/

import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.Portmanteau

open Set MeasureTheory Filter

open scoped ENNReal Topology NNReal

namespace ThetLogos

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

/-- **B1 — inner-regular approximation at a finite seat.**
A measurable set in a finite product of Polish spaces is
approximated from inside by a closed compact set, with the
`P J`-measure of the remainder below any prescribed `ε > 0`.
This is `MeasurableSet.exists_isCompact_isClosed_lt_add` at
the finite measure `P J` (inner regularity of finite measures
on Polish spaces), restated in the difference form the
compactness argument consumes. -/
theorem exists_closedCompact_sub
    [∀ J, IsProbabilityMeasure (P J)] (J : Finset ι)
    {S : Set (∀ j : J, α j)} (hS : MeasurableSet S)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set (∀ j : J, α j), K ⊆ S ∧ IsCompact K ∧ IsClosed K ∧ P J (S \ K) < ε := by
  obtain ⟨K, hKS, hKc, hlt⟩ :=
    hS.exists_isCompact_sdiff_lt (μ := P J) (measure_ne_top _ _) hε.ne'
  exact ⟨K, hKS, hKc, hKc.isClosed, hlt⟩

/-- **B2b — compact extraction.** Given finsets `J n` and closed
sets `K n ⊆ Π j : J n, α j`, each compact, such that every
finite intersection of the cylinders `cylinder (J k) (K k)`
is nonempty, there is a point of the full product lying in
every one of them. (No monotonicity of `J` is needed: the
finite-intersection hypothesis does all the work.) Tychonoff
over the coordinate compacts `A i = eval_i '' K (k i)`, where
`k i` is the first index with `i ∈ J (k i)`. -/
theorem exists_point_of_cylinders {J : ℕ → Finset ι}
    {K : ∀ n, Set (∀ j : J n, α j)} (hKc : ∀ n, IsCompact (K n))
    (hKcl : ∀ n, IsClosed (K n))
    (hne : ∀ n, (⋂ k ∈ Finset.range (n + 1), cylinder (J k) (K k)).Nonempty) :
    ∃ x : ∀ i, α i, ∀ k, x ∈ cylinder (J k) (K k) := by
  classical
  obtain ⟨x₀, -⟩ := hne 0
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := hne n
    have hx' : x ∈ cylinder (J n) (K n) :=
      Set.mem_iInter₂.mp hx n
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_self n)))
    exact ⟨Finset.restrict (J n) x, hx'⟩
  -- The coordinate union and, for each coordinate in it, the first index
  -- whose finset contains it.
  set Jun : Set ι := ⋃ n, ↑(J n) with hJun
  have memJun : ∀ i : ι, i ∈ Jun ↔ ∃ n, i ∈ J n := by
    intro i
    simp [hJun]
  have hex : ∀ i : ↥Jun, ∃ n, i.1 ∈ J n := fun i ↦ (memJun i.1).mp i.2
  let kf : ↥Jun → ℕ := fun i ↦ Nat.find (hex i)
  have hkf_mem : ∀ i, i.1 ∈ J (kf i) := fun i ↦ Nat.find_spec (hex i)
  have hkf_min : ∀ (i : ↥Jun) (m : ℕ), i.1 ∈ J m → kf i ≤ m :=
    fun i m hm ↦ Nat.find_min' (hex i) hm
  -- The coordinate compacts.
  set A : ∀ i : ↥Jun, Set (α i.1) :=
    fun i ↦ (fun y : ∀ j : J (kf i), α j ↦ y ⟨i.1, hkf_mem i⟩) '' K (kf i) with hA
  have hA_compact : ∀ i, IsCompact (A i) := by
    intro i
    show IsCompact ((fun y : ∀ j : J (kf i), α j ↦ y ⟨i.1, hkf_mem i⟩) '' K (kf i))
    exact (hKc (kf i)).image (continuous_apply _)
  have hA_ne : ∀ i, (A i).Nonempty :=
    fun i ↦ (hKne (kf i)).image _
  -- The compact product of the coordinate compacts, as a set.
  set W : Set (∀ i : ↥Jun, α i.1) := Set.univ.pi A with hW
  have hW_compact : IsCompact W := isCompact_univ_pi hA_compact
  -- The constraint sets in the subtype `↥W`.
  set φ : ∀ k : ℕ, ↥W → ∀ j : J k, α j :=
    fun k y j ↦ y.1 ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩ with hφdef
  have hφ_cont : ∀ k, Continuous (φ k) := by
    intro k
    refine continuous_pi_iff.mpr (fun j ↦ ?_)
    show Continuous fun y : ↥W ↦ y.1 ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩
    exact (continuous_apply (A := fun i : ↥Jun ↦ α i.1) ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩).comp continuous_subtype_val
  set Y : ℕ → Set ↥W :=
    fun n ↦ ⋂ k ∈ Finset.range (n + 1), (φ k) ⁻¹' K k with hYdef
  have hY_closed : ∀ n, IsClosed (Y n) := by
    intro n
    exact isClosed_biInter (fun k _ ↦ (hKcl k).preimage (hφ_cont k))
  have hY_step : ∀ n, Y (n + 1) ⊆ Y n := by
    intro n x hx
    exact Set.mem_iInter₂.mpr (fun k hk ↦ Set.mem_iInter₂.mp hx k
      (Finset.mem_coe.mpr (Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_coe.mp hk)) (Nat.le_succ (n + 1))))))
  have hY_ne : ∀ n, (Y n).Nonempty := by
    intro n
    obtain ⟨xh, hxh⟩ := hne n
    have hxhk : ∀ k ≤ n, Finset.restrict (J k) xh ∈ K k := by
      intro k hk
      exact Set.mem_iInter₂.mp hxh k
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    choose a ha using hA_ne
    have hw : ∀ i, (if kf i ≤ n then xh i.1 else a i) ∈ A i := by
      intro i
      by_cases h : kf i ≤ n
      · rw [ite_eq_left h]
        exact ⟨Finset.restrict (J (kf i)) xh, hxhk (kf i) h, rfl⟩
      · rw [ite_eq_right h]
        exact ha i
    refine ⟨⟨fun i ↦ if kf i ≤ n then xh i.1 else a i, Set.mem_univ_pi.mpr hw⟩, ?_⟩
    refine Set.mem_iInter₂.mpr (fun k hk ↦ ?_)
    have hk_le : k ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_coe.mp hk))
    have hφeq : φ k ⟨fun i ↦ if kf i ≤ n then xh i.1 else a i, Set.mem_univ_pi.mpr hw⟩
        = Finset.restrict (J k) xh := by
      funext j
      show (if kf ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩ ≤ n then xh j.1
        else a ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩) = xh j.1
      exact ite_eq_left (le_trans (hkf_min ⟨j.1, (memJun j.1).mpr ⟨k, j.2⟩⟩ k j.2) hk_le)
    show φ k ⟨fun i ↦ if kf i ≤ n then xh i.1 else a i, Set.mem_univ_pi.mpr hw⟩ ∈ K k
    rw [hφeq]
    exact hxhk k hk_le
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Y
    hY_step hY_ne (isCompact_iff_isCompact_univ.mp hW_compact |>.of_isClosed_subset
      (hY_closed 0) (Set.subset_univ _)) hY_closed
  refine ⟨fun i ↦ if h : i ∈ Jun then y.1 ⟨i, h⟩ else x₀ i, fun k ↦ ?_⟩
  have hyk : φ k y ∈ K k :=
    Set.mem_iInter₂.mp (Set.mem_iInter.mp hy k) k
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_self k)))
  show Finset.restrict (J k) (fun i ↦ if h : i ∈ Jun then y.1 ⟨i, h⟩ else x₀ i) ∈ K k
  convert hyk using 2
  funext j
  show (if h : j.1 ∈ Jun then y.1 ⟨j.1, h⟩ else x₀ j.1) = φ k y j
  rw [dite_eq_left ((memJun j.1).mpr ⟨k, j.2⟩)]

/-- Geometric bound for the approximation errors in B2:
`∑_{k<m} δ₀·(1/2)^{k+2} ≤ δ₀·(1/2)` in `ℝ≥0`. -/
theorem nnreal_sum_geometric_half_le (δ₀ : ℝ≥0) (m : ℕ) :
    ∑ k ∈ Finset.range m, (δ₀ * (1 / 2 : ℝ≥0) ^ (k + 2)) ≤ δ₀ * (1 / 2) := by
  have hsum : ∀ m : ℕ, (∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k) + 2 * (1 / 2) ^ m = 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h2 : (2 : ℝ≥0) * (1 / 2) ^ (m + 1) = (1 / 2) ^ m := by
        calc (2 : ℝ≥0) * (1 / 2) ^ (m + 1) = (1 / 2) ^ m * ((2 : ℝ≥0) * (1 / 2)) := by
              rw [pow_succ]; ring
          _ = (1 / 2) ^ m := by norm_num
      calc (∑ k ∈ Finset.range (m + 1), (1 / 2 : ℝ≥0) ^ k) + 2 * (1 / 2) ^ (m + 1)
          = (∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k) + (1 / 2) ^ m + (1 / 2) ^ m := by
            rw [Finset.sum_range_succ, h2]
        _ = (∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k) + 2 * (1 / 2) ^ m := by ring
        _ = 2 := ih
  have hle : ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k ≤ 2 := by
    intro m
    calc ∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k
        ≤ (∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k) + 2 * (1 / 2) ^ m := le_self_add
      _ = 2 := hsum m
  calc ∑ k ∈ Finset.range m, (δ₀ * (1 / 2 : ℝ≥0) ^ (k + 2))
      = δ₀ * (1 / 4) * ∑ k ∈ Finset.range m, (1 / 2 : ℝ≥0) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ ↦ ?_)
        rw [pow_add]
        ring
    _ ≤ δ₀ * (1 / 4) * 2 := mul_le_mul_of_nonneg_left (hle m) (by positivity)
    _ = δ₀ * (1 / 2) := by
        rw [mul_assoc]
        norm_num

/-- **B2 — the compactness heart.** A decreasing sequence of
measurable cylinders whose `projectiveFamilyContent` is bounded
below by some `δ > 0` has nonempty intersection. -/
theorem nonempty_iInter_of_content_ge (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsProbabilityMeasure (P J)] [Countable ι]
    {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ measurableCylinders α)
    (hanti : Antitone s) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hge : ∀ n, δ ≤ projectiveFamilyContent hP (s n)) :
    (⋂ n, s n).Nonempty := by
  classical
  -- A basepoint of the full product, from `content (s 0) ≥ δ > 0`.
  have hs0 : (s 0).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : projectiveFamilyContent hP (s 0) = 0 := by
      rw [hcon, projectiveFamilyContent_congr hP ∅ (cylinder_empty ∅).symm
        MeasurableSet.empty]
      exact measure_empty
    exact (not_le.mpr hδ) (h0 ▸ hge 0)
  obtain ⟨x₀, -⟩ := hs0
  -- Cylinder representations of the `s n`.
  choose I S hS hs_eq using fun n ↦ (mem_measurableCylinders _).mp (hs n)
  -- The combined finsets `J n = ⋃_{k ≤ n} I k` and the combined bases `B n`.
  let J : ℕ → Finset ι := fun n ↦ (Finset.range (n + 1)).biUnion I
  have hIJ : ∀ (n : ℕ) (k : ↥(Finset.range (n + 1))), I k.1 ⊆ J n :=
    fun n k ↦ Finset.subset_biUnion_of_mem I k.2
  have hJJ : ∀ k₀ n : ℕ, k₀ ≤ n → J k₀ ⊆ J n := by
    intro k₀ n h y hy
    obtain ⟨a, ha, hay⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_succ h)), hay⟩
  let B : ∀ n, Set (∀ j : J n, α j) := fun n ↦
    ⋂ k : ↥(Finset.range (n + 1)), Finset.restrict₂ (hIJ n k) ⁻¹' S k.1
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    exact MeasurableSet.iInter (fun k ↦ (hS k.1).preimage (Finset.measurable_restrict₂ _))
  have hB_cyl : ∀ n, cylinder (J n) (B n) = s n := by
    intro n
    ext x
    have key : ∀ k : ↥(Finset.range (n + 1)),
        Finset.restrict₂ (hIJ n k) (Finset.restrict (J n) x) = Finset.restrict (I k.1) x :=
      fun k ↦ rfl
    constructor
    · intro hx
      have hxB : Finset.restrict (J n) x ∈ B n := hx
      have hmem : Finset.restrict₂ (hIJ n ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩)
          (Finset.restrict (J n) x) ∈ S n :=
        Set.mem_iInter.mp hxB ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩
      rw [key] at hmem
      rw [hs_eq n]
      exact hmem
    · intro hx
      show Finset.restrict (J n) x ∈ B n
      rw [Set.mem_iInter]
      intro k
      show Finset.restrict₂ (hIJ n k) (Finset.restrict (J n) x) ∈ S k.1
      rw [key k]
      have hxk : x ∈ s k.1 := hanti (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)) hx
      rw [hs_eq k.1] at hxk
      exact hxk
  have hBn : ∀ n, projectiveFamilyContent hP (s n) = P (J n) (B n) :=
    fun n ↦ projectiveFamilyContent_congr hP (s n) (hB_cyl n).symm (hB_meas n)
  -- `δ ≤ 1`, hence finite; its NNReal shadow is positive.
  have hδle : δ ≤ 1 := by
    refine le_trans (hBn 0 ▸ hge 0) ?_
    rw [← measure_univ (μ := P (J 0))]
    exact measure_mono (Set.subset_univ _)
  have hδfin : δ ≠ ∞ := ne_top_of_le_ne_top (by simp) hδle
  set δ₀ : ℝ≥0 := δ.toNNReal with hδ₀def
  have hδ₀coe : (δ₀ : ℝ≥0∞) = δ := ENNReal.coe_toNNReal hδfin
  have hδ₀pos : 0 < δ₀ := ENNReal.toNNReal_pos hδ.ne' hδfin
  -- Inner-regular approximations of the bases, with geometric errors.
  have hK : ∀ n, ∃ K : Set (∀ j : J n, α j), K ⊆ B n ∧ IsCompact K ∧ IsClosed K ∧
      P (J n) (B n \ K) < ((δ₀ * (1 / 2 : ℝ≥0) ^ (n + 2) : ℝ≥0) : ℝ≥0∞) :=
    fun n ↦ exists_closedCompact_sub (J n) (hB_meas n)
      (ENNReal.coe_pos.mpr (mul_pos hδ₀pos (pow_pos (by norm_num) _)))
  choose K hKB hKc hKcl hKlt using hK
  -- Coherence: the combined bases restrict into each other.
  have hcoh : ∀ (k₀ n : ℕ) (hkn : k₀ ≤ n) (y : ∀ j : J n, α j) (hy : y ∈ B n),
      Finset.restrict₂ (hJJ k₀ n hkn) y ∈ B k₀ := by
    intro k₀ n hkn y hy
    refine Set.mem_iInter.mpr (fun k ↦ ?_)
    have hcomp : Finset.restrict₂ (hIJ k₀ k) (Finset.restrict₂ (hJJ k₀ n hkn) y)
        = Finset.restrict₂ (hIJ n ⟨k.1, Finset.mem_range.mpr
            (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp k.2))
              hkn))⟩) y := rfl
    show Finset.restrict₂ (hIJ k₀ k) (Finset.restrict₂ (hJJ k₀ n hkn) y) ∈ S k.1
    rw [hcomp]
    exact Set.mem_iInter.mp hy ⟨k.1, Finset.mem_range.mpr
      (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)) hkn))⟩
  -- The shrunken bases `DB n = B n ∩ ⋂_{k ≤ n} (restrictions of K k)`.
  let DB : ∀ n, Set (∀ j : J n, α j) := fun n ↦
    B n ∩ ⋂ k : ↥(Finset.range (n + 1)), Finset.restrict₂ (hJJ k.1 n
      (Nat.le_of_lt_succ (Finset.mem_range.mp k.2))) ⁻¹' K k.1
  have hDB_ne : ∀ n, (DB n).Nonempty := by
    intro n
    have hdiff : P (J n) (B n \ DB n) ≤ ((δ₀ * (1 / 2) : ℝ≥0) : ℝ≥0∞) := by
      have hsub : B n \ DB n ⊆ ⋃ k : ↥(Finset.range (n + 1)),
          Finset.restrict₂ (hJJ k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2))) ⁻¹'
            (B k.1 \ K k.1) := by
        intro y hy
        obtain ⟨hyB, hyDB⟩ := hy
        have hnot : y ∉ ⋂ k : ↥(Finset.range (n + 1)), Finset.restrict₂ (hJJ k.1 n
            (Nat.le_of_lt_succ (Finset.mem_range.mp k.2))) ⁻¹' K k.1 := by
          intro hcon
          exact hyDB ⟨hyB, hcon⟩
        have hex : ∃ k : ↥(Finset.range (n + 1)),
            Finset.restrict₂ (hJJ k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2))) y
              ∉ K k.1 := by
          by_contra hcon
          refine hnot (Set.mem_iInter.mpr (fun k ↦ ?_))
          by_contra hk
          exact hcon ⟨k, hk⟩
        obtain ⟨k, hk⟩ := hex
        refine Set.mem_iUnion.mpr ⟨k, ?_⟩
        exact ⟨hcoh k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)) y hyB, hk⟩
      have hterm : ∀ k : ↥(Finset.range (n + 1)),
          P (J n) (Finset.restrict₂ (hJJ k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)))
            ⁻¹' (B k.1 \ K k.1)) = P (J k.1) (B k.1 \ K k.1) := by
        intro k
        have h1 := hP (J n) (J k.1) (hJJ k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)))
        rw [h1, Measure.map_apply (Finset.measurable_restrict₂ _)
          (MeasurableSet.diff (hB_meas k.1) (hKcl k.1).measurableSet)]
      refine le_trans (measure_mono hsub) (le_trans (measure_iUnion_le _) ?_)
      rw [tsum_fintype]
      have hsum_eq : (∑ k : ↥(Finset.range (n + 1)),
            P (J n) (Finset.restrict₂ (hJJ k.1 n (Nat.le_of_lt_succ (Finset.mem_range.mp k.2)))
              ⁻¹' (B k.1 \ K k.1)))
          = ∑ k : ↥(Finset.range (n + 1)), P (J k.1) (B k.1 \ K k.1) :=
        Finset.sum_congr rfl (fun k _ ↦ hterm k)
      rw [hsum_eq]
      have hlt : (∑ k : ↥(Finset.range (n + 1)), P (J k.1) (B k.1 \ K k.1))
          ≤ ∑ k : ↥(Finset.range (n + 1)),
            ((δ₀ * (1 / 2 : ℝ≥0) ^ (k.1 + 2) : ℝ≥0) : ℝ≥0∞) :=
        Finset.sum_le_sum (fun k _ ↦ (hKlt k.1).le)
      refine le_trans hlt ?_
      have hεsum : (∑ k : ↥(Finset.range (n + 1)),
            ((δ₀ * (1 / 2 : ℝ≥0) ^ (k.1 + 2) : ℝ≥0) : ℝ≥0∞))
          = ((∑ k ∈ Finset.range (n + 1), (δ₀ * (1 / 2 : ℝ≥0) ^ (k + 2) : ℝ≥0) : ℝ≥0) :
            ℝ≥0∞) := by
        rw [ENNReal.ofNNReal_finsetSum]
        exact Finset.sum_coe_sort (Finset.range (n + 1))
          (fun j ↦ ((δ₀ * (1 / 2 : ℝ≥0) ^ (j + 2) : ℝ≥0) : ℝ≥0∞))
      rw [hεsum]
      exact ENNReal.coe_le_coe.mpr (nnreal_sum_geometric_half_le δ₀ (n + 1))
    have hhalf : ((δ₀ * (1 / 2) : ℝ≥0) : ℝ≥0∞) = δ / 2 := by
      have h12 : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 1 / 2 := by
        rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
        norm_num
      rw [ENNReal.coe_mul, hδ₀coe, h12, div_eq_mul_inv, div_eq_mul_inv, one_mul]
    have hPDB : P (J n) (DB n) ≠ 0 := by
      by_contra h0
      have hle : P (J n) (B n) ≤ P (J n) (DB n) + P (J n) (B n \ DB n) :=
        le_trans (measure_mono (fun y hy ↦ by
          by_cases hyy : y ∈ DB n
          · exact Set.mem_union_left _ hyy
          · exact Set.mem_union_right _ ⟨hy, hyy⟩)) (measure_union_le _ _)
      rw [h0, zero_add] at hle
      have hδle2 : δ ≤ δ / 2 := le_trans (le_trans (hBn n ▸ hge n) hle) (hhalf ▸ hdiff)
      exact (lt_irrefl δ) (lt_of_le_of_lt hδle2 (ENNReal.half_lt_self hδ.ne' hδfin))
    by_contra hne'
    rw [Set.not_nonempty_iff_eq_empty] at hne'
    rw [hne', measure_empty] at hPDB
    exact hPDB rfl
  -- Finite intersections of the closed compact cylinders are nonempty:
  -- they contain the cylinder over `DB n`.
  have hne' : ∀ n, (⋂ k ∈ Finset.range (n + 1), cylinder (J k) (K k)).Nonempty := by
    intro n
    obtain ⟨y, hy⟩ := hDB_ne n
    refine ⟨fun i ↦ if h : i ∈ J n then y ⟨i, h⟩ else x₀ i, ?_⟩
    rw [Set.mem_iInter₂]
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_coe.mp hk))
    have hfun : Finset.restrict (J k) (fun i ↦ if h : i ∈ J n then y ⟨i, h⟩ else x₀ i)
        = Finset.restrict₂ (hJJ k n hkn) y := by
      funext j
      show (if h : j.1 ∈ J n then y ⟨j.1, h⟩ else x₀ j.1) = y ⟨j.1, hJJ k n hkn j.2⟩
      rw [dite_eq_left (hJJ k n hkn j.2)]
    show Finset.restrict (J k) (fun i ↦ if h : i ∈ J n then y ⟨i, h⟩ else x₀ i) ∈ K k
    rw [hfun]
    exact Set.mem_iInter.mp ((Set.mem_inter_iff _ _ _).mp hy).2 ⟨k, hk⟩
  -- Extraction (B2b) and conclusion.
  obtain ⟨x, hx⟩ := exists_point_of_cylinders hKc hKcl hne'
  refine ⟨x, Set.mem_iInter.mpr (fun n ↦ ?_)⟩
  rw [← hB_cyl n]
  exact hKB n (hx n)

/-- **B2, Tendsto form.** A decreasing sequence of measurable
cylinders with empty intersection has content tending to `0`.
This is the exact hypothesis shape consumed by the pin's
`AddContent.addContent_iUnion_eq_sum_of_tendsto_zero`. -/
theorem projectiveFamilyContent_tendsto_zero (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsProbabilityMeasure (P J)] [Countable ι]
    {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ measurableCylinders α)
    (hanti : Antitone s) (hinter : ⋂ n, s n = ∅) :
    Tendsto (fun n ↦ projectiveFamilyContent hP (s n)) atTop (𝓝 0) := by
  have hanti_m : Antitone (fun n ↦ projectiveFamilyContent hP (s n)) :=
    fun a b hab ↦ projectiveFamilyContent_mono hP (hs b) (hs a) (hanti hab)
  have htend : Tendsto (fun n ↦ projectiveFamilyContent hP (s n)) atTop
      (𝓝 (⨅ n, projectiveFamilyContent hP (s n))) := tendsto_atTop_iInf hanti_m
  have hInf : ⨅ n, projectiveFamilyContent hP (s n) = 0 := by
    by_contra hne
    have hpos : (0 : ℝ≥0∞) < ⨅ n, projectiveFamilyContent hP (s n) :=
      bot_lt_iff_ne_bot.mpr hne
    obtain ⟨x, hx⟩ := nonempty_iInter_of_content_ge hP hs hanti hpos (fun n ↦ iInf_le _ n)
    exact Set.notMem_empty x (hinter ▸ hx)
  rwa [hInf] at htend

/-- **B3 — σ-subadditivity of the projective content.** -/
theorem isSigmaSubadditive_projectiveFamilyContent
    (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsProbabilityMeasure (P J)] [Countable ι] :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hfU hdisj ↦ ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders _
    (fun _ _ ↦ projectiveFamilyContent_ne_top hP) ?_ hf hfU hdisj
  exact fun s hs hanti hinter ↦ projectiveFamilyContent_tendsto_zero hP hs hanti hinter

/-- **MQ3-1 — the Kolmogorov extension theorem (frozen statement).**
For a countable index type and Polish factor spaces, every
projective family of probability measures has a projective
limit measure. -/
theorem exists_isProjectiveLimit (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsProbabilityMeasure (P J)] [Countable ι] :
    ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P := by
  classical
  refine ⟨(projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm.le
    (isSigmaSubadditive_projectiveFamilyContent hP), ?_⟩
  intro I
  ext S hS
  rw [Measure.map_apply _ hS]
  · show (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
        generateFrom_measurableCylinders.symm.le
        (isSigmaSubadditive_projectiveFamilyContent hP) (cylinder I S) = P I S
    rw [AddContent.measure_eq _ isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.symm
      (isSigmaSubadditive_projectiveFamilyContent hP)
      ((mem_measurableCylinders (cylinder I S)).mpr ⟨I, S, hS, rfl⟩)]
    exact projectiveFamilyContent_cylinder hP hS
  · exact .of_eval (fun _ ↦ measurable_pi_apply _)

end ThetLogos
