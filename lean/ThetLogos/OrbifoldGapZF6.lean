import ThetLogos.OrbifoldGapZF5c

/-!
# OrbifoldGapZF6 — ZF-6: the folded gap is the least quotient
# eigenvalue, and the comparison with the slice (Leg B, headline)

Lane grade. The folded gap of ZF-5 is the least nonconstant
eigenvalue of the quotient operator `laplacianOp quotW` (the
eigenpair of `foldedGap_eigen` attains it, and every nonconstant
quotient eigenpair bounds it below — the μ ≠ 0 case because such an
eigenvector is automatically weighted-mean-zero, the μ = 0 case by
shifting off the weighted mean). Consequently

  `fiedler (sliceW) ≤ foldedGap`,

and equality holds iff the slice carries a cyc-invariant Fiedler
eigenvector (via the banked `fiedler_eq_iff_invariant_eigen`).
This is the general-(R, h) form of the gap comparison: the plain
quotient Fiedler value of ZF-3 is the equal-fibre special case.
-/

namespace ThetLogos
namespace OrbifoldGapPin

variable {R : ℕ} {h : ℤ}

/-- The weighted total of the quotient Laplacian vanishes:
pairing against the constant potential through the weighted
self-adjointness. -/
theorem weighted_sum_laplacianOp_zero (G : SliceQuot R h → ℝ) :
    ∑ o, orbSize o * laplacianOp quotW G o = 0 := by
  have hsa := quotW_weighted_self_adjoint (fun _ => (1:ℝ)) G
  have e1 : ∀ o : SliceQuot R h,
      orbSize o * laplacianOp quotW (fun _ => (1:ℝ)) o * G o
        = 0 := by
    intro o
    rw [laplacianOp_const]
    simp
  have e2 : ∀ o : SliceQuot R h,
      orbSize o * (fun _ => (1:ℝ)) o * laplacianOp quotW G o
        = orbSize o * laplacianOp quotW G o := by
    intro o
    simp
  rw [Finset.sum_congr rfl (fun o _ => e1 o),
    Finset.sum_congr rfl (fun o _ => e2 o)] at hsa
  rw [Finset.sum_const_zero] at hsa
  exact hsa.symm

/-- A weighted-mean-zero nonconstant quotient eigenpair bounds
the folded gap below: its normalization is admissible with
weighted energy exactly `μ`. -/
theorem foldedGap_le_of_mean_zero_eigenpair {a b : SliceQuot R h}
    (hab : a ≠ b) (G : SliceQuot R h → ℝ) (μ : ℝ)
    (hG0 : ∑ o, orbSize o * G o = 0)
    (hGnc : ∃ o o', G o ≠ G o')
    (hG : ∀ o, laplacianOp quotW G o = μ * G o) :
    foldedGap R h ≤ μ := by
  obtain ⟨o₁, o₂, hne⟩ := hGnc
  have hterm_nonneg : ∀ o : SliceQuot R h, 0 ≤ orbSize o * G o ^ 2 :=
    fun o => mul_nonneg (orbSize_pos o).le (sq_nonneg _)
  have hS : 0 < ∑ o, orbSize o * G o ^ 2 := by
    apply Finset.sum_pos' (fun o _ => hterm_nonneg o)
    by_cases ho : G o₁ = 0
    · refine ⟨o₂, Finset.mem_univ o₂, ?_⟩
      have ho₂ : G o₂ ≠ 0 := fun hh => hne (ho.trans hh.symm)
      exact mul_pos (orbSize_pos o₂) (sq_pos_of_ne_zero ho₂)
    · exact ⟨o₁, Finset.mem_univ o₁,
        mul_pos (orbSize_pos o₁) (sq_pos_of_ne_zero ho)⟩
  set s : ℝ := Real.sqrt (∑ o, orbSize o * G o ^ 2) with hs
  have hs2 : s ^ 2 = ∑ o, orbSize o * G o ^ 2 := Real.sq_sqrt hS.le
  have hsne : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have hmean : ∑ o, orbSize o * (s⁻¹ • G) o = 0 := by
    have e : ∀ o : SliceQuot R h,
        orbSize o * (s⁻¹ • G) o = s⁻¹ * (orbSize o * G o) := by
      intro o
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun o _ => e o), ← Finset.mul_sum,
      hG0, mul_zero]
  have hnorm : ∑ o, orbSize o * (s⁻¹ • G) o ^ 2 = 1 := by
    have e : ∀ o : SliceQuot R h,
        orbSize o * (s⁻¹ • G) o ^ 2
          = s⁻¹ ^ 2 * (orbSize o * G o ^ 2) := by
      intro o
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun o _ => e o), ← Finset.mul_sum,
      inv_pow, hs2, inv_mul_cancel₀ hS.ne']
  have hadm : (s⁻¹ • G) ∈ wAdmissible (R := R) (h := h) :=
    ⟨hmean, hnorm⟩
  have hLo : ∀ o : SliceQuot R h,
      laplacianOp quotW (s⁻¹ • G) o = s⁻¹ * (μ * G o) := by
    intro o
    have h1 := congrFun (laplacianOp_smul quotW s⁻¹ G) o
    simpa only [Pi.smul_apply, smul_eq_mul, hG o] using h1
  have hE : wEnergy (s⁻¹ • G) = μ := by
    show (∑ o, orbSize o * (s⁻¹ • G) o
        * laplacianOp quotW (s⁻¹ • G) o) = μ
    have e : ∀ o : SliceQuot R h,
        orbSize o * (s⁻¹ • G) o * laplacianOp quotW (s⁻¹ • G) o
          = s⁻¹ ^ 2 * μ * (orbSize o * G o ^ 2) := by
      intro o
      rw [hLo o]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun o _ => e o), ← Finset.mul_sum]
    have hrw : s⁻¹ ^ 2 * μ * (∑ o, orbSize o * G o ^ 2)
        = μ * (s⁻¹ ^ 2 * (∑ o, orbSize o * G o ^ 2)) := by ring
    rw [hrw, inv_pow, hs2, inv_mul_cancel₀ hS.ne', mul_one]
  have hbdd : BddBelow (wEnergy '' wAdmissible (R := R) (h := h)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨G', _, rfl⟩
    exact wEnergy_nonneg G'
  have hmem : wEnergy (s⁻¹ • G)
      ∈ wEnergy '' wAdmissible (R := R) (h := h) :=
    ⟨s⁻¹ • G, hadm, rfl⟩
  have hle := csInf_le hbdd hmem
  rw [hE] at hle
  exact hle

/-- **Every nonconstant quotient eigenpair bounds the folded
gap below**, at general `(R, h)`. -/
theorem foldedGap_le_of_eigenpair {a b : SliceQuot R h}
    (hab : a ≠ b) (G : SliceQuot R h → ℝ) (μ : ℝ)
    (hGnc : ∃ o o', G o ≠ G o')
    (hG : ∀ o, laplacianOp quotW G o = μ * G o) :
    foldedGap R h ≤ μ := by
  by_cases hμ : μ = 0
  · subst hμ
    obtain ⟨o₁, o₂, hne⟩ := hGnc
    have hT : 0 < ∑ o : SliceQuot R h, orbSize o := by
      apply Finset.sum_pos' (fun o _ => (orbSize_pos o).le)
      exact ⟨a, Finset.mem_univ a, orbSize_pos a⟩
    set m : ℝ := (∑ o, orbSize o * G o)
      / (∑ o : SliceQuot R h, orbSize o) with hm
    have hmT : m * (∑ o : SliceQuot R h, orbSize o)
        = ∑ o, orbSize o * G o := by
      rw [hm]
      exact div_mul_cancel₀ _ hT.ne'
    have hG'0 : ∑ o : SliceQuot R h, orbSize o * (G - (fun _ : SliceQuot R h => m)) o
        = 0 := by
      have e : ∀ o : SliceQuot R h,
          orbSize o * (G - (fun _ : SliceQuot R h => m)) o
            = orbSize o * G o - m * orbSize o := by
        intro o
        show orbSize o * (G o - m) = orbSize o * G o - m * orbSize o
        ring
      rw [Finset.sum_congr rfl (fun o _ => e o),
        Finset.sum_sub_distrib, ← Finset.mul_sum, hmT, sub_self]
    have hG'nc : ∃ o o' : SliceQuot R h,
        (G - (fun _ : SliceQuot R h => m)) o ≠ (G - (fun _ : SliceQuot R h => m)) o' := by
      refine ⟨o₁, o₂, fun hh => hne ?_⟩
      have h1 : G o₁ - m = G o₂ - m := hh
      linarith
    have hG'eig : ∀ o : SliceQuot R h,
        laplacianOp quotW (G - (fun _ : SliceQuot R h => m)) o
        = (0:ℝ) * (G - (fun _ : SliceQuot R h => m)) o := by
      intro o
      have h1 : laplacianOp quotW (G - (fun _ : SliceQuot R h => m)) o
          = laplacianOp quotW G o
            - laplacianOp quotW (fun _ : SliceQuot R h => m) o :=
        congrFun (laplacianOp_sub quotW G (fun _ : SliceQuot R h => m)) o
      rw [h1, laplacianOp_const]
      simp only [Pi.zero_apply, Pi.sub_apply, hG o, zero_mul,
        sub_zero]
    exact foldedGap_le_of_mean_zero_eigenpair hab (G - (fun _ : SliceQuot R h => m))
      0 hG'0 hG'nc hG'eig
  · have hG0 : ∑ o, orbSize o * G o = 0 := by
      have h1 : μ * (∑ o, orbSize o * G o) = 0 := by
        have e : μ * (∑ o, orbSize o * G o)
            = ∑ o, orbSize o * laplacianOp quotW G o := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro o _
          rw [hG o]
          ring
        rw [e, weighted_sum_laplacianOp_zero]
      exact (mul_eq_zero.mp h1).resolve_left hμ
    exact foldedGap_le_of_mean_zero_eigenpair hab G μ hG0 hGnc hG

/-- **Headline (Leg B): the folded gap is the least nonconstant
eigenvalue of the quotient operator** `laplacianOp quotW`, at
general `(R, h)` (given two distinct quotient points). -/
theorem foldedGap_isLeast {a b : SliceQuot R h} (hab : a ≠ b) :
    IsLeast {μ : ℝ | ∃ G : SliceQuot R h → ℝ,
      (∃ o o', G o ≠ G o')
      ∧ ∀ o, laplacianOp quotW G o = μ * G o} (foldedGap R h) := by
  constructor
  · obtain ⟨G, -, hGnc, hGeig⟩ := foldedGap_eigen hab
    exact ⟨G, hGnc, hGeig⟩
  · intro μ hμ
    obtain ⟨G, hGnc, hGeig⟩ := hμ
    exact foldedGap_le_of_eigenpair hab G μ hGnc hGeig

/-- The slice's Fiedler value is at most the folded gap: folding
can only raise the gap, in the folded (weighted) sense at general
`(R, h)`. -/
theorem fiedler_le_foldedGap {a b : SliceQuot R h} (hab : a ≠ b)
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) :
    fiedler (sliceW (R := R) (h := h)) ≤ foldedGap R h := by
  obtain ⟨G, -, hGnc, hGeig⟩ := foldedGap_eigen hab
  exact fiedler_slice_le_of_eigen_quotient hGeig hGnc hcard

/-- **The equality criterion for the folded gap**: the slice's
Fiedler value equals the folded gap iff the slice carries a
cyc-invariant Fiedler eigenvector. -/
theorem fiedler_eq_foldedGap_iff {a b : SliceQuot R h}
    (hab : a ≠ b)
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) :
    fiedler (sliceW (R := R) (h := h)) = foldedGap R h ↔
    ∃ F : Slice R h → ℝ, (∀ p, F (cycSlice R h p) = F p) ∧ F ≠ 0
      ∧ (∑ p, F p = 0)
      ∧ ∀ p, laplacianOp sliceW F p
        = fiedler (sliceW (R := R) (h := h)) * F p := by
  constructor
  · intro heq
    obtain ⟨G, -, hGnc, hGeig⟩ := foldedGap_eigen hab
    have hGeig' : ∀ o, laplacianOp quotW G o
        = fiedler (sliceW (R := R) (h := h)) * G o := by
      intro o
      rw [heq]
      exact hGeig o
    exact (fiedler_eq_iff_invariant_eigen hcard).mp
      ⟨G, hGnc, hGeig'⟩
  · intro hF
    obtain ⟨G, hGnc, hGeig⟩ :=
      (fiedler_eq_iff_invariant_eigen hcard).mpr hF
    have h1 : foldedGap R h ≤ fiedler (sliceW (R := R) (h := h)) :=
      foldedGap_le_of_eigenpair hab G _ hGnc hGeig
    have h2 : fiedler (sliceW (R := R) (h := h)) ≤ foldedGap R h :=
      fiedler_le_foldedGap hab hcard
    exact le_antisymm h2 h1

end OrbifoldGapPin
end ThetLogos
