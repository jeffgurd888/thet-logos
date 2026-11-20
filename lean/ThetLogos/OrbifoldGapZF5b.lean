/-
# OrbifoldGapZF5b — ZF-5b: the folded gap and its attainment

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg B, brick ZF-5 (second half). Commissioned by Zero,
2026-11-18 18:07 EST ("Fire all three legs"). NO CLAIM. Dials
0/4. Dial-ineligible.**

The folded gap at `(R, h)` is the variational infimum of the
weighted energy over the weighted-admissible potentials of
ZF-5a. This brick proves the variational problem is inhabited
and attained, adapting BridgeCompletion's §2 pattern to the
weighted metric: the admissible set is closed and bounded
(hence compact), it is nonempty whenever the quotient has two
distinct points, the weighted energy is continuous, and so a
minimizer exists whose energy is exactly the folded gap. The
Lagrange step — the minimizer is an eigenvector — is ZF-5c.
-/

import ThetLogos.OrbifoldGapZF5

namespace ThetLogos
namespace OrbifoldGapPin

/-- **The folded gap** at `(R, h)`: the infimum of the weighted
energy over the weighted-admissible potentials — the variational
form of the quotient gap in the orbit-size metric, repairing the
deviation at unequal orbit sizes. -/
noncomputable def foldedGap (R : ℕ) (h : ℤ) : ℝ :=
  sInf (wEnergy (R := R) (h := h) '' wAdmissible (R := R) (h := h))

/-- The weighted energy is continuous in the potential (it is a
polynomial in the coordinates, the operator applied being a
finite sum of coordinates). -/
theorem continuous_wEnergy {R : ℕ} {h : ℤ} :
    Continuous (wEnergy (R := R) (h := h)) := by
  show Continuous fun G : SliceQuot R h → ℝ =>
    ∑ o, orbSize o * G o * laplacianOp quotW G o
  apply continuous_finset_sum
  intro o _
  have hLG : Continuous fun G : SliceQuot R h → ℝ =>
      laplacianOp quotW G o := by
    have hfun : (fun G : SliceQuot R h → ℝ => laplacianOp quotW G o)
        = (fun G => ∑ o', quotW o o' * (G o - G o')) := by
      funext G
      exact laplacianOp_apply quotW G o
    rw [hfun]
    apply continuous_finset_sum
    intro o' _
    apply Continuous.mul continuous_const
    exact Continuous.sub (continuous_apply o) (continuous_apply o')
  exact Continuous.mul
    (Continuous.mul continuous_const (continuous_apply o)) hLG

/-- The weighted-admissible set is closed: both defining
conditions are level sets of continuous maps. -/
theorem isClosed_wAdmissible {R : ℕ} {h : ℤ} :
    IsClosed (wAdmissible (R := R) (h := h)) := by
  have h1 : IsClosed {G : SliceQuot R h → ℝ |
      ∑ o, orbSize o * G o = 0} :=
    isClosed_eq (continuous_finset_sum _ fun o _ =>
      Continuous.mul continuous_const (continuous_apply o))
      continuous_const
  have h2 : IsClosed {G : SliceQuot R h → ℝ |
      ∑ o, orbSize o * G o ^ 2 = 1} :=
    isClosed_eq (continuous_finset_sum _ fun o _ =>
      Continuous.mul continuous_const
        ((continuous_pow 2).comp (continuous_apply o))) continuous_const
  have hset : wAdmissible (R := R) (h := h)
      = {G : SliceQuot R h → ℝ | ∑ o, orbSize o * G o = 0}
        ∩ {G : SliceQuot R h → ℝ | ∑ o, orbSize o * G o ^ 2 = 1} := rfl
  rw [hset]
  exact h1.inter h2

/-- The weighted-admissible set is bounded: every coordinate of
an admissible potential lies in `[−1, 1]` (each weighted square
is one nonnegative term of a sum equal to `1`, and the weights
are at least `1`). -/
theorem isBounded_wAdmissible {R : ℕ} {h : ℤ} :
    Bornology.IsBounded (wAdmissible (R := R) (h := h)) := by
  apply Bornology.IsBounded.subset Metric.isBounded_closedBall
  intro G hG
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro o
  have hge1 : (1:ℝ) ≤ orbSize o := by
    show (1:ℝ) ≤ ((fiber o).card : ℝ)
    have hne : (fiber o).card ≠ 0 := by
      intro hc
      apply fiber_card_ne_zero o
      rw [hc]
      simp
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hsq : orbSize o * G o ^ 2 ≤ ∑ o', orbSize o' * G o' ^ 2 :=
    Finset.single_le_sum
      (fun o' _ => mul_nonneg (orbSize_pos o').le (sq_nonneg _))
      (Finset.mem_univ o)
  rw [hG.2] at hsq
  have hsq2 : G o ^ 2 ≤ 1 :=
    le_trans (le_mul_of_one_le_left (sq_nonneg _) hge1) hsq
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hsq2

/-- The weighted-admissible set is compact. -/
theorem isCompact_wAdmissible {R : ℕ} {h : ℤ} :
    IsCompact (wAdmissible (R := R) (h := h)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_wAdmissible
    isBounded_wAdmissible

/-- The weighted-admissible set is inhabited whenever the
quotient has two distinct points: the two-point potential
`orbSize b` at `a`, `−orbSize a` at `b` is weighted-mean-zero,
and a scalar multiple of it is weighted-unit. -/
theorem wAdmissible_nonempty {R : ℕ} {h : ℤ} {a b : SliceQuot R h}
    (hab : a ≠ b) : (wAdmissible (R := R) (h := h)).Nonempty := by
  classical
  set G₀ : SliceQuot R h → ℝ :=
    fun o => if o = a then orbSize b else if o = b then -orbSize a
      else 0 with hG₀def
  have hG₀a : G₀ a = orbSize b := by
    show (if a = a then orbSize b else if a = b then -orbSize a
      else 0) = orbSize b
    rw [if_pos rfl]
  have hG₀b : G₀ b = -orbSize a := by
    show (if b = a then orbSize b else if b = b then -orbSize a
      else 0) = -orbSize a
    rw [if_neg (Ne.symm hab), if_pos rfl]
  have hG₀off : ∀ o : SliceQuot R h, o ≠ a → o ≠ b → G₀ o = 0 := by
    intro o h1 h2
    show (if o = a then orbSize b else if o = b then -orbSize a
      else 0) = 0
    rw [if_neg h1, if_neg h2]
  have hmean : ∑ o, orbSize o * G₀ o = 0 := by
    have hsub : (∑ o ∈ ({a, b} : Finset (SliceQuot R h)),
        orbSize o * G₀ o) = ∑ o, orbSize o * G₀ o := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro o _ ho
      rw [Finset.mem_insert, Finset.mem_singleton] at ho
      push_neg at ho
      rw [hG₀off o ho.1 ho.2, mul_zero]
    rw [← hsub, Finset.sum_pair hab, hG₀a, hG₀b]
    ring
  set N : ℝ := ∑ o, orbSize o * G₀ o ^ 2 with hNdef
  have hnorm : N
      = orbSize a * orbSize b ^ 2 + orbSize b * orbSize a ^ 2 := by
    rw [hNdef]
    have hsub : (∑ o ∈ ({a, b} : Finset (SliceQuot R h)),
        orbSize o * G₀ o ^ 2) = ∑ o, orbSize o * G₀ o ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro o _ ho
      rw [Finset.mem_insert, Finset.mem_singleton] at ho
      push_neg at ho
      rw [hG₀off o ho.1 ho.2]
      simp
    rw [← hsub, Finset.sum_pair hab, hG₀a, hG₀b]
    ring
  have hN : (0:ℝ) < N := by
    rw [hnorm]
    exact add_pos
      (mul_pos (orbSize_pos a) (pow_pos (orbSize_pos b) 2))
      (mul_pos (orbSize_pos b) (pow_pos (orbSize_pos a) 2))
  set s : ℝ := Real.sqrt N with hsdef
  have hs2 : s ^ 2 = N := Real.sq_sqrt hN.le
  have hsne : s ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  refine ⟨s⁻¹ • G₀, ?_, ?_⟩
  · show (∑ o, orbSize o * (s⁻¹ • G₀) o) = 0
    have hterm : ∀ o : SliceQuot R h,
        orbSize o * (s⁻¹ • G₀) o = s⁻¹ * (orbSize o * G₀ o) := by
      intro o
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.mul_sum,
      hmean, mul_zero]
  · show (∑ o, orbSize o * (s⁻¹ • G₀) o ^ 2) = 1
    have hnormform : (∑ o, orbSize o * (s⁻¹ • G₀) o ^ 2)
        = s⁻¹ ^ 2 * N := by
      have hterm : ∀ o : SliceQuot R h,
          orbSize o * (s⁻¹ • G₀) o ^ 2
            = s⁻¹ ^ 2 * (orbSize o * G₀ o ^ 2) := by
        intro o
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.mul_sum]
    rw [hnormform, ← hs2, ← mul_pow, inv_mul_cancel₀ hsne, one_pow]

/-- **Attainment of the folded gap**: whenever the quotient has
two distinct points, some weighted-admissible potential has
weighted energy exactly `foldedGap R h`, and it minimizes the
weighted energy over the admissible set. -/
theorem exists_foldedGap_minimizer {R : ℕ} {h : ℤ}
    {a b : SliceQuot R h} (hab : a ≠ b) :
    ∃ G : SliceQuot R h → ℝ, G ∈ wAdmissible (R := R) (h := h)
      ∧ wEnergy G = foldedGap R h
      ∧ ∀ H ∈ wAdmissible (R := R) (h := h), wEnergy G ≤ wEnergy H := by
  obtain ⟨G, hGmem, hGmin⟩ := isCompact_wAdmissible.exists_isMinOn
    (wAdmissible_nonempty hab) (continuous_wEnergy).continuousOn
  refine ⟨G, hGmem, ?_, fun H hH => isMinOn_iff.mp hGmin H hH⟩
  have hle1 : wEnergy G ≤ sInf (wEnergy (R := R) (h := h)
      '' wAdmissible (R := R) (h := h)) := by
    apply le_csInf
      ((wAdmissible_nonempty hab).image (wEnergy (R := R) (h := h)))
    rintro x ⟨H, hH, rfl⟩
    exact isMinOn_iff.mp hGmin H hH
  have hle2 : sInf (wEnergy (R := R) (h := h)
      '' wAdmissible (R := R) (h := h)) ≤ wEnergy G := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro x ⟨H, -, rfl⟩
      exact wEnergy_nonneg H
    · exact ⟨G, hGmem, rfl⟩
  exact le_antisymm hle1 hle2

end OrbifoldGapPin
end ThetLogos
