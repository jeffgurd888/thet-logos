/-
# OrbifoldGapZF5c — ZF-5c: the minimizer is an eigenvector

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg B, brick ZF-5 (third part; attainment was ZF-5b).
Commissioned by Zero, 2026-11-18 18:07 EST ("Fire all three
legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

The Lagrange step of the weighted variational problem, adapting
BridgeCompletion's first-variation argument to the orbit-size
metric. At a weighted-energy minimizer, the weighted bilinear
form vanishes against every weighted-mean-zero perturbation
orthogonal to the minimizer (`wBilin_eq_zero_of_minimizer`): the
normalized perturbation line `F + t • G` stays admissible, and
the linear coefficient of the resulting quadratic inequality
cannot be nonzero. Pairing the first variation against every
weighted-mean-zero test function then reads off that
`laplacianOp quotW F − (foldedGap) • F` is constant, and the
constant dies: its weighted sum is `0` (weighted
self-adjointness against the constant function, which the
operator kills) while the weights have positive total. Hence
the minimizer of ZF-5b is a nonconstant eigenvector of
`laplacianOp quotW` at the folded gap (`foldedGap_eigen`).
-/

import ThetLogos.OrbifoldGapZF5b

namespace ThetLogos
namespace OrbifoldGapPin

/-- First variation at a weighted minimizer: `wBilin F G = 0`
for every weighted-mean-zero `G` weighted-orthogonal to the
minimizer `F`. -/
theorem wBilin_eq_zero_of_minimizer {R : ℕ} {h : ℤ}
    (F G : SliceQuot R h → ℝ) (hF : F ∈ wAdmissible (R := R) (h := h))
    (hmin : ∀ H ∈ wAdmissible (R := R) (h := h), wEnergy F ≤ wEnergy H)
    (hG0 : ∑ o, orbSize o * G o = 0)
    (hGF : ∑ o, orbSize o * G o * F o = 0) :
    wBilin F G = 0 := by
  have key : ∀ t : ℝ, 0 ≤ 2 * t * wBilin F G
      + t ^ 2 * (wEnergy G - wEnergy F * ∑ o, orbSize o * G o ^ 2) := by
    intro t
    have hq0 : (0:ℝ) ≤ ∑ o, orbSize o * G o ^ 2 :=
      Finset.sum_nonneg fun o _ =>
        mul_nonneg (orbSize_pos o).le (sq_nonneg _)
    have hpos : (0:ℝ) < 1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2 :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg t) hq0))
    set s : ℝ := Real.sqrt (1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2) with hs
    have hs2 : s ^ 2 = 1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2 :=
      Real.sq_sqrt hpos.le
    have hsne : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hmem : (s⁻¹ • (F + t • G)) ∈ wAdmissible (R := R) (h := h) := by
      refine ⟨?_, ?_⟩
      · have h1 : ∀ o : SliceQuot R h,
            orbSize o * (s⁻¹ • (F + t • G)) o
              = s⁻¹ * (orbSize o * F o + t * (orbSize o * G o)) := by
          intro o
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          ring
        show (∑ o, orbSize o * (s⁻¹ • (F + t • G)) o) = 0
        rw [Finset.sum_congr rfl (fun o _ => h1 o), ← Finset.mul_sum,
          Finset.sum_add_distrib, ← Finset.mul_sum, hF.1, hG0]
        simp
      · have hnorm : (∑ o, orbSize o * (s⁻¹ • (F + t • G)) o ^ 2)
            = s⁻¹ ^ 2 * (1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2) := by
          have h1 : ∀ o : SliceQuot R h,
              orbSize o * (s⁻¹ • (F + t • G)) o ^ 2
                = s⁻¹ ^ 2 * (orbSize o * (F o + t * G o) ^ 2) := by
            intro o
            simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            ring
          rw [Finset.sum_congr rfl (fun o _ => h1 o), ← Finset.mul_sum]
          congr 1
          have hexp : ∀ o : SliceQuot R h,
              orbSize o * (F o + t * G o) ^ 2
                = orbSize o * F o ^ 2
                  + 2 * t * (orbSize o * (F o * G o))
                  + t ^ 2 * (orbSize o * G o ^ 2) := by
            intro o
            ring
          rw [Finset.sum_congr rfl (fun o _ => hexp o),
            Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          have hFG : (∑ o, orbSize o * (F o * G o)) = 0 := by
            have hcomm : (∑ o, orbSize o * (F o * G o))
                = ∑ o, orbSize o * G o * F o :=
              Finset.sum_congr rfl fun o _ => by ring
            rw [hcomm, hGF]
          rw [hF.2, hFG]
          ring
        show (∑ o, orbSize o * (s⁻¹ • (F + t • G)) o ^ 2) = 1
        rw [hnorm, ← hs2, ← mul_pow, inv_mul_cancel₀ hsne, one_pow]
    have hle := hmin _ hmem
    rw [wEnergy_smul, wEnergy_add_smul] at hle
    have h3 : s ^ 2 * (s⁻¹ ^ 2 * (wEnergy F + 2 * t * wBilin F G
        + t ^ 2 * wEnergy G))
        = wEnergy F + 2 * t * wBilin F G + t ^ 2 * wEnergy G := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hsne, one_pow, one_mul]
    have h4 := mul_le_mul_of_nonneg_left hle (sq_nonneg s)
    rw [h3] at h4
    have h5 : wEnergy F * (1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2)
        = s ^ 2 * wEnergy F := by
      rw [← hs2]
      ring
    have hmul : wEnergy F * (1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2)
        ≤ wEnergy F + 2 * t * wBilin F G + t ^ 2 * wEnergy G := h5 ▸ h4
    have e1 : wEnergy F * (1 + t ^ 2 * ∑ o, orbSize o * G o ^ 2)
        = wEnergy F + t ^ 2 * (wEnergy F * ∑ o, orbSize o * G o ^ 2) := by
      ring
    have e2 : t ^ 2 * (wEnergy G - wEnergy F * ∑ o, orbSize o * G o ^ 2)
        = t ^ 2 * wEnergy G
          - t ^ 2 * (wEnergy F * ∑ o, orbSize o * G o ^ 2) := by
      ring
    rw [e1] at hmul
    rw [e2]
    linarith
  by_contra hB
  set C : ℝ := wEnergy G - wEnergy F * ∑ o, orbSize o * G o ^ 2 with hC
  set u : ℝ := |C| + 1 with hu
  have hu0 : (0:ℝ) < u := by
    have h1 : (0:ℝ) ≤ |C| := abs_nonneg C
    rw [hu]
    linarith
  have hune : u ≠ 0 := ne_of_gt hu0
  have h0 := key (-(wBilin F G) / u)
  have hB2 : (0:ℝ) < (wBilin F G) ^ 2 := sq_pos_of_ne_zero hB
  have h1 : (0:ℝ) ≤ -2 * (wBilin F G) ^ 2 * u
      + (wBilin F G) ^ 2 * C := by
    have h2 := mul_nonneg h0 (sq_nonneg u)
    have h3 : (2 * (-(wBilin F G) / u) * wBilin F G
        + (-(wBilin F G) / u) ^ 2 * C) * u ^ 2
        = -2 * (wBilin F G) ^ 2 * u + (wBilin F G) ^ 2 * C := by
      field_simp
    rwa [h3] at h2
  rw [hu] at h1
  have h4 : (wBilin F G) ^ 2 * C ≤ (wBilin F G) ^ 2 * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self C) hB2.le
  have h5 : (0:ℝ) ≤ (wBilin F G) ^ 2 * |C| :=
    mul_nonneg hB2.le (abs_nonneg C)
  linarith

/-- **Attainment, eigenvector form**: whenever the quotient has
two distinct points, the folded gap is an eigenvalue of
`laplacianOp quotW`, carried by a weighted-admissible —
in particular nonconstant — eigenvector. -/
theorem foldedGap_eigen {R : ℕ} {h : ℤ} {a b : SliceQuot R h}
    (hab : a ≠ b) :
    ∃ G : SliceQuot R h → ℝ, G ∈ wAdmissible (R := R) (h := h)
      ∧ (∃ o o', G o ≠ G o')
      ∧ ∀ o, laplacianOp quotW G o = foldedGap R h * G o := by
  obtain ⟨F, hF, hFE, hmin⟩ := exists_foldedGap_minimizer hab
  refine ⟨F, hF, ?_, ?_⟩
  · -- The minimizer is nonconstant: a constant admissible
    -- potential is `0` by the mean condition, contradicting the
    -- unit condition.
    by_contra hcon
    push_neg at hcon
    have hsum : (∑ o : SliceQuot R h, orbSize o) * F a = 0 := by
      rw [Finset.sum_mul, ← hF.1]
      exact Finset.sum_congr rfl (fun o _ => by rw [hcon o a])
    have hpos : (0:ℝ) < ∑ o : SliceQuot R h, orbSize o :=
      Finset.sum_pos (fun o _ => orbSize_pos o) ⟨a, Finset.mem_univ a⟩
    have hFa : F a = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    have hF0 : F = 0 := by
      funext o
      show F o = 0
      rw [hcon o a, hFa]
    have h2 := hF.2
    rw [hF0] at h2
    simp at h2
  · -- The eigenvector conclusion.
    have hpair : ∀ H : SliceQuot R h → ℝ,
        (∑ o, orbSize o * H o = 0) →
        ∑ o, orbSize o * H o * laplacianOp quotW F o
          = foldedGap R h * ∑ o, orbSize o * H o * F o := by
      intro H hH0
      set c : ℝ := ∑ o, orbSize o * H o * F o with hc
      have hH'0 : ∑ o, orbSize o * (H - c • F) o = 0 := by
        have hterm : ∀ o : SliceQuot R h,
            orbSize o * (H - c • F) o
              = orbSize o * H o - c * (orbSize o * F o) := by
          intro o
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl (fun o _ => hterm o),
          Finset.sum_sub_distrib, ← Finset.mul_sum, hH0, hF.1]
        simp
      have hH'F : ∑ o, orbSize o * (H - c • F) o * F o = 0 := by
        have hterm : ∀ o : SliceQuot R h,
            orbSize o * (H - c • F) o * F o
              = orbSize o * H o * F o
                - c * (orbSize o * F o * F o) := by
          intro o
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have hFF : (∑ o, orbSize o * F o * F o) = 1 := by
          rw [← hF.2]
          exact Finset.sum_congr rfl (fun o _ => by ring)
        rw [Finset.sum_congr rfl (fun o _ => hterm o),
          Finset.sum_sub_distrib, ← Finset.mul_sum, hFF, ← hc]
        ring
      have hvar := wBilin_eq_zero_of_minimizer F (H - c • F) hF hmin
        hH'0 hH'F
      have hexp : wBilin F (H - c • F)
          = (∑ o, orbSize o * H o * laplacianOp quotW F o)
            - c * (∑ o, orbSize o * F o * laplacianOp quotW F o) := by
        show (∑ o, orbSize o * (H - c • F) o
            * laplacianOp quotW F o)
          = (∑ o, orbSize o * H o * laplacianOp quotW F o)
            - c * (∑ o, orbSize o * F o * laplacianOp quotW F o)
        have hterm : ∀ o : SliceQuot R h,
            orbSize o * (H - c • F) o * laplacianOp quotW F o
              = orbSize o * H o * laplacianOp quotW F o
                - c * (orbSize o * F o * laplacianOp quotW F o) := by
          intro o
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl (fun o _ => hterm o),
          Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hFE' : (∑ o, orbSize o * F o * laplacianOp quotW F o)
          = foldedGap R h := hFE
      rw [hexp, hFE'] at hvar
      have hS : (∑ o, orbSize o * H o * laplacianOp quotW F o)
          = foldedGap R h * c := by linarith [hvar]
      rwa [hc] at hS
    -- The defect `D = L F − μ • F` pairs to zero against every
    -- weighted-mean-zero test function, hence is constant.
    set D : SliceQuot R h → ℝ :=
      fun o => laplacianOp quotW F o - foldedGap R h * F o with hDdef
    have hDpair : ∀ H : SliceQuot R h → ℝ,
        (∑ o, orbSize o * H o = 0) →
        ∑ o, orbSize o * H o * D o = 0 := by
      intro H hH0
      have hpairH := hpair H hH0
      have hterm : ∀ o : SliceQuot R h,
          orbSize o * H o * D o
            = orbSize o * H o * laplacianOp quotW F o
              - foldedGap R h * (orbSize o * H o * F o) := by
        intro o
        show orbSize o * H o
            * (laplacianOp quotW F o - foldedGap R h * F o)
          = orbSize o * H o * laplacianOp quotW F o
            - foldedGap R h * (orbSize o * H o * F o)
        ring
      rw [Finset.sum_congr rfl (fun o _ => hterm o),
        Finset.sum_sub_distrib, ← Finset.mul_sum, hpairH, sub_self]
    have hDconst : ∀ o₁ o₂ : SliceQuot R h, D o₁ = D o₂ := by
      intro o₁ o₂
      by_cases ho : o₁ = o₂
      · rw [ho]
      · have hH := hDpair
          (fun o => if o = o₁ then orbSize o₂
            else if o = o₂ then -orbSize o₁ else 0) (by
            have hsub : (∑ o ∈ ({o₁, o₂} : Finset (SliceQuot R h)),
                orbSize o * (if o = o₁ then orbSize o₂
                  else if o = o₂ then -orbSize o₁ else 0))
                = ∑ o, orbSize o * (if o = o₁ then orbSize o₂
                  else if o = o₂ then -orbSize o₁ else 0) := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro o _ ho2
              rw [Finset.mem_insert, Finset.mem_singleton] at ho2
              push_neg at ho2
              rw [if_neg ho2.1, if_neg ho2.2, mul_zero]
            rw [← hsub, Finset.sum_pair ho,
              if_pos rfl, if_neg (Ne.symm ho), if_pos rfl]
            ring)
        have hval : (∑ o, orbSize o * (if o = o₁ then orbSize o₂
            else if o = o₂ then -orbSize o₁ else 0) * D o)
            = orbSize o₁ * orbSize o₂ * (D o₁ - D o₂) := by
          have hsub : (∑ o ∈ ({o₁, o₂} : Finset (SliceQuot R h)),
              orbSize o * (if o = o₁ then orbSize o₂
                else if o = o₂ then -orbSize o₁ else 0) * D o)
              = ∑ o, orbSize o * (if o = o₁ then orbSize o₂
                else if o = o₂ then -orbSize o₁ else 0) * D o := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro o _ ho2
            rw [Finset.mem_insert, Finset.mem_singleton] at ho2
            push_neg at ho2
            rw [if_neg ho2.1, if_neg ho2.2]
            simp
          rw [← hsub, Finset.sum_pair ho,
            if_pos rfl, if_neg (Ne.symm ho), if_pos rfl]
          ring
        rw [hval] at hH
        have hne : orbSize o₁ * orbSize o₂ ≠ 0 :=
          mul_ne_zero (orbSize_pos o₁).ne' (orbSize_pos o₂).ne'
        rcases mul_eq_zero.mp hH with h | h
        · exact absurd h hne
        · exact sub_eq_zero.mp h
    -- The constant defect has weighted sum `0`, and the weights
    -- have positive total: the defect vanishes.
    have hLF0 : ∑ o, orbSize o * laplacianOp quotW F o = 0 := by
      have hsa := quotW_weighted_self_adjoint (fun _ => (1:ℝ)) F
      have e1 : ∀ o : SliceQuot R h,
          orbSize o * laplacianOp quotW (fun _ => (1:ℝ)) o * F o
            = 0 := by
        intro o
        rw [laplacianOp_const]
        simp
      have e2 : ∀ o : SliceQuot R h,
          orbSize o * (fun _ => (1:ℝ)) o * laplacianOp quotW F o
            = orbSize o * laplacianOp quotW F o := by
        intro o
        show orbSize o * 1 * laplacianOp quotW F o
          = orbSize o * laplacianOp quotW F o
        rw [mul_one]
      rw [Finset.sum_congr rfl (fun o _ => e1 o),
        Finset.sum_congr rfl (fun o _ => e2 o)] at hsa
      rw [Finset.sum_const_zero] at hsa
      exact hsa.symm
    have hDsum : ∑ o, orbSize o * D o = 0 := by
      have hterm : ∀ o : SliceQuot R h,
          orbSize o * D o = orbSize o * laplacianOp quotW F o
            - foldedGap R h * (orbSize o * F o) := by
        intro o
        show orbSize o
            * (laplacianOp quotW F o - foldedGap R h * F o)
          = orbSize o * laplacianOp quotW F o
            - foldedGap R h * (orbSize o * F o)
        ring
      rw [Finset.sum_congr rfl (fun o _ => hterm o),
        Finset.sum_sub_distrib, ← Finset.mul_sum, hF.1, hLF0]
      simp
    have hsumD : (∑ o : SliceQuot R h, orbSize o) * D a = 0 := by
      rw [Finset.sum_mul, ← hDsum]
      exact Finset.sum_congr rfl (fun o _ => by rw [hDconst o a])
    have hpos : (0:ℝ) < ∑ o : SliceQuot R h, orbSize o :=
      Finset.sum_pos (fun o _ => orbSize_pos o) ⟨a, Finset.mem_univ a⟩
    have hDa : D a = 0 := by
      rcases mul_eq_zero.mp hsumD with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    intro o
    have hDo : D o = 0 := (hDconst o a).trans hDa
    have hDo2 : laplacianOp quotW F o - foldedGap R h * F o = 0 := hDo
    exact sub_eq_zero.mp hDo2

end OrbifoldGapPin
end ThetLogos
