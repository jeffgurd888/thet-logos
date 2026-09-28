import ThetLogos.Scaffold32

/-!
# ThetLogos.CFKernelBase — shared C_F definitions

Base module for the C_F (massless photon) projector. Contains the
`cfIndicator`/`cfMat` definitions and basic entrywise lemmas, extracted from
`ThetLogos.CFKernel` to break the circular import between `CFKernel` and
`CFKernelClassification`.

Both `ThetLogos.CFKernel` and `ThetLogos.CFKernelClassification` import this
module.
-/

namespace ThetLogos

/-! ## §1. The C_F representative -/

/-- Indicator of the C_F support S = C_SUPPORT ∪ H_SUPPORT = {0,…,17,24,25}. -/
def cfIndicator : I32 → ℂ := fun i =>
  if i.val < 18 ∨ i.val = 24 ∨ i.val = 25 then 1 else 0

/-- The 32×32 representative of C_F = {(λ,λ,0)} at λ = 1: π(1,1,0) = P_C + P_H,
    the diagonal projector onto the C/H support. [D, π(λ,λ,0)] = 0 for all
    λ ∈ ℂ iff [D, cfMat] = 0. Tier T2. -/
def cfMat : Matrix I32 I32 ℂ := Matrix.diagonal cfIndicator

theorem cfMat_apply (i j : I32) :
    cfMat i j = if i = j then cfIndicator i else 0 := by
  unfold cfMat; rw [Matrix.diagonal_apply]

theorem cfMat_apply_ne {i j : I32} (h : i ≠ j) : cfMat i j = 0 := by
  rw [cfMat_apply, if_neg h]

theorem mul_cfMat_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * cfMat) i j = M i j * cfIndicator j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [cfMat_apply, if_pos rfl]
  · intro k _ hkj
    rw [cfMat_apply_ne hkj, mul_zero]

theorem cfMat_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (cfMat * M) i j = cfIndicator i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [cfMat_apply, if_pos rfl]
  · intro k _ hki
    rw [cfMat_apply_ne (Ne.symm hki), zero_mul]

/-- The C_F indicator takes values in {0, 1}. -/
theorem cfIndicator_mem (i : I32) : cfIndicator i = 0 ∨ cfIndicator i = 1 := by
  unfold cfIndicator
  by_cases h : i.val < 18 ∨ i.val = 24 ∨ i.val = 25
  · rw [if_pos h]; right; rfl
  · rw [if_neg h]; left; rfl

end ThetLogos
