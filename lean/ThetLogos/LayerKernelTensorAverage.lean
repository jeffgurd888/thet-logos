/-
# WP2 character route, Module A, brick A2a — the slot tensor
representation as a continuous linear map

The tensor entry of A1 (`LayerKernelTensorContraction`) is the
`(A, B)` matrix coefficient of a unitary representation of the
finite group `G` on the slot Euclidean space
`EuclideanSpace ℂ (∀ j, Fin (n j))`: the tensor representation of
the slot family `σ`.  This brick packages that representation
as a family of continuous linear maps, following the
common-dimension pattern of `GramWordTensor.occRepCLM`
(rank-one expansion in the joint basis), and proves the
representation laws and unitarity — the exact hypotheses T2's
averaging operator (`AveragingProjection.averagingOperator`)
consumes.  The identification of A1's `tensorAvg` with that
averaging operator, and the channel (Gram) decomposition of
the average, are brick A2b.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of this
line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelTensorContraction

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section TensorRepCLM

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [TopologicalSpace G] [DiscreteTopology G]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {n : κ → ℕ}
  (σ : ∀ j, G →* ↥(Matrix.unitaryGroup (Fin (n j)) ℂ))

/-- Parseval's identity in the slot basis. -/
theorem tensor_inner_eq_sum (x y : EuclideanSpace ℂ (∀ j, Fin (n j))) :
    ⟪x, y⟫_ℂ = ∑ A, star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, x⟫_ℂ)
      * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, y⟫_ℂ := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).sum_repr' x]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [inner_smul_left]
  simp only [← RCLike.star_def]

/-- Two slot vectors with the same basis coefficients are
equal. -/
theorem tensor_ext_of_inner_basis {x y : EuclideanSpace ℂ (∀ j, Fin (n j))}
    (h : ∀ A, ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, x⟫_ℂ
      = ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, y⟫_ℂ) : x = y := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).sum_repr' x]
  conv_rhs => rw [← (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).sum_repr' y]
  exact Finset.sum_congr rfl fun A _ => by rw [h A]

/-- **The tensor representation as a continuous linear map**:
the finite sum of rank-one maps with the `tensorEntry`
coefficients, on the slot Euclidean space. -/
noncomputable def tensorRepCLM (g : G) :
    (EuclideanSpace ℂ (∀ j, Fin (n j))) →L[ℂ]
      (EuclideanSpace ℂ (∀ j, Fin (n j))) :=
  ∑ A : ∀ j, Fin (n j), ∑ B : ∀ j, Fin (n j),
    (tensorEntry σ g A B) • InnerProductSpace.rankOne ℂ
      ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)
      ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)

/-- The tensor CLM applied to a basis vector is the
corresponding column of the tensor entry, expanded in the
basis. -/
theorem tensorRepCLM_apply_basis (g : G) (B : ∀ j, Fin (n j)) :
    tensorRepCLM σ g ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)
      = ∑ A, (tensorEntry σ g A B) •
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A) := by
  classical
  have basis_inner : ∀ A B : ∀ j, Fin (n j),
      ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
        (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B⟫_ℂ
        = if A = B then (1 : ℂ) else 0 :=
    fun A B => (orthonormal_iff_ite.mp
      (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).orthonormal) A B
  simp only [tensorRepCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  refine (Finset.sum_eq_single B (fun C _ hCB => ?_)
    (fun h => (h (Finset.mem_univ B)).elim)).trans ?_
  · rw [show ((tensorEntry σ g A C) • InnerProductSpace.rankOne ℂ
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C))
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)
        = (tensorEntry σ g A C) • (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C,
            (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B⟫_ℂ •
            ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)) from rfl,
      basis_inner, if_neg hCB, zero_smul, smul_zero]
  · rw [show ((tensorEntry σ g A B) • InnerProductSpace.rankOne ℂ
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B))
          ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)
        = (tensorEntry σ g A B) • (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B,
            (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B⟫_ℂ •
            ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A)) from rfl,
      basis_inner, if_pos rfl, one_smul]

/-- **Coefficient identity.** The `(A, B)` matrix coefficient
of the tensor CLM is the tensor entry. -/
theorem tensorRepCLM_inner_basis (g : G) (A B : ∀ j, Fin (n j)) :
    ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
      tensorRepCLM σ g ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)⟫_ℂ
      = tensorEntry σ g A B := by
  classical
  have basis_inner : ∀ A B : ∀ j, Fin (n j),
      ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
        (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B⟫_ℂ
        = if A = B then (1 : ℂ) else 0 :=
    fun A B => (orthonormal_iff_ite.mp
      (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).orthonormal) A B
  rw [tensorRepCLM_apply_basis, inner_sum]
  refine (Finset.sum_eq_single A (fun A' _ hA' => ?_)
    (fun h => (h (Finset.mem_univ A)).elim)).trans ?_
  · rw [inner_smul_right, basis_inner, if_neg (fun h => hA' h.symm), mul_zero]
  · rw [inner_smul_right, basis_inner, if_pos rfl, mul_one]

/-- **Coefficient formula for a general vector.** The `A`-th
basis coefficient of the image of `v` under the tensor CLM is
the matrix product of the tensor-entry row with the
coefficients of `v`. -/
theorem tensorRepCLM_inner_basis_apply (g : G)
    (v : EuclideanSpace ℂ (∀ j, Fin (n j))) (A : ∀ j, Fin (n j)) :
    ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, tensorRepCLM σ g v⟫_ℂ
      = ∑ B, (tensorEntry σ g A B) *
          ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ).sum_repr' v]
  rw [_root_.map_sum, inner_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [map_smul, inner_smul_right, tensorRepCLM_inner_basis, mul_comm]

/-- The tensor CLM depends continuously on the group element:
`G` is finite and discrete, so every such family is
continuous.  This is the continuity hypothesis T2's averaging
operator consumes. -/
theorem tensorRepCLM_continuous : Continuous (tensorRepCLM σ) :=
  continuous_of_discreteTopology

/-- **Unitarity of the tensor CLM.** Each `tensorRepCLM σ g`
preserves the inner product: the tensor entry matrix is
unitary (slot by slot from `Matrix.unitaryGroup`), and
Parseval transports the matrix identity to the Euclidean
space.  This is the unitarity hypothesis T2's averaging
operator consumes. -/
theorem tensorRepCLM_unitary :
    ∀ (g : G) (v w : EuclideanSpace ℂ (∀ j, Fin (n j))),
      ⟪tensorRepCLM σ g v, tensorRepCLM σ g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  classical
  intro g v w
  have hδ : ∀ B C : ∀ j, Fin (n j),
      ∑ A, star (tensorEntry σ g A B) * tensorEntry σ g A C
        = if B = C then (1 : ℂ) else 0 := by
    intro B C
    have hfac : ∀ j : κ, ∑ a : Fin (n j),
        star (repMatrix (σ j) g a (B j)) * repMatrix (σ j) g a (C j)
          = if B j = C j then (1 : ℂ) else 0 := by
      intro j
      have h1 : star (repMatrix (σ j) g) * repMatrix (σ j) g = 1 :=
        mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp (σ j g).2)
      have h2 := congrArg
        (fun N : Matrix (Fin (n j)) (Fin (n j)) ℂ => N (B j) (C j)) h1
      rw [Matrix.mul_apply, Matrix.one_apply] at h2
      simpa only [Matrix.star_apply] using h2
    calc ∑ A, star (tensorEntry σ g A B) * tensorEntry σ g A C
        = ∑ A : ∀ j, Fin (n j), ∏ j, (star (repMatrix (σ j) g (A j) (B j))
            * repMatrix (σ j) g (A j) (C j)) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [tensorEntry, tensorEntry, star_prod, ← Finset.prod_mul_distrib]
      _ = ∏ j, ∑ a : Fin (n j), (star (repMatrix (σ j) g a (B j))
            * repMatrix (σ j) g a (C j)) := by
          rw [Fintype.prod_sum]
      _ = ∏ j, (if B j = C j then (1 : ℂ) else 0) :=
          Finset.prod_congr rfl fun j _ => hfac j
      _ = if B = C then (1 : ℂ) else 0 := by
          rw [prod_indicator_eq]
          by_cases h : B = C
          · rw [if_pos h, if_pos (fun j => congrFun h j)]
          · rw [if_neg h, if_neg (fun hall => h (funext hall))]
  have hmain : (∑ A, star (∑ B, tensorEntry σ g A B *
        ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
        * (∑ C, tensorEntry σ g A C *
        ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C, w⟫_ℂ))
      = ∑ A, star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, v⟫_ℂ)
        * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, w⟫_ℂ := by
    calc (∑ A, star (∑ B, tensorEntry σ g A B *
            ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
          * (∑ C, tensorEntry σ g A C *
            ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C, w⟫_ℂ))
        = ∑ A, ∑ B, ∑ C, (star (tensorEntry σ g A B) * tensorEntry σ g A C)
            * (star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C, w⟫_ℂ) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun B _ =>
            Finset.sum_congr rfl fun C _ => ?_
          simp only [star_mul]
          ring
      _ = ∑ B, ∑ C, ∑ A, (star (tensorEntry σ g A B) * tensorEntry σ g A C)
            * (star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C, w⟫_ℂ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ B, ∑ C, (∑ A, star (tensorEntry σ g A B) * tensorEntry σ g A C)
            * (star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) C, w⟫_ℂ) := by
          refine Finset.sum_congr rfl fun B _ =>
            Finset.sum_congr rfl fun C _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ B, star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B, w⟫_ℂ := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [Finset.sum_eq_single B]
          · rw [hδ B B, if_pos rfl, one_mul]
          · intro C _ hCB
            rw [hδ B C, if_neg (Ne.symm hCB), zero_mul]
          · exact fun h => (h (Finset.mem_univ B)).elim
      _ = ∑ A, star (⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A, w⟫_ℂ := rfl
  rw [tensor_inner_eq_sum, tensor_inner_eq_sum]
  simp only [tensorRepCLM_inner_basis_apply]
  exact hmain

/-- The tensor CLM at the identity is the identity. -/
theorem tensorRepCLM_one : tensorRepCLM σ 1 = 1 := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply tensor_ext_of_inner_basis
  intro A
  rw [tensorRepCLM_inner_basis_apply, ContinuousLinearMap.one_apply]
  have hM : ∀ B : ∀ j, Fin (n j), tensorEntry σ 1 A B
      = if A = B then (1 : ℂ) else 0 := fun B => tensorEntry_one σ A B
  rw [Finset.sum_eq_single A]
  · rw [hM A, if_pos rfl, one_mul]
  · intro B _ hBA
    rw [hM B, if_neg (fun h => hBA h.symm), zero_mul]
  · exact fun h => (h (Finset.mem_univ A)).elim

/-- The tensor CLM is multiplicative in the group element: it
is a representation of `G` by continuous linear maps. -/
theorem tensorRepCLM_mul (g h : G) :
    tensorRepCLM σ (g * h) = tensorRepCLM σ g * tensorRepCLM σ h := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply tensor_ext_of_inner_basis
  intro A
  rw [ContinuousLinearMap.mul_apply]
  simp only [tensorRepCLM_inner_basis_apply, tensorEntry_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ =>
    Finset.sum_congr rfl fun B _ => ?_
  ring

end TensorRepCLM

end ThetLogos
