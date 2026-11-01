import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic
import ThetLogos.ProductTriple

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.TensorCrossNorm - SHELF-12: tensor-product cross norms (2026-11-01)

The spectral-triple integrity audit's tensor-norm gap: `ProductTriple.lean`
owns `opTensor` (= `TensorProduct.map`, ProductTriple.lean:265) with its full
algebra (mul/one/add/smul/neg/sub/zero rules, ProductTriple.lean:272-360) but
NO operator-norm product bound for it, and `BoundedTriple.lean` scoped the
full product estimate out for want of a tensor-product inner product
(BoundedTriple.lean:56-60, and the PIN at the end of that file).

## Step 0 probe (what was found, with citations)

- `opTensor` is a plain linear map: `TensorProduct.map X Y` on
  `S1 \otimes[C] S2` for bare `[AddCommGroup S] [Module C S]` seats
  (ProductTriple.lean:265-269). No norm, inner product, or boundedness API
  for `opTensor` exists anywhere in the corpus (grep over ThetLogos/*.lean).
- The corpus's operator norm in force for `Module.End C S` at
  finite-dimensional generality is the opNorm of the continuous extension:
  `||LinearMap.toContinuousLinearMap A||` (e.g. FermionicInteraction.lean:209,
  ConcreteHilbertRep.lean:83-90). That is the norm used below. (Dot notation
  `A.toContinuousLinearMap` is NOT used: it resolves to the algebra
  equivalence `Module.End.toContinuousLinearMap` and fails to elaborate.)
- This Mathlib pin DOES carry the Hilbert tensor product:
  `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` gives the inner
  product (instInner, line 62), the normed group (line 134) and the
  `InnerProductSpace` instance (line 145) on `E \otimes[k] F`, the elementary
  cross norm `TensorProduct.norm_tmul` (line 147), and the continuous tensor
  map `TensorProduct.mapL` (line 602) with the product bound
  `TensorProduct.norm_mapL_le : ||mapL f g|| <= ||f|| * ||g||` (line 606).
  It has NO norm-equality for `mapL`, and no opNorm-attainment lemma; the
  equality below is proved here (sphere compactness in finite dimensions,
  via `FiniteDimensional.proper`, a theorem not an instance in this pin).
- CONCLUSION OF THE PROBE: the construction's norm is NOT mismatched with
  the Hilbert tensor norm - `opTensor A B` is definitionally
  `TensorProduct.map A B`, whose continuous extension is exactly
  `TensorProduct.mapL (LinearMap.toContinuousLinearMap A)
  (LinearMap.toContinuousLinearMap B)` (`opTensor_toContinuousLinearMap`
  below). The named PARTIAL seam of the pack therefore does NOT trigger;
  the brick lands FULL.

## What is proved (all T1, zero sorrys)

At finite-dimensional Hilbert generality (`InnerProductSpace C`,
`FiniteDimensional C` on both factors):

1. `opTensor_opNorm_le` - THE CROSS BOUND:
   `||LinearMap.toContinuousLinearMap (opTensor A B)||
     <= ||LinearMap.toContinuousLinearMap A|| * ||LinearMap.toContinuousLinearMap B||`.
2. `opTensor_opNorm_eq` - THE CROSS EQUALITY on the nose: the same with `=`
   (reverse inequality by opNorm attainment on the finite-dimensional unit
   sphere, evaluated on an elementary tensor).
3. Sanity package: `tensor_norm_tmul` (elementary-tensor cross norm, the
   found Mathlib vocabulary restated), `opTensor_tmul_norm` (the action on
   an elementary tensor has the product norm), `opTensor_apply_le` (the
   pointwise consumer form of the bound), `opTensor_one_opNorm`
   (`||opTensor 1 1|| = 1` on nontrivial factors).

## Honest seat note (on the face)

`BoundedTriple`'s abstract seats carry their inner product as class DATA
(`AnalyticTripleData.iprod` / `nrm`), not as a Mathlib `InnerProductSpace`
instance, so this module's theorems apply to any seat once equipped with
its Hilbert instance (as the concrete models are); turning the data-carried
`iprod` of an abstract `AnalyticTripleData` into such an instance is a
separate seat-level wiring step, not a gap in `opTensor`'s norm theory.
No claim is made here about `BoundedTriple`'s `nrm`.

NO CLAIM; no dial touched.
-/

section CrossNorm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The continuous extension of `opTensor A B` is Mathlib's continuous
    tensor map `TensorProduct.mapL` of the continuous extensions
    (Tier T1 - proved). This is the bridge the whole brick stands on:
    `opTensor`'s operator norm IS the Hilbert tensor operator norm. -/
theorem opTensor_toContinuousLinearMap (A : Module.End ℂ E) (B : Module.End ℂ F) :
    LinearMap.toContinuousLinearMap (opTensor A B)
      = TensorProduct.mapL (LinearMap.toContinuousLinearMap A)
          (LinearMap.toContinuousLinearMap B) := by
  ext z
  simp [opTensor, TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap']

/-- **THE CROSS BOUND** (Tier T1 - proved): the operator-norm product bound
    the audit flagged as missing -
    `||opTensor A B|| <= ||A|| * ||B||` for the operator norm in force
    (opNorm of the continuous extension). -/
theorem opTensor_opNorm_le (A : Module.End ℂ E) (B : Module.End ℂ F) :
    ‖LinearMap.toContinuousLinearMap (opTensor A B)‖
      ≤ ‖LinearMap.toContinuousLinearMap A‖
        * ‖LinearMap.toContinuousLinearMap B‖ := by
  rw [opTensor_toContinuousLinearMap]
  exact TensorProduct.norm_mapL_le _ _

/-- Pointwise consumer form of the cross bound (Tier T1 - proved):
    `||(opTensor A B) z|| <= (||A|| * ||B||) * ||z||` for every `z`. -/
theorem opTensor_apply_le (A : Module.End ℂ E) (B : Module.End ℂ F)
    (z : E ⊗[ℂ] F) :
    ‖(opTensor A B) z‖
      ≤ (‖LinearMap.toContinuousLinearMap A‖
        * ‖LinearMap.toContinuousLinearMap B‖) * ‖z‖ := by
  have h := ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap (opTensor A B)) z
  rw [LinearMap.coe_toContinuousLinearMap'] at h
  exact h.trans (mul_le_mul_of_nonneg_right (opTensor_opNorm_le A B) (norm_nonneg z))

/-- Elementary-tensor cross norm (Tier T1 - proved): `||x \otimes y|| =
    ||x|| * ||y||` in the Hilbert tensor norm - the found Mathlib vocabulary
    (`TensorProduct.norm_tmul`) restated at the corpus's seats. -/
theorem tensor_norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[ℂ] y‖ = ‖x‖ * ‖y‖ :=
  TensorProduct.norm_tmul x y

/-- The action on an elementary tensor has exactly the product norm
    (Tier T1 - proved): `||(opTensor A B) (x \otimes y)|| = ||A x|| * ||B y||`,
    from `TensorProduct.map_tmul` and the elementary cross norm. -/
theorem opTensor_tmul_norm (A : Module.End ℂ E) (B : Module.End ℂ F)
    (x : E) (y : F) :
    ‖(opTensor A B) (x ⊗ₜ[ℂ] y)‖ = ‖A x‖ * ‖B y‖ := by
  unfold opTensor
  rw [TensorProduct.map_tmul, TensorProduct.norm_tmul]

/-- A unit vector exists in any nontrivial Hilbert space (Tier T1 - proved). -/
theorem exists_norm_eq_one {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [Nontrivial G] :
    ∃ x : G, ‖x‖ = 1 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : G)
  refine ⟨(‖a‖⁻¹ : ℂ) • a, ?_⟩
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg a),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

/-- **OpNorm attainment** (Tier T1 - proved): on a finite-dimensional inner
    product space, a continuous linear endomorphism attains its operator
    norm at a unit vector (the unit sphere is compact). This is the one
    ingredient the equality needs that this Mathlib pin does not carry. -/
theorem exists_unit_apply_norm_eq_opNorm {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [Nontrivial G]
    (f : G →L[ℂ] G) :
    ∃ x : G, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖ := by
  haveI : ProperSpace G := FiniteDimensional.proper ℂ G
  have hcomp : IsCompact (Metric.sphere (0 : G) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : G) 1).Nonempty := by
    obtain ⟨x, hx⟩ := exists_norm_eq_one (G := G)
    exact ⟨x, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx⟩
  obtain ⟨x₀, hx₀, hmax⟩ :=
    hcomp.exists_isMaxOn hne ((continuous_norm.comp f.continuous).continuousOn)
  have hx₀n : ‖x₀‖ = 1 := by
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx₀
  refine ⟨x₀, hx₀n, le_antisymm ?_ ?_⟩
  · exact (ContinuousLinearMap.le_opNorm f x₀).trans_eq (by rw [hx₀n, mul_one])
  · refine ContinuousLinearMap.opNorm_le_bound f (norm_nonneg _) (fun x => ?_)
    by_cases hx : x = 0
    · simp [hx]
    · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : (‖x‖⁻¹ : ℂ) • x ∈ Metric.sphere (0 : G) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul]
        simp [Complex.norm_real, inv_mul_cancel₀ hnx]
      have h1 : ‖f ((‖x‖⁻¹ : ℂ) • x)‖ ≤ ‖f x₀‖ := hmax hu
      have hcast : ‖(‖x‖ : ℂ)⁻¹‖ = ‖x‖⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x)]
      rw [map_smul, norm_smul, hcast] at h1
      calc ‖f x‖ = ‖x‖ * (‖x‖⁻¹ * ‖f x‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hnx, one_mul]
        _ ≤ ‖x‖ * ‖f x₀‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg x)
        _ = ‖f x₀‖ * ‖x‖ := mul_comm _ _

/-- **THE CROSS EQUALITY** (Tier T1 - proved): on finite-dimensional Hilbert
    tensor products the cross bound is an equality on the nose,
    `||opTensor A B|| = ||A|| * ||B||`. The reverse inequality evaluates the
    product operator on `x \otimes y` for opNorm-attaining unit vectors
    `x, y` (zero factors handled by the landed `opTensor_zero_left/right`). -/
theorem opTensor_opNorm_eq (A : Module.End ℂ E) (B : Module.End ℂ F) :
    ‖LinearMap.toContinuousLinearMap (opTensor A B)‖
      = ‖LinearMap.toContinuousLinearMap A‖
        * ‖LinearMap.toContinuousLinearMap B‖ := by
  refine le_antisymm (opTensor_opNorm_le A B) ?_
  by_cases hA : A = 0
  · simp [hA, opTensor_zero_left]
    exact norm_nonneg (0 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F))
  by_cases hB : B = 0
  · simp [hB, opTensor_zero_right]
    exact norm_nonneg (0 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F))
  have hE : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hA (LinearMap.ext fun x => Subsingleton.elim _ _)
  have hF : Nontrivial F := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hB (LinearMap.ext fun y => Subsingleton.elim _ _)
  obtain ⟨x, hx, hAx⟩ :=
    exists_unit_apply_norm_eq_opNorm (LinearMap.toContinuousLinearMap A)
  obtain ⟨y, hy, hBy⟩ :=
    exists_unit_apply_norm_eq_opNorm (LinearMap.toContinuousLinearMap B)
  have hz : ‖x ⊗ₜ[ℂ] y‖ = 1 := by rw [tensor_norm_tmul, hx, hy, mul_one]
  calc ‖LinearMap.toContinuousLinearMap A‖ * ‖LinearMap.toContinuousLinearMap B‖
      = ‖(opTensor A B) (x ⊗ₜ[ℂ] y)‖ := by
        rw [opTensor_tmul_norm, ← hAx, ← hBy,
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
    _ ≤ ‖LinearMap.toContinuousLinearMap (opTensor A B)‖ * ‖x ⊗ₜ[ℂ] y‖ := by
        rw [← LinearMap.coe_toContinuousLinearMap']
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖LinearMap.toContinuousLinearMap (opTensor A B)‖ := by rw [hz, mul_one]

/-- Identity cross norm (Tier T1 - proved): `||opTensor 1 1|| = 1` on
    nontrivial factors, via the landed `opTensor_one`. -/
theorem opTensor_one_opNorm [Nontrivial E] [Nontrivial F] :
    ‖LinearMap.toContinuousLinearMap
        (opTensor (1 : Module.End ℂ E) (1 : Module.End ℂ F))‖ = 1 := by
  have hid : LinearMap.toContinuousLinearMap
        (opTensor (1 : Module.End ℂ E) (1 : Module.End ℂ F)) = 1 := by
    ext z
    simp [opTensor_one, LinearMap.coe_toContinuousLinearMap']
  rw [hid]
  obtain ⟨x, hx⟩ := exists_norm_eq_one (G := E)
  obtain ⟨y, hy⟩ := exists_norm_eq_one (G := F)
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
    rw [one_apply_eq_self, one_mul]
  · have h1 := ContinuousLinearMap.le_opNorm
      (1 : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) (x ⊗ₜ[ℂ] y)
    rwa [one_apply_eq_self, tensor_norm_tmul, hx, hy,
      mul_one, mul_one] at h1

end CrossNorm

#print axioms opTensor_toContinuousLinearMap
#print axioms opTensor_opNorm_le
#print axioms opTensor_apply_le
#print axioms tensor_norm_tmul
#print axioms opTensor_tmul_norm
#print axioms exists_norm_eq_one
#print axioms exists_unit_apply_norm_eq_opNorm
#print axioms opTensor_opNorm_eq
#print axioms opTensor_one_opNorm

end ThetLogos
