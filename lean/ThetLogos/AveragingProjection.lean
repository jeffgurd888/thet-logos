/-
# The averaging projection (Route B, step T2)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: `whitepaper/gram-clause-scoping-2026-10-23.md`, §4 Route B,
step **T2** — the averaging-projection lemma, a reusable module in
its own right. Steps T3 (word/tensor bookkeeping) and T4 (assembly)
consume this module; nothing of the lattice appears here.

## Content

For a compact group `G`, a Haar probability measure `μ` on `G`
(left-invariant and inversion-invariant, as typeclass hypotheses),
and a continuous finite-dimensional unitary representation `ρ` of
`G` on a complex inner product space `E`, the averaging operator
`A = ∫ g, ρ g ∂μ` is the **orthogonal projection onto the invariant
subspace** `{v | ∀ g, ρ g v = v}`:

* `averagingOperator_idempotent` — `A ∘L A = A` (Haar invariance);
* `averagingOperator_adjoint` — `A.adjoint = A` (unitarity plus
  inversion invariance of `μ`), from the pointwise identity
  `averagingOperator_inner_left`;
* `averagingOperator_range` — the range of `A` is exactly the
  invariant submodule, and `A` acts as the identity there
  (`averagingOperator_of_mem_invariant`);
* `averagingOperator_gram` — `A` is a finite Gram sum over an
  orthonormal basis of its range:
  `A v = ∑ i, ⟪e i, v⟫ • e i`.

No Peter–Weyl, no Schur, no irreducibility anywhere: invariance and
unitarity only.

## Formulation choices (disclosed)

* `E` is an abstract finite-dimensional inner product space over
  `ℂ` and `ρ : G → (E →L[ℂ] E)` carries its representation laws as
  pointwise hypotheses (`hρmul`, `hρone`, `hρunit`, taken as
  explicit binders) rather than a bundled homomorphism type, and
  continuity as `hρcont`. T4 instantiates `E` with the corpus's
  matrix representation space, where unitarity of `ρ` is
  definitional.
* `μ` is an abstract measure with the Haar-probability typeclasses
  `[IsProbabilityMeasure μ]`, `[μ.IsMulLeftInvariant]`,
  `[μ.IsInvInvariant]`; the concrete Haar probability measure is
  supplied at instantiation (T4).

## Fences

This is pure finite-dimensional harmonic analysis: no lattice, no
plaquettes, no `β`, no statement about any gauge theory. **NO
CLAIM** — parts of any official Clay statement closed by this
module: 0.
-/

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

namespace AveragingProjection

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  [μ.IsInvInvariant]
variable (ρ : G → (E →L[ℂ] E))

/-- The integrand of the averaging operator is continuous, hence
integrable against the finite measure `μ`. -/
lemma integrable_apply (hρcont : Continuous ρ) (v : E) :
    Integrable (fun g => ρ g v) μ :=
  ((ContinuousLinearMap.apply ℂ E v).continuous.comp hρcont).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Unitarity of `ρ` says each `ρ g` is norm-preserving. -/
lemma norm_apply (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    (g : G) (v : E) : ‖ρ g v‖ = ‖v‖ := by
  have h : (‖ρ g v‖ : ℝ) ^ 2 = ‖v‖ ^ 2 := by
    have h1 := hρunit g v v
    have h2 := congrArg RCLike.re h1
    rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h2
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h3 | h3
  · exact h3
  · have h4 := norm_nonneg (ρ g v)
    have h5 := norm_nonneg v
    linarith

/-- The averaging operator as a linear map: `v ↦ ∫ g, ρ g v ∂μ`. -/
noncomputable def averagingLinear (hρcont : Continuous ρ) : E →ₗ[ℂ] E where
  toFun v := ∫ g, ρ g v ∂μ
  map_add' v w := by
    simp only [map_add]
    exact integral_add (integrable_apply μ ρ hρcont v)
      (integrable_apply μ ρ hρcont w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul c (fun g => ρ g v)

/-- The averaging operator `A = ∫ g, ρ g ∂μ`, a continuous linear
map of operator norm at most `1`. -/
noncomputable def averagingOperator (hρcont : Continuous ρ)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) : E →L[ℂ] E :=
  (averagingLinear μ ρ hρcont).mkContinuous 1 (fun v => by
    calc ‖averagingLinear μ ρ hρcont v‖
        = ‖∫ g, ρ g v ∂μ‖ := rfl
      _ ≤ ‖v‖ * μ.real Set.univ :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall fun g => le_of_eq (norm_apply ρ hρunit g v))
      _ = 1 * ‖v‖ := by simp [Measure.real])

@[simp]
lemma averagingOperator_apply (hρcont : Continuous ρ)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v : E) :
    averagingOperator μ ρ hρcont hρunit v = ∫ g, ρ g v ∂μ := rfl

/-- Left translating the average reproduces the average: each
`ρ g₀` fixes every vector in the range of `A`. -/
lemma rho_apply_averaging (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    (g₀ : G) (v : E) :
    ρ g₀ (averagingOperator μ ρ hρcont hρunit v)
      = averagingOperator μ ρ hρcont hρunit v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have h1 : ρ g₀ (averagingOperator μ ρ hρcont hρunit v)
      = ∫ g, ρ (g₀ * g) v ∂μ := by
    rw [averagingOperator_apply,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_apply μ ρ hρcont v)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => (hρmul g₀ g v).symm)
  rw [h1, averagingOperator_apply]
  exact integral_mul_left_eq_self (fun g => ρ g v) g₀

/-- The integral form of idempotence: averaging an averaged vector
returns the same integral. -/
lemma integral_rho_apply_averaging (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v : E) :
    ∫ g, ρ g (∫ g', ρ g' v ∂μ) ∂μ = ∫ g, ρ g v ∂μ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have key : ∀ g : G, ρ g (∫ g', ρ g' v ∂μ) = ∫ g', ρ g' v ∂μ := by
    intro g
    rw [← averagingOperator_apply μ ρ hρcont hρunit v]
    exact rho_apply_averaging μ ρ hρcont hρmul hρunit g v
  exact integral_eq_const (Filter.Eventually.of_forall key)

/-- **Idempotence.** `A ∘L A = A`: averaging twice is averaging
once. -/
theorem averagingOperator_idempotent (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    (averagingOperator μ ρ hρcont hρunit) ∘L (averagingOperator μ ρ hρcont hρunit)
      = averagingOperator μ ρ hρcont hρunit := by
  ext v
  rw [ContinuousLinearMap.comp_apply, averagingOperator_apply, averagingOperator_apply]
  exact integral_rho_apply_averaging μ ρ hρcont hρmul hρunit v

/-- The invariant submodule: vectors fixed by every `ρ g`. It is a
submodule from linearity of each `ρ g` alone — no representation
laws are needed. -/
def invariantSubmodule : Submodule ℂ E where
  carrier := {v | ∀ g, ρ g v = v}
  add_mem' := by
    intro v w hv hw g
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, hv g, hw g]
  zero_mem' := by
    intro g
    exact map_zero _
  smul_mem' := by
    intro c v hv g
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [map_smul, hv g]

/-- Every averaged vector is invariant. -/
lemma apply_mem_invariant (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v : E) :
    averagingOperator μ ρ hρcont hρunit v ∈ invariantSubmodule ρ :=
  fun g₀ => rho_apply_averaging μ ρ hρcont hρmul hρunit g₀ v

/-- `A` acts as the identity on invariant vectors. -/
lemma averagingOperator_of_mem_invariant (hρcont : Continuous ρ)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    (v : E) (hv : ∀ g, ρ g v = v) :
    averagingOperator μ ρ hρcont hρunit v = v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  rw [averagingOperator_apply]
  exact integral_eq_const (Filter.Eventually.of_forall hv)

/-- **Range.** The range of `A` is exactly the invariant
submodule. -/
theorem averagingOperator_range (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    LinearMap.range (averagingOperator μ ρ hρcont hρunit).toLinearMap
      = invariantSubmodule ρ := by
  ext v
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact apply_mem_invariant μ ρ hρcont hρmul hρunit w
  · intro hv
    exact ⟨v, averagingOperator_of_mem_invariant μ ρ hρcont hρunit v hv⟩

/-- The inner product against an averaged vector, right slot:
the integral comes out of the (linear) second argument. -/
lemma averagingOperator_inner_right (hρcont : Continuous ρ)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v w : E) :
    ⟪v, averagingOperator μ ρ hρcont hρunit w⟫_ℂ
      = ∫ g, ⟪v, ρ g w⟫_ℂ ∂μ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  rw [averagingOperator_apply]
  exact (ContinuousLinearMap.integral_comp_comm (innerSL ℂ v)
    (integrable_apply μ ρ hρcont w)).symm

/-- The inner product against an averaged vector, left slot:
the integral comes out of the (conjugate-linear) first argument,
via `innerSL` and the semilinear integral commutation. -/
lemma averagingOperator_inner_left (hρcont : Continuous ρ)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v w : E) :
    ⟪averagingOperator μ ρ hρcont hρunit v, w⟫_ℂ
      = ∫ g, ⟪ρ g v, w⟫_ℂ ∂μ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hInt : Integrable (fun g => innerSL ℂ (ρ g v)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.of_compactSpace _)
    exact (innerSL ℂ).continuous.comp
      ((ContinuousLinearMap.apply ℂ E v).continuous.comp hρcont)
  have h2 : (∫ g, innerSL ℂ (ρ g v) ∂μ) w
      = ∫ g, (innerSL ℂ (ρ g v)) w ∂μ :=
    ContinuousLinearMap.integral_apply hInt w
  have h3 : ∫ g, innerSL ℂ (ρ g v) ∂μ = innerSL ℂ (∫ g, ρ g v ∂μ) :=
    ContinuousLinearMap.integral_comp_commSL (L := innerSL ℂ)
      (φ := fun g => ρ g v) (by simp) (integrable_apply μ ρ hρcont v)
  have goal' : (innerSL ℂ (∫ g, ρ g v ∂μ)) w
      = ∫ g, (innerSL ℂ (ρ g v)) w ∂μ := by
    rw [← h3]
    exact h2
  rw [averagingOperator_apply]
  exact goal'

/-- **Self-adjointness, pointwise form.** `⟪A v, w⟫ = ⟪v, A w⟫`:
unitarity moves `ρ g` across the inner product at the cost of an
inversion, and inversion invariance of `μ` absorbs it. -/
theorem self_adjoint_inner (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρone : ∀ v : E, ρ 1 v = v)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) (v w : E) :
    ⟪averagingOperator μ ρ hρcont hρunit v, w⟫_ℂ
      = ⟪v, averagingOperator μ ρ hρcont hρunit w⟫_ℂ := by
  rw [averagingOperator_inner_left μ ρ hρcont hρunit v w,
    averagingOperator_inner_right μ ρ hρcont hρunit v w]
  have pt : ∀ g : G, ⟪ρ g v, w⟫_ℂ = ⟪v, ρ g⁻¹ w⟫_ℂ := by
    intro g
    have h1 : ρ g (ρ g⁻¹ w) = w := by
      rw [← hρmul g g⁻¹ w, mul_inv_cancel, hρone]
    calc ⟪ρ g v, w⟫_ℂ = ⟪ρ g v, ρ g (ρ g⁻¹ w)⟫_ℂ := by rw [h1]
    _ = ⟪v, ρ g⁻¹ w⟫_ℂ := hρunit g v (ρ g⁻¹ w)
  rw [integral_congr_ae (Filter.Eventually.of_forall pt)]
  exact integral_inv_eq_self (fun g => ⟪v, ρ g w⟫_ℂ) μ

/-- **Self-adjointness.** `A.adjoint = A`. -/
theorem averagingOperator_adjoint [CompleteSpace E] (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρone : ∀ v : E, ρ 1 v = v)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    (averagingOperator μ ρ hρcont hρunit).adjoint
      = averagingOperator μ ρ hρcont hρunit :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    (fun x y => self_adjoint_inner μ ρ hρcont hρmul hρone hρunit x y)).symm

/-- Orthogonality: `A v - v` is orthogonal to every invariant
vector — together with idempotence and self-adjointness, `A` is
the orthogonal projection onto its range. -/
lemma inner_apply_sub_left (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρone : ∀ v : E, ρ 1 v = v)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    (v w : E) (hw : ∀ g, ρ g w = w) :
    ⟪averagingOperator μ ρ hρcont hρunit v - v, w⟫_ℂ = 0 := by
  rw [inner_sub_left, sub_eq_zero, self_adjoint_inner μ ρ hρcont hρmul hρone hρunit v w,
    averagingOperator_of_mem_invariant μ ρ hρcont hρunit w hw]

/-- **Finite Gram sum.** Over an orthonormal basis `e` of the
invariant submodule, `A` is the Gram sum
`A v = ∑ i, ⟪e i, v⟫ • e i`: expand `A v` in the basis of its
range and use self-adjointness plus `A eᵢ = eᵢ` on coefficients. -/
theorem averagingOperator_gram (hρcont : Continuous ρ)
    (hρmul : ∀ g h (v : E), ρ (g * h) v = ρ g (ρ h v))
    (hρone : ∀ v : E, ρ 1 v = v)
    (hρunit : ∀ g (v w : E), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    ∃ (m : ℕ) (e : OrthonormalBasis (Fin m) ℂ (invariantSubmodule ρ)),
      ∀ v : E, averagingOperator μ ρ hρcont hρunit v
        = ∑ i, ⟪(e i : E), v⟫_ℂ • (e i : E) := by
  classical
  refine ⟨Module.finrank ℂ (invariantSubmodule ρ),
    stdOrthonormalBasis ℂ (invariantSubmodule ρ), fun v => ?_⟩
  have hmem : averagingOperator μ ρ hρcont hρunit v ∈ invariantSubmodule ρ :=
    apply_mem_invariant μ ρ hρcont hρmul hρunit v
  have hexp := OrthonormalBasis.sum_repr'
    (stdOrthonormalBasis ℂ (invariantSubmodule ρ)) ⟨averagingOperator μ ρ hρcont hρunit v, hmem⟩
  have hexpE : averagingOperator μ ρ hρcont hρunit v
      = ∑ i, ⟪((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E),
          averagingOperator μ ρ hρcont hρunit v⟫_ℂ
        • ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E) := by
    have h := congrArg (Submodule.subtype (invariantSubmodule ρ)) hexp
    rw [_root_.map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [hexpE]
  apply Finset.sum_congr rfl
  intro i _
  have hbi : ∀ g, ρ g ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E)
      = ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E) :=
    ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i).2
  have hAi : averagingOperator μ ρ hρcont hρunit
        ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E)
      = ((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E) :=
    averagingOperator_of_mem_invariant μ ρ hρcont hρunit _ hbi
  have hinner : ⟪((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E),
        averagingOperator μ ρ hρcont hρunit v⟫_ℂ
      = ⟪((stdOrthonormalBasis ℂ (invariantSubmodule ρ)) i : E), v⟫_ℂ := by
    rw [← self_adjoint_inner μ ρ hρcont hρmul hρone hρunit _ v, hAi]
  rw [hinner]

end AveragingProjection
