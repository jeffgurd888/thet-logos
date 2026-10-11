import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ThetLogos.ConcreteStar

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.ConcreteHilbertRep — Rung 4 Track 2: Hilbert completion + bounded *-representation (2026-10-11)

The Hilbert-space representation picture for the concrete Pauli model
(EVOLVE Track 1, `ConcreteFiniteModel.lean`).

## What this file IS
- §1: Completion — `pauliHilbert_complete` (T1: Mathlib's `CompleteSpace`
  instance) and `pauliHilbert_completion_trivial` (T1: the uniform completion
  of a complete space is the space itself). Discharges the
  `AnalyticTriple.lean` PIN for the concrete model: there is nothing to
  complete — `iprod` is already the Hilbert inner product (`iprod_eq_inner`)
  and `nrm` the Hilbert norm (`nrm_eq_norm`).
- §2: Bounded operators — `endCLM` (T2: the algebra equivalence
  `Module.End.toContinuousLinearMap`, continuity from finite-dimensionality)
  and `repScalCLM` (T2: the scalar representation as a CLM), with T1s
  `repScalCLM_apply`, `repScalCLM_bounded` (sharp constant `‖a‖`),
  `repScalCLM_mul`, `repScalCLM_one`.
- §3: The *-representation — `repScal_is_star_rep` (T1: the adjoint identity
  in the inner product), `repScal_star_eq` (T1: `star (repScal a) =
  repScal (star a)` for the TRUE adjoint star `pauliStarInst`, via
  `pauliStar_is_adjoint`), `endCLM_star` (T1: the CLM adjoint coincides with
  the transported true star on the whole matrix algebra), `repScalCLM_star`
  (T1).
- §4: `BoundedStarRep` (T2 interface) + `repScalBoundedStarRep` (T1 instance).
- §5: T2 WINDOWS — `HilbertCompletionWindow` (what a general
  `AnalyticTripleData` must supply for its Hilbert completion) and
  `ProductHilbertRepWindow` (the product-representation interface).

## HONESTY NOTE
There is NO concrete manifold factor in the repo, so NO product
representation is formed — §5 states the interface as a window, nothing
claimed. The scalar algebra makes this model analytically trivial
(`bddRep` with `C = ‖a‖`); the content here is the *representation
picture* (boundedness, multiplicativity, star-compatibility), not new
gauge content.

## Tier ledger
T2 (definitions/interfaces/instances): `endCLM`, `repScalCLM`,
  `BoundedStarRep`, `HilbertCompletionWindow`, `ProductHilbertRepWindow`,
  `AnalyticTripleData.instRingA`, `AnalyticTripleData.instStarRingA`.
T1 (proved, zero sorrys): `pauliHilbert_complete`,
  `pauliHilbert_completion_trivial`, `repScalCLM_apply`, `repScalCLM_bounded`,
  `repScalCLM_mul`, `repScalCLM_one`, `repScal_is_star_rep`,
  `repScal_star_eq`, `endCLM_star`, `repScalCLM_star`,
  `repScalBoundedStarRep`.
-/

-- ============================================================================
-- §1. Completion (T1 for the concrete model)
-- ============================================================================

/-- The Hilbert space is already complete (Tier T1 — proved): Mathlib's
    `CompleteSpace` instance on `EuclideanSpace ℂ (Fin 2)`. This discharges
    the `AnalyticTriple.lean` PIN ("`CompleteSpace S` unprovable for abstract
    `S`") for the concrete Pauli model. -/
theorem pauliHilbert_complete : CompleteSpace (EuclideanSpace ℂ (Fin 2)) :=
  inferInstance

/-- The Hilbert completion is trivial (Tier T1 — proved): the uniform
    completion of a complete space is uniformly equivalent to the space
    itself. For the Pauli model there is nothing to complete — `iprod` is
    already the full Hilbert inner product (`iprod_eq_inner`) and `nrm` the
    Hilbert norm (`nrm_eq_norm`). -/
theorem pauliHilbert_completion_trivial :
    Nonempty (UniformSpace.Completion (EuclideanSpace ℂ (Fin 2)) ≃ᵤ
      EuclideanSpace ℂ (Fin 2)) :=
  ⟨UniformSpace.Completion.UniformCompletion.completeEquivSelf⟩

-- ============================================================================
-- §2. Bounded operators (T2 defs + T1 laws)
-- ============================================================================

/-- Every endomorphism acts as a bounded operator (Tier T2 — definition):
    the algebra equivalence `Module.End.toContinuousLinearMap`, whose
    continuity half is finite-dimensionality
    (`LinearMap.continuous_of_finiteDimensional`). In particular `pauliD`
    and `pauliGrading` act as bounded operators via `endCLM pauliD`,
    `endCLM pauliGrading`. -/
noncomputable def endCLM : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) ≃ₐ[ℂ]
    (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
  Module.End.toContinuousLinearMap _

/-- The scalar representation as a bounded operator (Tier T2 — definition). -/
noncomputable def repScalCLM (a : ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  endCLM (repScal a)

/-- The bounded scalar representation acts by scalar multiplication
    (Tier T1 — proved). -/
theorem repScalCLM_apply (a : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
    repScalCLM a x = a • x := by
  have h : ∀ (Y : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) (z),
      (endCLM Y) z = Y z := fun _ _ => rfl
  show (endCLM (repScal a)) x = a • x
  rw [h, repScal_smul_one a, LinearMap.smul_apply, Module.End.one_apply]

/-- Bounded with the sharp constant `‖a‖` (Tier T1 — proved): the analytic
    content of `bddRep`, restated as an operator-norm bound. -/
theorem repScalCLM_bounded (a : ℂ) : ‖repScalCLM a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [repScalCLM_apply, norm_smul]

/-- Multiplicative (Tier T1 — proved): `repScal` is an algebra hom and
    `endCLM` is an algebra equiv, so the composite is. -/
theorem repScalCLM_mul (a b : ℂ) :
    repScalCLM (a * b) = repScalCLM a * repScalCLM b := by
  show endCLM (repScal (a * b)) = endCLM (repScal a) * endCLM (repScal b)
  rw [show repScal (a * b) = repScal a * repScal b from map_mul _ _ _,
    show endCLM (repScal a * repScal b) = endCLM (repScal a) * endCLM (repScal b)
      from map_mul _ _ _]

/-- Unital (Tier T1 — proved). -/
theorem repScalCLM_one : repScalCLM 1 = 1 := by
  show endCLM (repScal 1) = 1
  rw [show repScal (1 : ℂ) = 1 from map_one _,
    show endCLM (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) = 1 from map_one _]

-- ============================================================================
-- §3. The *-representation (T1)
-- ============================================================================

/-- The scalar representation's adjoint identity (Tier T1 — proved):
    `⟪π(a) x, y⟫ = ⟪x, π(star a) y⟫`. The algebraic involution on `ℂ` acts as
    the Hilbert adjoint — this is the analytic content of the representation
    being a *-representation. -/
theorem repScal_is_star_rep (a : ℂ) (x y : EuclideanSpace ℂ (Fin 2)) :
    ⟪(repScal a) x, y⟫_ℂ = ⟪x, (repScal (star a)) y⟫_ℂ := by
  have h1 : (repScal a) x = a • x := by
    rw [repScal_smul_one a, LinearMap.smul_apply, Module.End.one_apply]
  have h2 : (repScal (star a)) y = star a • y := by
    rw [repScal_smul_one (star a), LinearMap.smul_apply, Module.End.one_apply]
  rw [h1, h2, inner_smul_left, inner_smul_right, starRingEnd_apply]

/-- The representation respects the star (Tier T1 — proved):
    `star (repScal a) = repScal (star a)` for the TRUE adjoint star
    `pauliStarInst` (NOT the `conjJ` shadow).

    Proof: `pauliStar_is_adjoint` says the algebraic `star` IS the Hilbert
    adjoint; `repScal_is_star_rep` computes that adjoint as `repScal (star a)`;
    inner-product extensionality (`ext_inner_left`) identifies the operators. -/
theorem repScal_star_eq (a : ℂ) : star (repScal a) = repScal (star a) := by
  apply LinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro v
  rw [← pauliStar_is_adjoint, repScal_is_star_rep]

/-- The CLM adjoint coincides with the transported true star on the whole
    matrix algebra (Tier T1 — proved): `star (endCLM X) = endCLM (star X)`,
    where the left `star` is Mathlib's adjoint on continuous linear maps and
    the right is `pauliStarInst`. Via `pauliStar_is_adjoint` +
    `ext_inner_left`. -/
theorem endCLM_star (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    star (endCLM X) = endCLM (star X) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  show ⟪X v, x⟫_ℂ = ⟪v, star X x⟫_ℂ
  exact pauliStar_is_adjoint X v x

/-- The bounded scalar representation is a *-representation (Tier T1 —
    proved): the CLM adjoint of `repScalCLM a` is `repScalCLM (star a)`. -/
theorem repScalCLM_star (a : ℂ) : star (repScalCLM a) = repScalCLM (star a) := by
  show star (endCLM (repScal a)) = endCLM (repScal (star a))
  rw [endCLM_star, repScal_star_eq]

-- ============================================================================
-- §4. The bounded *-representation interface (T2) + instance (T1)
-- ============================================================================

/-- Re-exports (same pattern as `AnalyticTripleData.instAddS` in
    `AnalyticTriple.lean`): TC does not see through the `AnalyticTripleData`
    projection, so the algebra's `Ring`/`StarRing` are re-exported for the
    `BoundedStarRep` interface below. -/
instance AnalyticTripleData.instRingA [α : AnalyticTripleData] :
    Ring α.toTripleData.A := α.toTripleData.ringA

instance AnalyticTripleData.instStarRingA [α : AnalyticTripleData] :
    StarRing α.toTripleData.A := α.toTripleData.starA

/-- A bounded *-representation (Tier T2 — interface): an algebra homomorphism
    from `α`'s algebra into the bounded operators on a Hilbert space `H`,
    intertwining the stars (the CLM adjoint on the operator side, the
    algebra's `StarRing` star on the scalar side). -/
structure BoundedStarRep (α : AnalyticTripleData) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  rep : α.toTripleData.A → (H →L[ℂ] H)
  rep_mul : ∀ a b, rep (a * b) = rep a * rep b
  rep_one : rep 1 = 1
  rep_star : ∀ a, star (rep a) = rep (star a)

/-- The Pauli model's scalar representation as a bounded *-representation
    (Tier T1 — instance data, assembled from §2–§3). -/
noncomputable def repScalBoundedStarRep :
    BoundedStarRep pauliAnalytic (EuclideanSpace ℂ (Fin 2)) where
  rep := repScalCLM
  rep_mul := repScalCLM_mul
  rep_one := repScalCLM_one
  rep_star := repScalCLM_star

-- ============================================================================
-- §5. T2 WINDOWS — completion interface + product scoping (nothing claimed)
-- ============================================================================

/-- T2 WINDOW (interface, no theorems): what a general `AnalyticTripleData`
    must supply for its Hilbert completion.

    The abstract `S` carries no topology, so completeness cannot even be
    *stated* — the window supplies the uniform structure and the completeness
    witness as data. With these, `UniformSpace.Completion.completeEquivSelf`
    identifies the completion with `S` itself (as in
    `pauliHilbert_completion_trivial`); without completeness, the further
    debt would be extending every represented bounded operator to
    `UniformSpace.Completion S`. Discharged for the Pauli model by
    `pauliHilbert_complete`. -/
structure HilbertCompletionWindow (α : AnalyticTripleData) where
  uniformS : UniformSpace α.toTripleData.S
  completeS : @CompleteSpace α.toTripleData.S uniformS

/-- T2 WINDOW (interface only — nothing claimed): the product-representation
    interface.

    There is NO concrete manifold factor in the repo, so NO product
    representation is formed. For a product `M × F` of analytic triples to
    carry a Hilbert-space representation, each factor must supply a bounded
    *-representation on its Hilbert space (`BoundedStarRep`); the remaining
    analytic debt — the Hilbert-space tensor product `H_M ⊗̂ H_F` and the
    tensor representation `(a_M, a_F) ↦ rep_M a_M ⊗̂ rep_F a_F` as bounded
    operators — is stated here as the shape of the interface, not as
    theorems. -/
structure ProductHilbertRepWindow (αM αF : AnalyticTripleData)
    (HM HF : Type*) [NormedAddCommGroup HM] [InnerProductSpace ℂ HM] [CompleteSpace HM]
    [NormedAddCommGroup HF] [InnerProductSpace ℂ HF] [CompleteSpace HF] where
  repM : BoundedStarRep αM HM
  repF : BoundedStarRep αF HF

-- ============================================================================
-- §6. Tier ledger check
-- ============================================================================

#print axioms pauliHilbert_complete
#print axioms pauliHilbert_completion_trivial
#print axioms repScalCLM_apply
#print axioms repScalCLM_bounded
#print axioms repScalCLM_mul
#print axioms repScalCLM_one
#print axioms repScal_is_star_rep
#print axioms repScal_star_eq
#print axioms endCLM_star
#print axioms repScalCLM_star
#print axioms repScalBoundedStarRep

end ThetLogos
