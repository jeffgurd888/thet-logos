import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import ThetLogos.StoneFiniteDim

namespace ThetLogos

open scoped InnerProductSpace Function
open Topology

/-!
# ThetLogos.SpectralFrontier — Rung 7 Prong 5: bounded spectral calculus + the unbounded frontier frame (2026-10-11)

## Part 1 — Mathlib's bounded spectral API: survey (verified by grep, 2026-10-11)

PRESENT in Mathlib (2026), all bounded:
- Continuous functional calculus for C*-algebras, unital (`cfc`) and non-unital (`cfcₙ`),
  with the spectral mapping property (`cfcHom_map_spectrum`) —
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/`.
- Finite-dimensional spectral theorem for self-adjoint operators
  (`LinearMap.IsSymmetric.eigenvectorBasis`, diagonalization) —
  `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.
- Simultaneous diagonalization of commuting symmetric operators via joint eigenspaces
  (`iSup_iInf_eq_top_of_commute`, `orthogonalFamily_iInf_eigenspaces`) —
  `Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean`.
- Fuglede's theorem — `Mathlib/Analysis/CStarAlgebra/Fuglede.lean`.
- Riesz–Schauder / Fredholm alternative for compact operators
  (`hasEigenvalue_iff_mem_spectrum`) — `Mathlib/Analysis/Normed/Operator/Compact/`.

ABSENT (verified by grep; §2 makes each checkable):
- A *joint* functional calculus, even in finite dimensions — proved here (§1, T1).
  The C*-algebra `cfc` API is strictly single-operator.
- Projection-valued / spectral measures: `grep -rli "projection.valued\|spectral.measure"`
  over `Mathlib/` returns nothing.
- Borel functional calculus, bounded or unbounded: no "Borel functional calculus" in Mathlib.
- The eigenbasis spectral theorem for compact self-adjoint operators (only
  Riesz–Schauder ingredients: `eq_zero_of_forall_hasEigenvalue_eq_zero`,
  `finite_dimensional_eigenspace`).
- Everything unbounded: densely-defined closed operators, unbounded adjoints,
  von Neumann's theorem, the operator Cayley transform, the unbounded spectral
  theorem, unbounded Stone (§2, T5 windows).

## Part 1 results (T1, proved, zero sorrys)

§1 builds the joint functional calculus for a commuting family
`T : Fin n → H →ₗ[ℂ] H` of symmetric operators on a finite-dimensional inner
product space — the finite-dimensional case of joint spectral calculus, where every
operator is bounded and everywhere-defined:
- `jointFC_coordinate`: the calculus recovers each `T i` (joint spectral theorem,
  functional-calculus form).
- `jointFC_one`, `jointFC_mul`, `jointFC_star`: `jointFC T` is a unital
  *-algebra homomorphism from functions on the joint spectrum.
- `jointFC_spectralMapping`: `HasEigenvalue (jointFC T f) μ ↔ μ ∈ f '' jointSpectrum`
  (the spectral mapping property for the joint calculus).
This narrows `JointSpectralCalculusUnbounded_sharp` (`StoneFiniteDim.lean` §4) from
below. None of this is in Mathlib: the `cfc` API handles one operator at a time.

## Part 2 (T5, priced windows)

§2 frames the unbounded frontier as labeled T5 windows with exact mathematical content
and a grep check for each absence: the unbounded adjoint (`UnboundedAdjoint_sharp`),
von Neumann's theorem (`VonNeumannAdjoint_sharp`), the Cayley transform
(`CayleyTransform_sharp`), the unbounded spectral theorem (`SpectralTheoremUnbounded_sharp`),
and the unbounded Borel calculus (`BorelCalculusUnbounded_sharp`). Together with the
two windows in `StoneFiniteDim.lean` §4 (`StoneUnbounded_sharp`,
`JointSpectralCalculusUnbounded_sharp`) this is the complete checkable map of what
stands between the bounded calculus of §1 and unbounded Stone.

## Tier ledger
T1 (proved, zero sorrys): `jointFC_apply_of_mem`, `jointFC_coordinate`, `jointFC_one`,
  `jointFC_mul`, `jointFC_star`, `jointFC_spectralMapping`, plus the projection
  infrastructure (`jointProj_sum_id`, `jointProj_comp_eq_zero`, ...).
T2 (markers/interfaces): `jointEigenspace`, `jointProj`, `jointSpectrum`, `jointFC`
  (all defined, not opaque); §2 markers `UnboundedOp.adjoint`, `UnboundedOp.isClosed`,
  `UnboundedOp.isSelfAdjoint`, `ProjValuedMeasure`, `UnboundedOp.cayley`,
  `isSpectralMeasureOf`, `borelFC`.
T5 (priced windows): `UnboundedAdjoint_sharp`, `VonNeumannAdjoint_sharp`,
  `CayleyTransform_sharp`, `SpectralTheoremUnbounded_sharp`, `BorelCalculusUnbounded_sharp`.
-/

-- ============================================================================
-- §1. Joint functional calculus for commuting symmetric operators (finite-dimensional)
-- ============================================================================

section JointCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {n : ℕ}

/-- The joint eigenspace for a character `χ : Fin n → ℂ` (T2 interface: a plain
    definition). -/
def jointEigenspace (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) : Submodule ℂ H :=
  ⨅ i, Module.End.eigenspace (T i) (χ i)

/-- Joint eigenspaces in finite dimensions are complete, hence admit orthogonal
    projections. -/
instance jointEigenspace_complete (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) :
    CompleteSpace ↥(jointEigenspace T χ) :=
  FiniteDimensional.complete ℂ ↥(jointEigenspace T χ)

/-- Orthogonal projection onto the joint eigenspace, as a plain linear map
    (T2 interface). -/
noncomputable def jointProj (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) : H →ₗ[ℂ] H :=
  (jointEigenspace T χ).starProjection.toLinearMap

/-- Applying a sum of linear maps pointwise (local helper). -/
private theorem sum_apply_linmap (s : Finset (Fin n → ℂ))
    (F : (Fin n → ℂ) → H →ₗ[ℂ] H) (x : H) :
    (∑ χ ∈ s, F χ) x = ∑ χ ∈ s, F χ x := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, LinearMap.add_apply, ih]

/-- The projection lands in the joint eigenspace. -/
theorem jointProj_apply_mem (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) (x : H) :
    jointProj T χ x ∈ jointEigenspace T χ :=
  Submodule.starProjection_apply_mem _ x

/-- The projection fixes its joint eigenspace pointwise. -/
theorem jointProj_apply_self (T : Fin n → H →ₗ[ℂ] H) {χ : Fin n → ℂ} {x : H}
    (hx : x ∈ jointEigenspace T χ) : jointProj T χ x = x :=
  (Submodule.starProjection_eq_self_iff).mpr hx

/-- The projection is symmetric (self-adjoint). -/
theorem jointProj_isSymmetric (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) :
    (jointProj T χ).IsSymmetric :=
  Submodule.starProjection_isSymmetric _

/-- Joint eigenspaces for distinct characters are orthogonal. -/
theorem jointEigenspace_orthogonal (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) {χ ψ : Fin n → ℂ} (hne : χ ≠ ψ) {v w : H}
    (hv : v ∈ jointEigenspace T χ) (hw : w ∈ jointEigenspace T ψ) :
    ⟪v, w⟫_ℂ = 0 := by
  have horth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (𝕜 := ℂ) (E := H)
    (n := Fin n) hsymm
  have h := horth hne ⟨v, hv⟩ ⟨w, hw⟩
  simpa using h

/-- The projection onto `W_χ` kills `W_ψ` for `χ ≠ ψ`. -/
theorem jointProj_apply_of_orthogonal (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) {χ ψ : Fin n → ℂ} (hne : χ ≠ ψ) {w : H}
    (hw : w ∈ jointEigenspace T ψ) : jointProj T χ w = 0 := by
  have h1 : jointProj T χ w ∈ jointEigenspace T χ := jointProj_apply_mem T χ w
  have h2 : jointProj T χ w ∈ (jointEigenspace T χ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hort : ⟪v, w⟫_ℂ = 0 := jointEigenspace_orthogonal T hsymm hne hv hw
    have hsymP := jointProj_isSymmetric T χ
    have h3 : ⟪v, jointProj T χ w⟫_ℂ = ⟪jointProj T χ v, w⟫_ℂ := (hsymP v w).symm
    rw [h3, jointProj_apply_self T hv, hort]
  have hmem : jointProj T χ w ∈ jointEigenspace T χ ⊓ (jointEigenspace T χ)ᗮ :=
    Submodule.mem_inf.mpr ⟨h1, h2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-- Distinct joint projections compose to zero. -/
theorem jointProj_comp_eq_zero (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) {χ ψ : Fin n → ℂ} (hne : χ ≠ ψ) :
    (jointProj T χ).comp (jointProj T ψ) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact jointProj_apply_of_orthogonal T hsymm hne (jointProj_apply_mem T ψ x)

/-- Each joint projection is idempotent. -/
theorem jointProj_comp_self (T : Fin n → H →ₗ[ℂ] H) (χ : Fin n → ℂ) :
    (jointProj T χ).comp (jointProj T χ) = jointProj T χ := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  exact jointProj_apply_self T (jointProj_apply_mem T χ x)

/-- The joint spectrum: characters with nontrivial joint eigenspace, as a finset.
    Finiteness is `ThetLogos.finite_nontrivial_jointEigenspace` (StoneFiniteDim §2). -/
noncomputable def jointSpectrum (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise (Commute on T)) : Finset (Fin n → ℂ) :=
  Set.Finite.toFinset (s := {χ : Fin n → ℂ |
    Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i))}) (by
    show Finite ↥{χ : Fin n → ℂ | Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i))}
    exact finite_nontrivial_jointEigenspace hsymm (fun i j => by
      by_cases h : i = j
      · subst h
        exact Commute.refl _
      · exact hcomm h))

/-- Membership in the joint spectrum. -/
theorem mem_jointSpectrum (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (χ : Fin n → ℂ) :
    χ ∈ jointSpectrum T hsymm hcomm ↔ Nontrivial ↥(jointEigenspace T χ) := by
  show χ ∈ Set.Finite.toFinset _ ↔ _
  rw [Set.Finite.mem_toFinset]
  show Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i)) ↔ _
  rfl

/-- The joint projections sum to the identity ("partition of unity", T1).
    Proof: `y := x - ∑ P_χ x` is orthogonal to every joint eigenspace `W_ψ` — for
    `ψ ∈ σ` only the `ψ`-term of the sum survives (distinct projections kill each
    other), and for `ψ ∉ σ` we have `W_ψ = ⊥` — so `y ∈ ⨅ ψ, (W_ψ)ᗮ`;
    `Submodule.iInf_orthogonal` and `iSup_iInf_eq_top_of_commute` force `y = 0`. -/
theorem jointProj_sum_id (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  rw [sum_apply_linmap]
  suffices h : x - ∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ x = 0 by
    exact (eq_of_sub_eq_zero h).symm
  have key : ∀ ψ : Fin n → ℂ, ∀ w ∈ jointEigenspace T ψ,
      ⟪w, x - ∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ x⟫_ℂ = 0 := by
    intro ψ w hw
    by_cases hψ : ψ ∈ jointSpectrum T hsymm hcomm
    · rw [inner_sub_right, inner_sum]
      have hsum : ∑ χ ∈ jointSpectrum T hsymm hcomm, ⟪w, jointProj T χ x⟫_ℂ
          = ⟪w, x⟫_ℂ := by
        rw [Finset.sum_eq_single ψ]
        · have hsymP := jointProj_isSymmetric T ψ
          have h1 : ⟪w, jointProj T ψ x⟫_ℂ = ⟪jointProj T ψ w, x⟫_ℂ := (hsymP w x).symm
          rw [h1, jointProj_apply_self T hw]
        · intro χ _ hne
          have hsymP := jointProj_isSymmetric T χ
          have h1 : ⟪w, jointProj T χ x⟫_ℂ = ⟪jointProj T χ w, x⟫_ℂ := (hsymP w x).symm
          rw [h1, jointProj_apply_of_orthogonal T hsymm hne hw, inner_zero_left]
        · intro hcon
          exact absurd hψ hcon
      rw [hsum, sub_self]
    · have hnt : ¬ Nontrivial ↥(jointEigenspace T ψ) := fun hnt =>
        hψ ((mem_jointSpectrum T hsymm hcomm ψ).mpr hnt)
      have hss : Subsingleton ↥(jointEigenspace T ψ) :=
        not_nontrivial_iff_subsingleton.mp hnt
      have hw0 : w = 0 := by
        have hzw : (⟨w, hw⟩ : ↥(jointEigenspace T ψ)) = 0 := Subsingleton.elim _ _
        simpa using congrArg Subtype.val hzw
      rw [hw0, inner_zero_left]
  have htop : (⨆ ψ : Fin n → ℂ, jointEigenspace T ψ) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (𝕜 := ℂ) (E := H) (ι := Fin n)
      hsymm hcomm
  have hmem : x - ∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ x
      ∈ ⨅ ψ : Fin n → ℂ, (jointEigenspace T ψ)ᗮ := by
    rw [Submodule.mem_iInf]
    intro ψ
    rw [Submodule.mem_orthogonal]
    intro w hw
    exact key ψ w hw
  rw [Submodule.iInf_orthogonal, htop, Submodule.top_orthogonal_eq_bot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-- The joint functional calculus: `f ↦ Σ_{χ ∈ σ} f(χ) • P_χ` (T2 interface: defined,
    not opaque). For commuting symmetric operators this is the finite-dimensional
    joint spectral calculus; Mathlib's `cfc` API handles only one operator at a time. -/
noncomputable def jointFC (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (f : (Fin n → ℂ) → ℂ) : H →ₗ[ℂ] H :=
  ∑ χ ∈ jointSpectrum T hsymm hcomm, f χ • jointProj T χ

/-- On a joint eigenspace the calculus acts as the scalar `f χ` (T1). -/
theorem jointFC_apply_of_mem (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    {f : (Fin n → ℂ) → ℂ} {χ : Fin n → ℂ}
    (hχ : χ ∈ jointSpectrum T hsymm hcomm) {x : H} (hx : x ∈ jointEigenspace T χ) :
    jointFC T hsymm hcomm f x = f χ • x := by
  classical
  show (∑ ψ ∈ jointSpectrum T hsymm hcomm, f ψ • jointProj T ψ) x = _
  rw [sum_apply_linmap, Finset.sum_eq_single χ]
  · rw [LinearMap.smul_apply, jointProj_apply_self T hx]
  · intro ψ _ hne
    rw [LinearMap.smul_apply, jointProj_apply_of_orthogonal T hsymm hne hx, smul_zero]
  · intro h
    exact absurd hχ h

/-- The calculus acts diagonally on projected vectors (T1). -/
theorem jointFC_apply_proj (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    {f : (Fin n → ℂ) → ℂ} {ψ : Fin n → ℂ}
    (hψ : ψ ∈ jointSpectrum T hsymm hcomm) (x : H) :
    jointFC T hsymm hcomm f (jointProj T ψ x) = f ψ • jointProj T ψ x := by
  classical
  show (∑ χ ∈ jointSpectrum T hsymm hcomm, f χ • jointProj T χ) (jointProj T ψ x) = _
  rw [sum_apply_linmap, Finset.sum_eq_single ψ]
  · rw [LinearMap.smul_apply]
    congr 1
    exact jointProj_apply_self T (jointProj_apply_mem T ψ x)
  · intro χ _ hne
    rw [LinearMap.smul_apply,
      jointProj_apply_of_orthogonal T hsymm hne (jointProj_apply_mem T ψ x), smul_zero]
  · intro h
    exact absurd hψ h

/-- The calculus recovers each operator from its coordinate function: the joint
    spectral theorem in functional-calculus form (T1). -/
theorem jointFC_coordinate (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (i : Fin n) :
    jointFC T hsymm hcomm (fun χ => χ i) = T i := by
  classical
  apply LinearMap.ext
  intro x
  have hPx : x = (∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ) x := by
    have hsum := jointProj_sum_id T hsymm hcomm
    have h2 := congrArg (fun F : H →ₗ[ℂ] H => F x) hsum
    simpa using h2.symm
  have lhs : jointFC T hsymm hcomm (fun χ => χ i) x
      = ∑ χ ∈ jointSpectrum T hsymm hcomm, (χ i) • jointProj T χ x := by
    show (∑ χ ∈ jointSpectrum T hsymm hcomm, (fun χ => χ i) χ • jointProj T χ) x = _
    rw [sum_apply_linmap]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [LinearMap.smul_apply]
  have rhs : T i x = ∑ χ ∈ jointSpectrum T hsymm hcomm, (χ i) • jointProj T χ x := by
    conv_lhs => rw [hPx, sum_apply_linmap, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hmem0 : jointProj T χ x ∈ ⨅ j, Module.End.eigenspace (T j) (χ j) :=
      jointProj_apply_mem T χ x
    have hmem : jointProj T χ x ∈ Module.End.eigenspace (T i) (χ i) :=
      (Submodule.mem_iInf _).mp hmem0 i
    exact Module.End.mem_eigenspace_iff.mp hmem
  rw [lhs, rhs]

/-- The calculus sends `1` to the identity (T1). -/
theorem jointFC_one (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    jointFC T hsymm hcomm 1 = LinearMap.id := by
  classical
  show (∑ χ ∈ jointSpectrum T hsymm hcomm, (1 : (Fin n → ℂ) → ℂ) χ • jointProj T χ)
    = LinearMap.id
  simp only [Pi.one_apply, one_smul]
  exact jointProj_sum_id T hsymm hcomm

/-- The calculus is multiplicative (T1). -/
theorem jointFC_mul (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (f g : (Fin n → ℂ) → ℂ) :
    jointFC T hsymm hcomm (f * g)
      = (jointFC T hsymm hcomm f).comp (jointFC T hsymm hcomm g) := by
  classical
  apply LinearMap.ext
  intro x
  have lhs : jointFC T hsymm hcomm (f * g) x
      = ∑ χ ∈ jointSpectrum T hsymm hcomm, (f χ * g χ) • jointProj T χ x := by
    show (∑ χ ∈ jointSpectrum T hsymm hcomm, (f * g) χ • jointProj T χ) x = _
    rw [sum_apply_linmap]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Pi.mul_apply, LinearMap.smul_apply]
  have rhs : ((jointFC T hsymm hcomm f).comp (jointFC T hsymm hcomm g)) x
      = ∑ χ ∈ jointSpectrum T hsymm hcomm, (f χ * g χ) • jointProj T χ x := by
    rw [LinearMap.comp_apply]
    have hg : jointFC T hsymm hcomm g x
        = ∑ ψ ∈ jointSpectrum T hsymm hcomm, g ψ • jointProj T ψ x := by
      show (∑ ψ ∈ jointSpectrum T hsymm hcomm, g ψ • jointProj T ψ) x = _
      rw [sum_apply_linmap]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [LinearMap.smul_apply]
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [map_smul, jointFC_apply_proj T hsymm hcomm hψ x, smul_comm, ← mul_smul]
  rw [lhs, rhs]

/-- The calculus is star-preserving (T1): with `jointFC_one`/`jointFC_mul` this makes
    `jointFC T` a unital *-algebra homomorphism from functions on the joint spectrum. -/
theorem jointFC_star (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (f : (Fin n → ℂ) → ℂ) :
    (jointFC T hsymm hcomm f).adjoint
      = jointFC T hsymm hcomm (fun χ => star (f χ)) := by
  classical
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro x y
  have e1 : ⟪jointFC T hsymm hcomm (fun χ => star (f χ)) x, y⟫_ℂ
      = ∑ χ ∈ jointSpectrum T hsymm hcomm, f χ * ⟪jointProj T χ x, y⟫_ℂ := by
    show ⟪(∑ χ ∈ jointSpectrum T hsymm hcomm, star (f χ) • jointProj T χ) x, y⟫_ℂ = _
    rw [sum_apply_linmap, sum_inner]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [LinearMap.smul_apply, inner_smul_left]
    congr 1
    exact star_star _
  have e2 : ⟪x, jointFC T hsymm hcomm f y⟫_ℂ
      = ∑ χ ∈ jointSpectrum T hsymm hcomm, f χ * ⟪jointProj T χ x, y⟫_ℂ := by
    show ⟪x, (∑ χ ∈ jointSpectrum T hsymm hcomm, f χ • jointProj T χ) y⟫_ℂ = _
    rw [sum_apply_linmap, inner_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right]
    have hsymP := jointProj_isSymmetric T χ
    rw [← hsymP x y]
  rw [e1, e2]

/-- **Spectral mapping for the joint functional calculus (T1, flagship):** the
    eigenvalues of `jointFC T f` are exactly the values of `f` on the joint spectrum.
    Proof: applying a joint projection `P_ψ` to the eigenvector equation collapses the
    sum to the `ψ`-term (distinct projections kill each other), giving
    `(μ - f ψ) • P_ψ v = 0` with `P_ψ v ≠ 0` for some `ψ`. -/
theorem jointFC_spectralMapping (T : Fin n → H →ₗ[ℂ] H)
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T))
    (f : (Fin n → ℂ) → ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (jointFC T hsymm hcomm f) μ ↔
      μ ∈ f '' ↑(jointSpectrum T hsymm hcomm) := by
  classical
  constructor
  · intro h
    rw [Module.End.hasEigenvalue_iff] at h
    obtain ⟨v, hv_mem, hv_ne⟩ :
        ∃ v ∈ Module.End.eigenspace (jointFC T hsymm hcomm f) μ, v ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply h
      ext w
      constructor
      · intro hw
        rw [(Submodule.mem_bot ℂ)]
        exact hall w hw
      · intro hw
        rw [(Submodule.mem_bot ℂ)] at hw
        rw [hw]
        exact Submodule.zero_mem _
    have hfv : jointFC T hsymm hcomm f v = μ • v :=
      Module.End.mem_eigenspace_iff.mp hv_mem
    have hPv : v = (∑ χ ∈ jointSpectrum T hsymm hcomm, jointProj T χ) v := by
      have hsum := jointProj_sum_id T hsymm hcomm
      have h2 := congrArg (fun F : H →ₗ[ℂ] H => F v) hsum
      simpa using h2.symm
    have hex : ∃ ψ ∈ jointSpectrum T hsymm hcomm, jointProj T ψ v ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hv0 : v = 0 := by
        rw [hPv, sum_apply_linmap]
        exact Finset.sum_eq_zero hall
      exact hv_ne hv0
    obtain ⟨ψ, hψ, hPψne⟩ := hex
    have hP : jointProj T ψ (jointFC T hsymm hcomm f v)
        = jointProj T ψ (μ • v) := by rw [hfv]
    rw [map_smul] at hP
    have hLHS : jointProj T ψ (jointFC T hsymm hcomm f v)
        = f ψ • jointProj T ψ v := by
      have e : jointFC T hsymm hcomm f v
          = ∑ χ ∈ jointSpectrum T hsymm hcomm, f χ • jointProj T χ v := by
        show (∑ χ ∈ jointSpectrum T hsymm hcomm, f χ • jointProj T χ) v = _
        rw [sum_apply_linmap]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [LinearMap.smul_apply]
      rw [e, map_sum]
      simp_rw [map_smul]
      rw [Finset.sum_eq_single ψ]
      · congr 1
        exact jointProj_apply_self T (jointProj_apply_mem T ψ v)
      · intro χ _ hne'
        have h0 : jointProj T ψ (jointProj T χ v) = 0 :=
          jointProj_apply_of_orthogonal T hsymm (Ne.symm hne')
            (jointProj_apply_mem T χ v)
        rw [h0, smul_zero]
      · intro hcon
        exact absurd hψ hcon
    rw [hLHS] at hP
    have hsub : (μ - f ψ) • jointProj T ψ v = 0 := by
      rw [sub_smul, ← hP, sub_self]
    have hμψ : μ - f ψ = 0 := by
      by_contra hne
      have hzero : jointProj T ψ v = 0 := by
        have h2 : jointProj T ψ v
            = (μ - f ψ)⁻¹ • ((μ - f ψ) • jointProj T ψ v) := by
          rw [← mul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [h2, hsub, smul_zero]
      exact hPψne hzero
    exact ⟨ψ, Finset.mem_coe.mpr hψ, (sub_eq_zero.mp hμψ).symm⟩
  · intro h
    obtain ⟨χ, hχmem, hμ⟩ := h
    have hχ : χ ∈ jointSpectrum T hsymm hcomm := Finset.mem_coe.mp hχmem
    haveI hnt := (mem_jointSpectrum T hsymm hcomm χ).mp hχ
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥(jointEigenspace T χ))
    have hxH : (x : H) ≠ 0 := by
      intro hz
      apply hx
      ext
      simpa using hz
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    apply hxH
    have hmem : (x : H) ∈ Module.End.eigenspace (jointFC T hsymm hcomm f) μ := by
      rw [Module.End.mem_eigenspace_iff, jointFC_apply_of_mem T hsymm hcomm hχ x.2, hμ]
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem

end JointCalculus

-- ============================================================================
-- §2. The unbounded frontier, framed as checkable T5 windows
-- ============================================================================
-- Each window states the exact mathematical content Mathlib (2026) lacks, with a
-- grep CHECK a reader can run against `.lake/packages/mathlib/Mathlib/` to confirm
-- the absence. Together with `StoneUnbounded_sharp` and
-- `JointSpectralCalculusUnbounded_sharp` (StoneFiniteDim.lean §4) this is the complete
-- map of what stands between the bounded calculus of §1 and unbounded Stone.
-- Base T2 markers (`UnboundedOp`, `skewAdjoint`, `unboundedExp`,
-- `commutingSelfAdjoint`, `JointSpecMeasure`) live in StoneFiniteDim.lean §4.

/-- **T2 marker:** the adjoint of a densely-defined unbounded operator.
    Opaque: Mathlib has `LinearPMap` (partial linear maps) but no adjoint operation
    on it and no graph-based unbounded-operator API. -/
axiom UnboundedOp.adjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : UnboundedOp H → UnboundedOp H

/-- **T2:** unbounded self-adjointness `A* = A`, domains included (via the adjoint marker). -/
def UnboundedOp.isSelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : UnboundedOp H) : Prop :=
  A.adjoint = A

/-- **T2 marker:** "A is closed" (graph-closed in `H × H`).
    Opaque: no closed-operator API in Mathlib. -/
axiom UnboundedOp.isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : UnboundedOp H → Prop

/-- **T2 marker:** projection-valued measures on `ℝⁿ`.
    Opaque: Mathlib has no spectral measures at all. -/
axiom ProjValuedMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (n : ℕ) : Type

/-- **T2 marker:** "`P` is the spectral measure of the self-adjoint unbounded `A`",
    i.e. `A = ∫ λ dP(λ)`. Opaque. -/
axiom isSpectralMeasureOf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ProjValuedMeasure H 1 → UnboundedOp H → Prop

/-- **T2 marker:** the Borel functional calculus `f ↦ f(A)` for unbounded self-adjoint
    `A` (bounded Borel `f` give bounded operators). Opaque: Mathlib's `cfc` API is
    continuous-only by design. -/
axiom borelFC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : UnboundedOp H → (ℝ → ℂ) → (H →L[ℂ] H)

/-- **T2 marker:** the Cayley transform `C(A) = (A - iI)(A + iI)⁻¹` of an unbounded
    symmetric operator (a unitary). Opaque: no operator Cayley transform in Mathlib. -/
axiom UnboundedOp.cayley {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : UnboundedOp H → (H ≃ₗᵢ[ℂ] H)

/-- **Unbounded adjoint, exact statement (T5 window):** the adjoint marker has the
    correct domain — `y ∈ dom(A*)` iff the adjoint relation `⟪Ax, y⟫ = ⟪x, z⟫` holds
    for some `z` (unique, since `dom A` is dense by `UnboundedOp.denseDom`).

    PRICE: needs the unbounded-adjoint API — the graph definition of `A*`, density of
    `dom(A*)`, the domain characterization. None of this exists in Mathlib.
    CHECK (2026-10-11): `grep -rn "adjoint" Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`
    → no hits (partial linear maps carry no adjoint);
    `grep -rli "unbounded" Mathlib/Analysis/` → no unbounded-operator API. -/
def UnboundedAdjoint_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedOp H) (y : H),
    y ∈ (A.adjoint).dom ↔
      ∃ z : H, ∀ x : A.dom, ⟪A.op x, y⟫_ℂ = ⟪(x : H), z⟫_ℂ

/-- **von Neumann's adjoint theorem (T5 window):** the adjoint of a densely-defined
    operator is closed; a closed densely-defined operator satisfies `A** = A`.

    PRICE: needs closed unbounded operators (graph-closed) and the adjoint API.
    This is Reed–Simon Vol. I, Theorem VII.2.
    CHECK (2026-10-11): `grep -rn "IsClosed" Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`
    → no closed-operator API; no `IsClosed` graph predicate for operators anywhere. -/
def VonNeumannAdjoint_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedOp H),
    (A.adjoint).isClosed ∧ (A.isClosed → (A.adjoint).adjoint = A)

/-- **Cayley transform correspondence (T5 window):** `A ↦ (A-i)(A+i)⁻¹` maps
    self-adjoint unbounded operators onto unitaries `U` with `1 ∉ σ_p(U)`
    (1 not an eigenvalue). This is the standard bridge (Reed–Simon VII.2) carrying the
    *bounded* spectral theorem for unitaries to the unbounded self-adjoint case — the
    exact missing link between the §1-style bounded calculus and `StoneUnbounded_sharp`.

    PRICE: needs the unbounded adjoint (to say "self-adjoint"), the resolvent
    `(A + iI)⁻¹` as a bounded everywhere-defined operator, and the proof that the
    Cayley transform is unitary with the stated range.
    CHECK (2026-10-11): `grep -ri "cayley" Mathlib/` → only combinatorics/graph-theory
    and polynomial hits; no operator Cayley transform. -/
def CayleyTransform_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ A : UnboundedOp H, A.isSelfAdjoint →
      ¬ Module.End.HasEigenvalue (A.cayley : H →ₗ[ℂ] H) 1)
    ∧ (∀ U : H ≃ₗᵢ[ℂ] H, ¬ Module.End.HasEigenvalue (U : H →ₗ[ℂ] H) 1 →
      ∃ A : UnboundedOp H, A.isSelfAdjoint ∧ A.cayley = U)

/-- **Spectral theorem for unbounded self-adjoint operators (T5 window):** every
    self-adjoint unbounded `A` admits a projection-valued measure `P` on `ℝ` with
    `A = ∫ λ dP(λ)`.

    PRICE: needs PVMs (absent — see CHECK), the unbounded adjoint (to say
    "self-adjoint"), and the construction via the Cayley transform or the resolvent.
    This is Reed–Simon Vol. I, Theorem VII.2.
    CHECK (2026-10-11): `grep -rli "projection.valued\|spectral.measure\|spectralmeasure"
    Mathlib/` → no hits; `ls Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/`
    → continuous-only, no Borel calculus. -/
def SpectralTheoremUnbounded_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedOp H),
    A.isSelfAdjoint → ∃ P : ProjValuedMeasure H 1, isSpectralMeasureOf P A

/-- **Borel functional calculus for unbounded self-adjoint operators (T5 window):**
    for self-adjoint unbounded `A`, `f ↦ f(A)` is a *-homomorphism from bounded Borel
    functions into the bounded operators.

    PRICE: needs PVMs + the unbounded spectral theorem to *construct* `f(A)`. The
    bounded-below shadow (§1: `jointFC_mul`, `jointFC_star`) is T1.
    CHECK (2026-10-11): `grep -rli "borel.*functional.calculus\|functional.calculus.*borel"
    Mathlib/` → no hits; the `cfc`/`cfcₙ` API is continuous-only by design. -/
def BorelCalculusUnbounded_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedOp H),
    A.isSelfAdjoint →
      (∀ f g : ℝ → ℂ, Measurable f → Measurable g →
        Bornology.IsBounded (Set.range f) → Bornology.IsBounded (Set.range g) →
        borelFC A (f * g) = (borelFC A f).comp (borelFC A g))
      ∧ (∀ f : ℝ → ℂ, Measurable f → Bornology.IsBounded (Set.range f) →
        borelFC A (star ∘ f) = (borelFC A f).adjoint)

-- ============================================================================
-- §3. Axiom audit
-- ============================================================================

#print axioms ThetLogos.jointProj_sum_id
#print axioms ThetLogos.jointFC_apply_of_mem
#print axioms ThetLogos.jointFC_coordinate
#print axioms ThetLogos.jointFC_one
#print axioms ThetLogos.jointFC_mul
#print axioms ThetLogos.jointFC_star
#print axioms ThetLogos.jointFC_spectralMapping
