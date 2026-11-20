/-
# WP2 character route, Module B, brick B1b1 — unitary matrix
# models of the minimal constituents

Brick B1b of the scope (§3) is re-cut — content unchanged,
seams disclosed (the lane's A2 → A2a/A2b precedent) — as
B1b1 (this file: the constituent model) and B1b2
(`LayerKernelIrredFamily.lean`: the character orthogonality
and the finite irreducible family τ).  Here: each minimal
constituent `W` of B1a's decomposition (a nonzero invariant
subspace, minimal among invariant subspaces) is realized by
a **unitary matrix model**

  `unitaryModel T hT hW : G →* unitaryGroup (Fin (finrank ℂ ↥W)) ℂ`,

the matrix of the restricted action in a chosen orthonormal
basis of `W` (entries `⟪b i, T g (b j)⟫`).  Its character is
the constituent trace (`charFn_unitaryModel`), and it is
irreducible in the corpus's owned vocabulary
(`unitaryModel_irreducible`, from the minimality of `W`).

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelUnitaryDecomp
import ThetLogos.RepOrthogonality
import Mathlib.Analysis.InnerProductSpace.Trace

open Finset
open scoped Matrix InnerProductSpace

namespace ThetLogos

section UnitaryModel

variable {G : Type*} [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable (T : G →* (E →L[ℂ] E))
variable (hT : ∀ g : G, ∀ v w : E, ⟪T g v, T g w⟫_ℂ = ⟪v, w⟫_ℂ)

/-- A chosen orthonormal basis of the subspace `W`, indexed
by `Fin (finrank ℂ ↥W)` (transported from the finset-indexed
existence theorem along the cardinal equality). -/
noncomputable def constituentBasis (W : Submodule ℂ E) :
    OrthonormalBasis (Fin (Module.finrank ℂ ↥W)) ℂ ↥W :=
  let hex := exists_orthonormalBasis ℂ ↥W
  let s := Classical.choose hex
  let b := Classical.choose (Classical.choose_spec hex)
  b.reindex ((Finset.equivFin s).trans (finCongr (by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_coe])))

/-- The matrix of the restricted action on `W` in the
constituent basis: entries `⟪b i, T g (b j)⟫`. -/
noncomputable def unitaryModelMat {W : Submodule ℂ E}
    (hW : TInvariant T W) (g : G) :
    Matrix (Fin (Module.finrank ℂ ↥W)) (Fin (Module.finrank ℂ ↥W)) ℂ :=
  fun i j => ⟪constituentBasis W i,
    (TInvariant.restrictHom T hW) g (constituentBasis W j)⟫_ℂ

theorem unitaryModelMat_one {W : Submodule ℂ E} (hW : TInvariant T W) :
    unitaryModelMat T hW 1 = 1 := by
  ext i j
  show ⟪constituentBasis W i,
      (TInvariant.restrictHom T hW) 1 (constituentBasis W j)⟫_ℂ
    = (1 : Matrix _ _ ℂ) i j
  rw [map_one, ContinuousLinearMap.one_apply, Matrix.one_apply]
  exact (orthonormal_iff_ite.mp (constituentBasis W).orthonormal) i j

theorem unitaryModelMat_mul {W : Submodule ℂ E} (hW : TInvariant T W)
    (g h : G) : unitaryModelMat T hW (g * h)
      = unitaryModelMat T hW g * unitaryModelMat T hW h := by
  have hexp : ∀ x : ↥W, x
      = ∑ k, ⟪constituentBasis W k, x⟫_ℂ • constituentBasis W k := by
    intro x
    conv_lhs => rw [← (constituentBasis W).sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(constituentBasis W).repr_apply_apply]
  ext i j
  show ⟪constituentBasis W i,
      (TInvariant.restrictHom T hW) (g * h) (constituentBasis W j)⟫_ℂ
    = (unitaryModelMat T hW g * unitaryModelMat T hW h) i j
  rw [Matrix.mul_apply, map_mul, ContinuousLinearMap.mul_apply]
  rw [hexp ((TInvariant.restrictHom T hW) h (constituentBasis W j)),
    map_sum, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]
  rfl

include hT in
/-- The model matrix is unitary: `star A * A = 1` entrywise
is Parseval at the transported pair plus the unitarity of
the restricted action. -/
theorem unitaryModelMat_mem_unitaryGroup {W : Submodule ℂ E}
    (hW : TInvariant T W) (g : G) :
    unitaryModelMat T hW g
      ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ ↥W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  show (star (unitaryModelMat T hW g) * unitaryModelMat T hW g) i j
    = (1 : Matrix _ _ ℂ) i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : ∀ k, star (unitaryModelMat T hW g k i)
        * unitaryModelMat T hW g k j
      = ⟪(TInvariant.restrictHom T hW) g (constituentBasis W i),
          constituentBasis W k⟫_ℂ
        * ⟪constituentBasis W k,
          (TInvariant.restrictHom T hW) g (constituentBasis W j)⟫_ℂ := by
    intro k
    show star ⟪constituentBasis W k,
        (TInvariant.restrictHom T hW) g (constituentBasis W i)⟫_ℂ
        * ⟪constituentBasis W k,
          (TInvariant.restrictHom T hW) g (constituentBasis W j)⟫_ℂ = _
    have h : (starRingEnd ℂ) ⟪constituentBasis W k,
          (TInvariant.restrictHom T hW) g (constituentBasis W i)⟫_ℂ
        = ⟪(TInvariant.restrictHom T hW) g (constituentBasis W i),
          constituentBasis W k⟫_ℂ := inner_conj_symm _ _
    rw [starRingEnd_apply] at h
    rw [h]
  simp only [Matrix.star_apply]
  rw [Finset.sum_congr rfl (fun k _ => hstar k),
    OrthonormalBasis.sum_inner_mul_inner,
    TInvariant.restrictHom_unitary T hT hW g]
  exact (orthonormal_iff_ite.mp (constituentBasis W).orthonormal) i j

/-- **The unitary matrix model of a minimal constituent**:
the restricted action on `W`, read in the constituent basis
as a homomorphism into the unitary group. -/
noncomputable def unitaryModel {W : Submodule ℂ E}
    (hW : TInvariant T W) :
    G →* ↥(Matrix.unitaryGroup (Fin (Module.finrank ℂ ↥W)) ℂ) where
  toFun g := ⟨unitaryModelMat T hW g,
    unitaryModelMat_mem_unitaryGroup T hT hW g⟩
  map_one' := Subtype.ext (unitaryModelMat_one T hW)
  map_mul' := fun g h => Subtype.ext (unitaryModelMat_mul T hW g h)

/-- The model's character is the constituent trace. -/
theorem charFn_unitaryModel {W : Submodule ℂ E} (hW : TInvariant T W) :
    charFn (unitaryModel T hT hW)
      = fun g => LinearMap.trace ℂ ↥W
          ((T g).toLinearMap.restrict (hW g)) := by
  funext g
  show Matrix.trace (unitaryModelMat T hW g) = _
  show (∑ i, unitaryModelMat T hW g i i) = _
  rw [LinearMap.trace_eq_sum_inner
    ((T g).toLinearMap.restrict (hW g)) (constituentBasis W)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

/-- **The model of a minimal constituent is irreducible**
(owned vocabulary): an invariant subspace of the coordinate
space transports along the basis coordinates to an invariant
subspace of `W`, and minimality leaves only `⊥` and `⊤`. -/
theorem unitaryModel_irreducible {W : Submodule ℂ E}
    (hW : TInvariant T W)
    (hWmin : ∀ U : Submodule ℂ E, U ≤ W → TInvariant T U
      → U = ⊥ ∨ U = W) :
    RepIrreducible (unitaryModel T hT hW) := by
  intro W' hW'
  classical
  set b := constituentBasis W with hb
  set φ := b.toBasis.equivFun with hφ
  have hcoord : ∀ (y : ↥W) (j),
      φ y j = ⟪b j, y⟫_ℂ := by
    intro y j
    show b.toBasis.repr y j = ⟪b j, y⟫_ℂ
    rw [← OrthonormalBasis.repr_apply_apply]
    rfl
  have hexp : ∀ x : ↥W, x = ∑ k, ⟪b k, x⟫_ℂ • b k := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [b.repr_apply_apply]
  -- the intertwining identity: coordinates of the restricted
  -- action are the model matrix times coordinates
  have htw : ∀ (g : G) (x : ↥W),
      unitaryModelMat T hW g *ᵥ (φ x)
        = φ ((T g).toLinearMap.restrict (hW g) x) := by
    intro g x
    funext i
    have h1 : (unitaryModelMat T hW g *ᵥ (φ x)) i
        = ∑ j, ⟪b i, (TInvariant.restrictHom T hW) g (b j)⟫_ℂ
            * ⟪b j, x⟫_ℂ := by
      show (∑ j, unitaryModelMat T hW g i j * φ x j) = _
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcoord]
      rfl
    have h2 : φ ((T g).toLinearMap.restrict (hW g) x) i
        = ⟪b i, (TInvariant.restrictHom T hW) g x⟫_ℂ := hcoord _ i
    rw [h1, h2]
    conv_rhs => rw [hexp x]
    rw [map_sum, inner_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, inner_smul_right, mul_comm]
  -- the transported submodule of `↥W`
  set U : Submodule ℂ ↥W := W'.comap φ.toLinearMap with hU
  have hUinv : ∀ (g : G) (x : ↥W), x ∈ U
      → (T g).toLinearMap.restrict (hW g) x ∈ U := by
    intro g x hx
    have hx' : φ x ∈ W' := hx
    have h1 : unitaryModelMat T hW g *ᵥ (φ x) ∈ W' := by
      have := hW' g (φ x) hx'
      exact this
    rw [htw] at h1
    exact h1
  -- its image in `E`, an invariant submodule below `W`
  set UE : Submodule ℂ E := U.map W.subtype with hUE
  have hUEle : UE ≤ W := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := hv
    exact u.2
  have hUEinv : TInvariant T UE := by
    intro g v hv
    obtain ⟨u, hu, rfl⟩ := hv
    have h2 : (T g).toLinearMap.restrict (hW g) u ∈ U := hUinv g u hu
    exact ⟨(T g).toLinearMap.restrict (hW g) u, h2, rfl⟩
  rcases hWmin UE hUEle hUEinv with h | h
  · -- `UE = ⊥` forces `W' = ⊥`
    left
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    have hxU : φ.symm v ∈ U := by
      show φ (φ.symm v) ∈ W'
      rwa [LinearEquiv.apply_symm_apply]
    have hx0 : φ.symm v ≠ 0 := by
      intro h0
      apply hv0
      have h3 : φ (φ.symm v) = 0 := by rw [h0]; simp
      rwa [LinearEquiv.apply_symm_apply] at h3
    have hmem : (φ.symm v).1 ∈ UE := ⟨φ.symm v, hxU, rfl⟩
    rw [h] at hmem
    have h6 : (φ.symm v).1 = 0 := hmem
    exact hx0 (Subtype.ext h6)
  · -- `UE = W` forces `W' = ⊤`
    right
    rw [eq_top_iff]
    intro v _
    have hxU : φ.symm v ∈ U := by
      have hmem : (φ.symm v).1 ∈ UE := by
        rw [h]
        exact (φ.symm v).2
      obtain ⟨u, hu, hu1⟩ := hmem
      have h4 : φ.symm v = u := Subtype.ext hu1.symm
      rwa [h4]
    have h5 : φ (φ.symm v) ∈ W' := hxU
    rwa [LinearEquiv.apply_symm_apply] at h5

end UnitaryModel

end ThetLogos
