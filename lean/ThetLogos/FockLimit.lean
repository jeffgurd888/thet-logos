import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# ThetLogos.FockLimit — the embedding machine for the infinite-mode limit
(Pitch 2, Campaign A; shared infrastructure for `FermionicLimit` and
`BosonicLimit`)

This module contains NO physics objects. It is the reusable Hilbert-space
machinery that Pitch 2's Task 2 needs and that Mathlib (v4.35.0-rc3) does
not provide: there is no `lp`-reindexing / orthonormal-family embedding
constructor upstream, so the Fock embeddings are assembled here from
`HilbertBasis` representation theory.

## Contents (all T1)

- `lp_single_span_topologicalClosure`: in a constant-`ℂ` `lp` space, the
  span of the standard basis vectors `lp.single 2 i 1` is dense. This is
  the density input for every finite-particle domain in the campaign
  (proved once, from `lp.hasSum_single`).
- `onbEmb`: given a Hilbert basis `b` of a source space `E` and an
  orthonormal family `w` in a target space `F` (same index type), the
  linear isometry `E →ₗᵢ[ℂ] F` sending `b i ↦ w i`, built by transporting
  `b.repr` through the Hilbert basis that `w` induces on the closure of
  its own span.
- `onbEmb_apply`: the basis action.
- `onbEmb_mem`: the filtered span-mapping lemma (domain compatibility and
  sector preservation in the statistics modules are instances).

## Honesty ledger

- Tier: T1 (machine-checked, zero sorries, no new axioms).
- This module builds abstract Hilbert-space infrastructure ONLY.
  It contains no Fock spaces, no Γ-identification, no `dΓ` in any limit,
  and no spectral-gap statement. It is not interaction, not continuum,
  and not the Yang–Mills mass gap.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-- **Density of finite-support vectors in a constant-`ℂ` `lp` space (T1).**
The span of the standard basis vectors `lp.single 2 i 1` is dense in
`lp (fun _ : ι => ℂ) 2`, for an arbitrary index type `ι`. Proved from
`lp.hasSum_single`: every vector is the sum of its own singletons. -/
theorem lp_single_span_topologicalClosure (ι : Type*) [DecidableEq ι] :
    (Submodule.span ℂ (Set.range fun i : ι => lp.single 2 i (1 : ℂ))).topologicalClosure
      = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    (Filter.Eventually.of_forall ?_)
  intro s
  refine sum_mem fun i _ => ?_
  have h : (lp.single 2 i ((x : ι → ℂ) i) : lp (fun _ : ι => ℂ) 2)
      = ((x : ι → ℂ) i) • lp.single 2 i (1 : ℂ) := by
    rw [← lp.single_smul (E := fun _ : ι => ℂ) 2 i ((x : ι → ℂ) i) (1 : ℂ)]
    simp
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

section OnbEmb

variable {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The closure of the span of an orthonormal family's range: the
receiving subspace of the target in the `onbEmb` construction. -/
noncomputable abbrev onbClosure (w : ι → F) : Submodule ℂ F :=
  (Submodule.span ℂ (Set.range w)).topologicalClosure

/-- The family `w`, viewed as a family in the closure of its own span. -/
noncomputable def onbFamilyInClosure (w : ι → F) (i : ι) : onbClosure w :=
  ⟨w i, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)⟩

/-- The family in its own span-closure is still orthonormal (the inner
product on a submodule is the ambient one). -/
theorem onbFamilyInClosure_orthonormal (w : ι → F) (hw : Orthonormal ℂ w) :
    Orthonormal ℂ (onbFamilyInClosure w) := by
  classical
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  exact hw i j

/-- The span of the family in its own span-closure has trivial orthogonal
complement: an element of the closure orthogonal to every `w i` is
orthogonal to the whole closed span, hence to itself. -/
theorem onbFamilyInClosure_orthogonal_eq_bot [CompleteSpace F] (w : ι → F) :
    (Submodule.span ℂ (Set.range (onbFamilyInClosure w)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  -- Step 1: `(x : F)` is orthogonal to every `w i`.
  have step1 : ∀ i, ⟪w i, (x : F)⟫_ℂ = 0 := by
    intro i
    have hi : onbFamilyInClosure w i
        ∈ Submodule.span ℂ (Set.range (onbFamilyInClosure w)) :=
      Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_orthogonal _ _).mp hx _ hi
  -- Step 2: hence `(x : F)` is orthogonal to the whole span of `range w`.
  have step2 : (x : F) ∈ (Submodule.span ℂ (Set.range w))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction
      (p := fun u _ => ⟪u, (x : F)⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro v ⟨i, rfl⟩
      exact step1 i
    · simp
    · intro a b _ _ ha hb
      rw [inner_add_left, ha, hb, add_zero]
    · intro a v _ hv
      rw [inner_smul_left, hv, mul_zero]
  -- Step 3: `(x : F)` also lies in the closed span, i.e. in the double
  -- orthogonal complement of the span; pairing it with itself kills it.
  have step3 : (x : F) ∈ (Submodule.span ℂ (Set.range w))ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact x.2
  have hx0 : (x : F) = 0 := by
    have h := (Submodule.mem_orthogonal _ _).mp step3 _ step2
    exact inner_self_eq_zero.mp h
  exact Subtype.ext (by simp [hx0])

/-- The Hilbert basis that an orthonormal family induces on the closure
of its own span. -/
noncomputable def onbBasisInClosure [CompleteSpace F] (w : ι → F) (hw : Orthonormal ℂ w) :
    HilbertBasis ι ℂ (onbClosure w) :=
  HilbertBasis.mkOfOrthogonalEqBot (onbFamilyInClosure_orthonormal w hw)
    (onbFamilyInClosure_orthogonal_eq_bot w)

/-- The Hilbert basis on the span-closure is the family `w` itself. -/
theorem onbBasisInClosure_coe [CompleteSpace F] (w : ι → F) (hw : Orthonormal ℂ w) :
    ⇑(onbBasisInClosure w hw) = onbFamilyInClosure w :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The embedding machine (T1).** Given a Hilbert basis `b` of the
source `E` and an orthonormal family `w` in the target `F` over the same
index type, the linear isometry `E →ₗᵢ[ℂ] F` characterized (by
`onbEmb_apply`) by `b i ↦ w i`. Assembled from `HilbertBasis.repr` on
both sides: source coordinates, then the target family viewed as a
Hilbert basis of its own span-closure, then inclusion. -/
noncomputable def onbEmb [CompleteSpace F] (b : HilbertBasis ι ℂ E) (w : ι → F)
    (hw : Orthonormal ℂ w) :
    E →ₗᵢ[ℂ] F :=
  (onbClosure w).subtypeₗᵢ.comp
    ((onbBasisInClosure w hw).repr.symm.toLinearIsometry.comp b.repr.toLinearIsometry)

/-- **Basis action of the embedding machine (T1):** `onbEmb` sends the
`i`-th source basis vector to the `i`-th target family vector. -/
theorem onbEmb_apply [CompleteSpace F] (b : HilbertBasis ι ℂ E) (w : ι → F)
    (hw : Orthonormal ℂ w)
    (i : ι) : onbEmb b w hw (b i) = w i := by
  classical
  have h1 : b.repr.toLinearIsometry (b i) = lp.single 2 i (1 : ℂ) :=
    HilbertBasis.repr_self b i
  have h2 : (onbBasisInClosure w hw).repr.symm.toLinearIsometry (lp.single 2 i (1 : ℂ))
      = onbFamilyInClosure w i := by
    rw [show (onbBasisInClosure w hw).repr.symm.toLinearIsometry (lp.single 2 i (1 : ℂ))
        = (onbBasisInClosure w hw).repr.symm (lp.single 2 i (1 : ℂ)) from rfl,
      HilbertBasis.repr_symm_single, onbBasisInClosure_coe]
  show (onbClosure w).subtypeₗᵢ
      ((onbBasisInClosure w hw).repr.symm.toLinearIsometry
        (b.repr.toLinearIsometry (b i))) = w i
  rw [h1, h2]
  rfl

/-- **Filtered span mapping (T1).** If each target vector `w i` with
`i ∈ s` lies in a submodule `t` of the target, then `onbEmb` maps the
span of the source basis vectors indexed by `s` into `t`. Domain
compatibility and sector preservation are instances of this lemma. -/
theorem onbEmb_mem [CompleteSpace F] (b : HilbertBasis ι ℂ E) (w : ι → F)
    (hw : Orthonormal ℂ w)
    {s : Set ι} {t : Submodule ℂ F} (ht : ∀ i ∈ s, w i ∈ t)
    {x : E} (hx : x ∈ Submodule.span ℂ (b '' s)) : onbEmb b w hw x ∈ t := by
  have hle : Submodule.span ℂ (b '' s)
      ≤ Submodule.comap (onbEmb b w hw).toLinearMap t := by
    rw [Submodule.span_le]
    rintro y ⟨i, hi, rfl⟩
    show (onbEmb b w hw) (b i) ∈ t
    rw [onbEmb_apply]
    exact ht i hi
  exact hle hx

end OnbEmb

end ThetLogos
