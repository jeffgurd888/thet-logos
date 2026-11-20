/-
# WP2 character route, Module B, brick B1a — the unitary
# decomposition engine

A unitary representation of the finite group `G` on a
finite-dimensional inner product space (a MonoidHom into
continuous linear maps preserving the inner product)
decomposes into finitely many **minimal invariant
subspaces**, and its character (the trace of the action)
is the sum of the constituents' traces.  This is the
decomposition core of the column expansion (scope §3, B1):
Module B's later bricks apply it to the tensor word
representations of Module A, realize each constituent by a
unitary matrix model, and regroup the tensor series.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap`
is proved at no seat, no β, no `d`; `LayerKernelPos` at
general finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity
object.
-/

import ThetLogos.LayerKernelWordContraction

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section UnitaryDecomp

variable {G : Type*} [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable (T : G →* (E →L[ℂ] E))
variable (hT : ∀ g : G, ∀ v w : E, ⟪T g v, T g w⟫_ℂ = ⟪v, w⟫_ℂ)

/-- A subspace is **invariant** under the unitary action
when every group element maps it into itself. -/
def TInvariant (W : Submodule ℂ E) : Prop :=
  ∀ g : G, ∀ v ∈ W, T g v ∈ W

theorem TInvariant_top : TInvariant T (⊤ : Submodule ℂ E) :=
  fun _ _ _ => Submodule.mem_top

include hT in
/-- The orthogonal complement of an invariant subspace is
invariant: unitarity moves the group element across the
inner product at the cost of an inverse, which stays
inside the original subspace. -/
theorem TInvariant.orthogonal {W : Submodule ℂ E}
    (hW : TInvariant T W) : TInvariant T Wᗮ := by
  intro g v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have h1 : u = T g (T g⁻¹ u) := by
    have h2 : T (g * g⁻¹) u = T g (T g⁻¹ u) := by
      rw [map_mul]
      rfl
    rwa [mul_inv_cancel, map_one, ContinuousLinearMap.one_apply] at h2
  rw [h1, hT]
  exact hv _ (hW g⁻¹ u hu)

/-- The restriction of the action to an invariant subspace,
as a MonoidHom into its continuous linear maps. -/
noncomputable def TInvariant.restrictHom {W : Submodule ℂ E}
    (hW : TInvariant T W) : G →* (↥W →L[ℂ] ↥W) where
  toFun g :=
    ⟨(T g).toLinearMap.restrict (hW g),
      ((T g).continuous.comp continuous_subtype_val).subtype_mk _⟩
  map_one' := by
    ext x
    show (T 1) x.1 = x.1
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    ext x
    show (T (g * h)) x.1 = (T g) ((T h) x.1)
    rw [map_mul]
    rfl

include hT in
/-- The restricted action is still unitary (the inner
product on a submodule is the ambient one). -/
theorem TInvariant.restrictHom_unitary {W : Submodule ℂ E}
    (hW : TInvariant T W) :
    ∀ g : G, ∀ v w : ↥W,
      ⟪(TInvariant.restrictHom T hW) g v,
        (TInvariant.restrictHom T hW) g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  intro g v w
  show ⟪(T g) v.1, (T g) w.1⟫_ℂ = ⟪v.1, w.1⟫_ℂ
  exact hT g v.1 w.1

include hT in
/-- **Trace splitting over an orthogonal invariant pair.**
The trace of the action on `E` is the trace of its
restriction to an invariant subspace plus the trace of
its restriction to the orthogonal complement. -/
theorem trace_add_orthogonal {W : Submodule ℂ E}
    (hW : TInvariant T W) (g : G) :
    LinearMap.trace ℂ E (T g).toLinearMap
      = LinearMap.trace ℂ ↥W ((T g).toLinearMap.restrict (hW g))
        + LinearMap.trace ℂ ↥Wᗮ
            ((T g).toLinearMap.restrict (hW.orthogonal T hT g)) := by
  classical
  set P := W.prodEquivOfIsCompl Wᗮ (Submodule.isCompl_orthogonal W) with hP
  set e := P.symm with he
  have hPapply : ∀ (a : ↥W) (b : ↥Wᗮ), P ⟨a, b⟩ = a.1 + b.1 := by
    intro a b
    simp only [hP, Submodule.coe_prodEquivOfIsCompl']
  have hconj : e.conj (T g).toLinearMap
      = LinearMap.prodMap ((T g).toLinearMap.restrict (hW g))
          ((T g).toLinearMap.restrict (hW.orthogonal T hT g)) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    show e ((T g) (e.symm (x, y))) = _
    have hsymm : e.symm (x, y) = (x.1 + y.1 : E) := by
      have h : e.symm = P := by rw [he, LinearEquiv.symm_symm]
      rw [h]
      exact hPapply x y
    have hpair : e ((T g) x.1 + (T g) y.1)
        = (⟨(T g) x.1, hW g x.1 x.2⟩,
            ⟨(T g) y.1, hW.orthogonal T hT g y.1 y.2⟩) := by
      apply (LinearEquiv.symm_apply_eq P).mpr
      rw [hPapply]
    rw [hsymm, map_add, hpair]
    rfl
  rw [← LinearMap.trace_conj' (T g).toLinearMap e, hconj,
    LinearMap.trace_prodMap']

/-- **Minimal invariant subspaces exist.**  Among the
nonzero invariant subspaces there is one of minimal
finite rank; any invariant subspace of it is `⊥` or
itself. -/
theorem exists_minimal_TInvariant
    (h0 : ∃ W : Submodule ℂ E, TInvariant T W ∧ W ≠ ⊥) :
    ∃ W : Submodule ℂ E, TInvariant T W ∧ W ≠ ⊥
      ∧ ∀ U : Submodule ℂ E, U ≤ W → TInvariant T U
        → U = ⊥ ∨ U = W := by
  classical
  obtain ⟨W₀, hW₀, hW₀ne⟩ := h0
  set S : Set ℕ := {n | ∃ W : Submodule ℂ E,
    TInvariant T W ∧ W ≠ ⊥ ∧ Module.finrank ℂ ↥W = n} with hS
  have hne : S.Nonempty :=
    ⟨Module.finrank ℂ ↥W₀, W₀, hW₀, hW₀ne, rfl⟩
  obtain ⟨W, hW, hWne, hWfin⟩ := Nat.find_spec hne
  refine ⟨W, hW, hWne, fun U hUW hU => ?_⟩
  by_cases h : U = ⊥
  · exact Or.inl h
  · right
    have hfin1 : Module.finrank ℂ ↥W ≤ Module.finrank ℂ ↥U := by
      have h1 : Nat.find hne ≤ Module.finrank ℂ ↥U :=
        Nat.find_min' hne ⟨U, hU, h, rfl⟩
      omega
    have hfin2 : Module.finrank ℂ ↥U ≤ Module.finrank ℂ ↥W := by
      apply LinearMap.finrank_le_finrank_of_injective
        (f := (Submodule.inclusion hUW))
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : E)) hab
    exact Submodule.eq_of_le_of_finrank_eq hUW (le_antisymm hfin2 hfin1)

/-- The decomposition, by induction on a bound for the
finite rank (the induction step applies the statement to
the orthogonal complement of a minimal invariant
subspace, whose rank is strictly smaller). -/
theorem unitary_decomp_aux : ∀ (n : ℕ) (E' : Type*)
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [FiniteDimensional ℂ E'] (T' : G →* (E' →L[ℂ] E')),
    (∀ g : G, ∀ v w : E', ⟪T' g v, T' g w⟫_ℂ = ⟪v, w⟫_ℂ)
    → Module.finrank ℂ E' ≤ n
    → ∃ (m : ℕ) (W : Fin m → Submodule ℂ E')
        (hinv : ∀ i, TInvariant T' (W i)),
        (∀ i, W i ≠ ⊥)
        ∧ (∀ i, ∀ U : Submodule ℂ E', U ≤ W i → TInvariant T' U
            → U = ⊥ ∨ U = W i)
        ∧ ∀ g : G, LinearMap.trace ℂ E' (T' g).toLinearMap
            = ∑ i, LinearMap.trace ℂ ↥(W i)
                ((T' g).toLinearMap.restrict (hinv i g)) := by
  intro n
  induction n with
  | zero =>
    intro E' _ _ _ T' hT' hfin
    have h0 : Module.finrank ℂ E' = 0 := le_antisymm hfin (Nat.zero_le _)
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun g => ?_⟩
    have hsub : Subsingleton E' := Module.finrank_zero_iff.mp h0
    have hf : (T' g).toLinearMap = 0 := Subsingleton.elim _ _
    rw [Fin.sum_univ_zero, hf]
    simp
  | succ n ih =>
    intro E' _ _ _ T' hT' hfin
    by_cases hE : Module.finrank ℂ E' = 0
    · refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun g => ?_⟩
      have hsub : Subsingleton E' := Module.finrank_zero_iff.mp hE
      have hf : (T' g).toLinearMap = 0 := Subsingleton.elim _ _
      rw [Fin.sum_univ_zero, hf]
      simp
    · have htop : (⊤ : Submodule ℂ E') ≠ ⊥ := by
        intro hcon
        apply hE
        have h1 : Module.finrank ℂ ↥(⊤ : Submodule ℂ E')
            = Module.finrank ℂ ↥(⊥ : Submodule ℂ E') := by rw [hcon]
        rw [finrank_top, finrank_bot] at h1
        exact h1
      obtain ⟨W₀, hW₀, hW₀ne, hW₀min⟩ :=
        exists_minimal_TInvariant T' ⟨⊤, TInvariant_top T', htop⟩
      have hfinW : Module.finrank ℂ ↥W₀ᗮ ≤ n := by
        have hsum := Submodule.finrank_add_finrank_orthogonal W₀
        have hpos : 0 < Module.finrank ℂ ↥W₀ := by
          obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hW₀ne
          haveI : Nontrivial ↥W₀ := ⟨⟨v, hv⟩, 0, by
            intro hcon
            apply hv0
            have := congrArg Subtype.val hcon
            simpa using this⟩
          exact Module.finrank_pos
        omega
      obtain ⟨m, W', hinv', hne', hmin', htr'⟩ := ih ↥W₀ᗮ
        (TInvariant.restrictHom T' (hW₀.orthogonal T' hT'))
        (TInvariant.restrictHom_unitary T' hT' (hW₀.orthogonal T' hT'))
        hfinW
      classical
      refine ⟨m + 1, Fin.cons W₀ (fun i => (W' i).map W₀ᗮ.subtype),
        ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · rwa [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          intro g v hv
          rw [Submodule.mem_map] at hv ⊢
          obtain ⟨y, hy, rfl⟩ := hv
          exact ⟨(TInvariant.restrictHom T' (hW₀.orthogonal T' hT')) g y,
            hinv' j g y hy, rfl⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · rwa [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (hne' j)
          refine (Submodule.ne_bot_iff _).mpr ?_
          exact ⟨v.1, Submodule.mem_map.mpr ⟨v, hv, rfl⟩,
            fun h => hv0 (Subtype.ext h)⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · rwa [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          intro U hUle hUinv
          set U' := U.comap W₀ᗮ.subtype with hU'
          have hU'le : U' ≤ W' j := by
            intro x hx
            have hxU : x.1 ∈ U := hx
            have hxmap : x.1 ∈ (W' j).map W₀ᗮ.subtype := hUle hxU
            obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxmap
            have : y = x := Subtype.ext hyx
            rwa [this] at hy
          have hU'inv : TInvariant
              (TInvariant.restrictHom T' (hW₀.orthogonal T' hT')) U' := by
            intro g x hx
            have hxU : x.1 ∈ U := hx
            show (T' g) x.1 ∈ U
            exact hUinv g x.1 hxU
          have hUeq : U = U'.map W₀ᗮ.subtype := by
            have hUW : U ≤ W₀ᗮ := by
              intro z hz
              obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp (hUle hz)
              exact y.2
            rw [hU', Submodule.map_comap_subtype]
            exact (inf_eq_right.mpr hUW).symm
          rcases hmin' j U' hU'le hU'inv with h | h
          · left
            rw [hUeq, h, Submodule.map_bot]
          · right
            rw [hUeq, h]
      · intro g
        simp only [Fin.sum_univ_succ, Fin.cons_zero]
        have hstep := trace_add_orthogonal T' hT' hW₀ g
        rw [hstep]
        congr 1
        have htr'' : LinearMap.trace ℂ ↥W₀ᗮ
              ((T' g).toLinearMap.restrict (hW₀.orthogonal T' hT' g))
            = LinearMap.trace ℂ ↥W₀ᗮ
                ((TInvariant.restrictHom T' (hW₀.orthogonal T' hT')
                  g).toLinearMap) := rfl
        rw [htr'', htr' g]
        apply Finset.sum_congr rfl
        intro j _
        have hmap_inv : ∀ v ∈ (W' j).map W₀ᗮ.subtype,
            (T' g) v ∈ (W' j).map W₀ᗮ.subtype := by
          intro v hv
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
          exact Submodule.mem_map.mpr
            ⟨(TInvariant.restrictHom T' (hW₀.orthogonal T' hT') g) y,
              hinv' j g y hy, rfl⟩
        show LinearMap.trace ℂ ↥(W' j)
              ((TInvariant.restrictHom T' (hW₀.orthogonal T' hT')
                g).toLinearMap.restrict (hinv' j g))
            = LinearMap.trace ℂ ↥((W' j).map W₀ᗮ.subtype)
              ((T' g).toLinearMap.restrict hmap_inv)
        have hconj : (Submodule.equivMapOfInjective W₀ᗮ.subtype
              W₀ᗮ.injective_subtype (W' j)).conj
              ((TInvariant.restrictHom T' (hW₀.orthogonal T' hT')
                g).toLinearMap.restrict (hinv' j g))
            = (T' g).toLinearMap.restrict hmap_inv := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          rw [LinearEquiv.conj_apply, LinearMap.comp_apply,
            LinearMap.comp_apply]
          show ((Submodule.equivMapOfInjective W₀ᗮ.subtype
                W₀ᗮ.injective_subtype (W' j))
              (((TInvariant.restrictHom T' (hW₀.orthogonal T' hT')
                  g).toLinearMap.restrict (hinv' j g))
                ((Submodule.equivMapOfInjective W₀ᗮ.subtype
                  W₀ᗮ.injective_subtype (W' j)).symm x)) : E')
            = (T' g) ↑x
          rw [Submodule.coe_equivMapOfInjective_apply]
          show (T' g) (W₀ᗮ.subtype
              ((Submodule.equivMapOfInjective W₀ᗮ.subtype
                W₀ᗮ.injective_subtype (W' j)).symm x : ↥W₀ᗮ))
            = (T' g) ↑x
          rw [Submodule.map_equivMapOfInjective_symm_apply]
        rw [← hconj, LinearMap.trace_conj']

include hT in
/-- **Unitary decomposition.**  A unitary representation
of the finite group on a finite-dimensional inner product
space decomposes into finitely many minimal invariant
subspaces, and its character is the sum of the
constituents' traces. -/
theorem unitary_decomp :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E)
      (hinv : ∀ i, TInvariant T (W i)),
      (∀ i, W i ≠ ⊥)
      ∧ (∀ i, ∀ U : Submodule ℂ E, U ≤ W i → TInvariant T U
          → U = ⊥ ∨ U = W i)
      ∧ ∀ g : G, LinearMap.trace ℂ E (T g).toLinearMap
          = ∑ i, LinearMap.trace ℂ ↥(W i)
              ((T g).toLinearMap.restrict (hinv i g)) :=
  unitary_decomp_aux (Module.finrank ℂ E) E T hT le_rfl

end UnitaryDecomp

end ThetLogos
