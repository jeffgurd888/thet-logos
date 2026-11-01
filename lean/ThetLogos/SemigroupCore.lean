/-
# SHELF-1a - the C0-semigroup core (working label)

Brick SHELF-1a of the SHELF line (scoping map
`routeb-general-scratch/scoping-shelf-map-2026-10-30.md`):
strongly continuous semigroups on Banach spaces, the
generator, resolvent basics, and general Yosida
approximants. NO CLAIM beyond the theorems below.

## Strike-check (done first, 2026-10-31)

The pin (Mathlib v4.35.0-rc3) owns NO C0-semigroup theory:
no strongly-continuous-semigroup definition, no unbounded
generator, no Yosida approximants (grep for `Yosida` and for
semigroup/generator API over Banach spaces in
`Mathlib/Analysis` returns nothing). Fragments consumed:
* `spectrum.resolvent` / `resolventSet`
  (`Mathlib/Algebra/Algebra/Spectrum/Basic.lean`,
  `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`) - the
  resolvent of a *bounded* Banach-algebra element; the
  unbounded-generator resolvent below is built here.
* `NormedSpace.exp` (`Mathlib/Analysis/Normed/Algebra/
  Exponential.lean`) with `NormedSpace.exp_add_of_commute`
  and the derivative API `hasDerivAt_exp_smul_const`
  (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`) -
  the bounded-generator exponential, consumed in \S 3.
* `banach_steinhaus`
  (`Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`)
  for the local operator-norm bound in \S 1.

## Fences

This module retires the general-API half of the VISC fence
and of the S2-4(b) fence: the definitions and headlines are
at general Banach-space generality (no finite-dimensional
or single-seat hypothesis anywhere). It does NOT touch:
SHELF-1b generation theorems (Lumer-Phillips / Hille-Yosida
as generation results), SHELF-2's Friedrichs theorem, or any
seat claim. The seat module `LatticeSliceYosida` is not
edited.

## Design choices (on the face)

* Packaging: a `structure` (`C0Semigroup`) over a family
  `toFun : Real -> (E ->L[R] E)`. The family is defined for
  all real `t`; the axioms (identity, semigroup law) are
  imposed only for `t >= 0`, and strong continuity is
  `ContinuousOn` on `Set.Ici 0`. This keeps the real
  one-sided differential calculus (`HasDerivWithinAt` on
  `Set.Ici t`, slopes) directly available.
* Scalar field: specialized to `R`. Time is real, the
  generator is a real one-sided derivative, and the
  resolvent parameter / Yosida weights are real; the
  complex case is not claimed.
* The generator is the linear map on its domain submodule
  `genDom` defined by the strong right derivative at `0`.

## Named remainders (never silently dropped)

* Closedness and density of the generator: NOT proved here
  (pre-named PARTIAL seam of the pack).
* The resolvent integral formula
  `R(lam) x = int_0^infty e^{-lam t} T t x dt`: the
  resolvent is defined algebraically (\S 4); the integral
  formula is a named remainder.
* `exp(t A_n) x -> T t x` for the Yosida approximants:
  named remainder (it routes through Trotter-Kato /
  density). What IS proved: `A_n x -> A x` on the domain
  under the stated resolvent hypotheses (\S 5).
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ThetLogos

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-! ## 1. The C0-semigroup object -/

/-- A strongly continuous (C0) semigroup on a Banach space
`E` over `R`: a family of bounded operators `toFun t` for
`t >= 0` with `toFun 0 = 1`, the semigroup law, and strong
continuity of every orbit on `Set.Ici 0`. The family is
defined for all real `t`; no axiom constrains `t < 0`. -/
structure C0Semigroup (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  toFun : ℝ → (E →L[ℝ] E)
  map_zero : toFun 0 = 1
  map_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    toFun (s + t) = (toFun s).comp (toFun t)
  strongly_continuous : ∀ x : E,
    ContinuousOn (fun t => toFun t x) (Set.Ici 0)

namespace C0Semigroup

variable (S : C0Semigroup E)

@[simp]
theorem map_zero_apply (x : E) : S.toFun 0 x = x := by
  rw [S.map_zero]; rfl

theorem map_add_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : E) : S.toFun (s + t) x = S.toFun s (S.toFun t x) := by
  rw [S.map_add s t hs ht]; rfl

/-- Strong continuity at every nonnegative time, within
`Set.Ici t`. -/
theorem continuousWithinAt (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => S.toFun s x) (Set.Ici t) t :=
  (S.strongly_continuous x).mono (fun z hz => le_trans ht hz)
    t (Set.mem_Ici.mpr le_rfl)

/-- Local operator-norm bound on `[0, 1]`, from strong
continuity and Banach-Steinhaus. -/
theorem exists_opNorm_le_Icc (S : C0Semigroup E) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖S.toFun t‖ ≤ M := by
  have hbdd : ∀ x : E, BddAbove
      (Set.range fun t : Set.Icc (0 : ℝ) 1 => ‖S.toFun t x‖) := by
    intro x
    have hcont : ContinuousOn (fun t => ‖S.toFun t x‖)
        (Set.Icc (0 : ℝ) 1) :=
      (S.strongly_continuous x).norm.mono Set.Icc_subset_Ici_self
    have h := isCompact_Icc.bddAbove_image hcont
    rwa [Set.image_eq_range] at h
  have hbdd' : ∀ x : E, ∃ C, ∀ t : Set.Icc (0 : ℝ) 1,
      ‖S.toFun t x‖ ≤ C := fun x =>
    let ⟨C, hC⟩ := hbdd x
    ⟨C, fun t => hC (Set.mem_range_self t)⟩
  obtain ⟨M, hM⟩ := banach_steinhaus hbdd'
  exact ⟨M, fun t ht => hM ⟨t, ht⟩⟩


/-! ## 2. The generator -/

/-- `y` is the generator value of `S` at `x`: the strong
right derivative of the orbit at `0`. -/
def HasGen (x y : E) : Prop :=
  Filter.Tendsto (fun h : ℝ => h⁻¹ • (S.toFun h x - x))
    (𝓝[>] 0) (𝓝 y)

theorem hasGen_zero : S.HasGen 0 0 := by
  simpa [HasGen] using
    (tendsto_const_nhds (a := (0 : E)) (l := 𝓝[>] (0 : ℝ)))

theorem hasGen_add {x₁ x₂ y₁ y₂ : E} (h₁ : S.HasGen x₁ y₁)
    (h₂ : S.HasGen x₂ y₂) : S.HasGen (x₁ + x₂) (y₁ + y₂) := by
  have heq : (fun h : ℝ => h⁻¹ • (S.toFun h (x₁ + x₂) - (x₁ + x₂)))
      = fun h => h⁻¹ • (S.toFun h x₁ - x₁)
        + h⁻¹ • (S.toFun h x₂ - x₂) := by
    funext h
    rw [_root_.map_add, add_sub_add_comm, smul_add]
  rw [HasGen, heq]
  exact h₁.add h₂

theorem hasGen_smul {x y : E} (c : ℝ) (h : S.HasGen x y) :
    S.HasGen (c • x) (c • y) := by
  have heq : (fun hh : ℝ => hh⁻¹ • (S.toFun hh (c • x) - c • x))
      = fun hh => c • (hh⁻¹ • (S.toFun hh x - x)) := by
    funext hh
    rw [map_smul, ← smul_sub]
    exact smul_comm hh⁻¹ c _
  rw [HasGen, heq]
  exact tendsto_const_nhds.smul h

theorem hasGen_unique {x y₁ y₂ : E} (h₁ : S.HasGen x y₁)
    (h₂ : S.HasGen x y₂) : y₁ = y₂ :=
  tendsto_nhds_unique h₁ h₂

/-- The domain of the generator, as a submodule. -/
def genDom : Submodule ℝ E where
  carrier := {x | ∃ y, S.HasGen x y}
  add_mem' := fun ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ =>
    ⟨y₁ + y₂, S.hasGen_add h₁ h₂⟩
  zero_mem' := ⟨0, S.hasGen_zero⟩
  smul_mem' := fun c _ ⟨y, h⟩ => ⟨c • y, S.hasGen_smul c h⟩

theorem mem_genDom {x : E} : x ∈ S.genDom ↔ ∃ y, S.HasGen x y :=
  Iff.rfl

/-- The generator value at a domain point. -/
noncomputable def genVal {x : E} (hx : x ∈ S.genDom) : E :=
  Classical.choose hx

theorem hasGen_genVal {x : E} (hx : x ∈ S.genDom) :
    S.HasGen x (S.genVal hx) :=
  Classical.choose_spec hx

/-- The generator of `S`, as a linear map on its domain. -/
noncomputable def generator : S.genDom →ₗ[ℝ] E where
  toFun := fun x => S.genVal x.prop
  map_add' := by
    intro x₁ x₂
    apply S.hasGen_unique
      (y₁ := S.genVal (x₁ + x₂).prop)
    · exact S.hasGen_genVal _
    · exact S.hasGen_add (S.hasGen_genVal _) (S.hasGen_genVal _)
  map_smul' := by
    intro c x
    apply S.hasGen_unique
      (y₁ := S.genVal (c • x).prop)
    · exact S.hasGen_genVal _
    · exact S.hasGen_smul c (S.hasGen_genVal _)

/-- The generator, applied to a domain element coerced to
`E`. -/
theorem generator_apply {x : E} (hx : x ∈ S.genDom) :
    S.generator ⟨x, hx⟩ = S.genVal hx :=
  rfl

/-- The semigroup commutes with its generator on the
domain, and the domain is invariant: for `t >= 0`,
`T t x` is in the domain and `A (T t x) = T t (A x)`. -/
theorem hasGen_apply {x y : E} (hx : S.HasGen x y) {t : ℝ}
    (ht : 0 ≤ t) : S.HasGen (S.toFun t x) (S.toFun t y) := by
  have hev : ∀ᶠ h : ℝ in 𝓝[>] 0,
      h⁻¹ • (S.toFun h (S.toFun t x) - S.toFun t x)
        = S.toFun t (h⁻¹ • (S.toFun h x - x)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 ≤ h := le_of_lt hh
    rw [← S.map_add_apply hh0 ht, add_comm h t,
      S.map_add_apply ht hh0, ← map_sub, map_smul]
  exact (tendsto_congr' hev).mpr
    (((S.toFun t).continuous.tendsto y).comp hx)

theorem mem_genDom_apply {x : E} (hx : x ∈ S.genDom) {t : ℝ}
    (ht : 0 ≤ t) : S.toFun t x ∈ S.genDom :=
  ⟨S.toFun t (S.genVal hx),
    S.hasGen_apply (S.hasGen_genVal hx) ht⟩

theorem genVal_apply {x : E} (hx : x ∈ S.genDom) {t : ℝ}
    (ht : 0 ≤ t) :
    S.genVal (S.mem_genDom_apply hx ht)
      = S.toFun t (S.genVal hx) :=
  S.hasGen_unique (S.hasGen_genVal _)
    (S.hasGen_apply (S.hasGen_genVal hx) ht)

/-- At `0`, the generator is the right derivative within
`Set.Ici 0`. -/
theorem hasDerivWithinAt_zero {x y : E} (h : S.HasGen x y) :
    HasDerivWithinAt (fun s => S.toFun s x) y (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext z
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
      Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2),
      fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩
  rw [hset]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp [slope, S.map_zero_apply]

/-- The core differential identity: for `x` in the domain
and `t >= 0`, the orbit differentiates (from the right,
within `Set.Ici t`) to `T t (A x)`. -/
theorem hasDerivWithinAt_apply {x : E} (hx : x ∈ S.genDom)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => S.toFun s x)
      (S.toFun t (S.genVal hx)) (Set.Ici t) t := by
  have hgen : S.HasGen (S.toFun t x)
      (S.toFun t (S.genVal hx)) :=
    S.hasGen_apply (S.hasGen_genVal hx) ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsub : Tendsto (fun s : ℝ => s - t)
      (𝓝[Set.Ici t \ {t}] t) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
        have hc : ContinuousAt (fun s : ℝ => s - t) t :=
          continuousAt_id.sub continuousAt_const
        simpa using hc.tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · apply eventually_nhdsWithin_of_forall
      intro s hs
      simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
        Set.mem_Ioi] at hs ⊢
      exact sub_pos.mpr (lt_of_le_of_ne hs.1 (Ne.symm hs.2))
  have hcomp : Tendsto
      (fun s => (s - t)⁻¹ • (S.toFun (s - t) (S.toFun t x)
        - S.toFun t x))
      (𝓝[Set.Ici t \ {t}] t) (𝓝 (S.toFun t (S.genVal hx))) :=
    hgen.comp hsub
  apply (tendsto_congr' _).mpr hcomp
  apply eventually_nhdsWithin_of_forall
  intro s hs
  simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff] at hs
  have hs0 : 0 ≤ s - t := sub_nonneg.mpr hs.1
  have e : S.toFun s x = S.toFun t (S.toFun (s - t) x) := by
    have h2 : t + (s - t) = s := by linarith [hs.1]
    conv_lhs => rw [← h2]
    exact S.map_add_apply ht hs0 x
  show slope (fun s => S.toFun s x) t s
    = (s - t)⁻¹ • (S.toFun (s - t) (S.toFun t x) - S.toFun t x)
  rw [slope]
  simp only [vsub_eq_sub]
  rw [e, ← S.map_add_apply ht hs0, ← S.map_add_apply hs0 ht,
    add_comm t (s - t)]

end C0Semigroup

/-! ## 3. The anchor: a bounded generator

A bounded operator `A` generates `exp(tA)`, and its
generator is exactly `A`. -/

section BoundedGenerator

variable (A : E →L[ℝ] E)

/-- The uniformly continuous semigroup generated by a
bounded operator `A`: `t |-> NormedSpace.exp (t • A)` in
the Banach algebra `E ->L[R] E`. -/
noncomputable def expSemigroup (A : E →L[ℝ] E) : C0Semigroup E where
  toFun := fun t => NormedSpace.exp (t • A)
  map_zero := by simp [NormedSpace.exp_zero]
  map_add := by
    intro s t _ _
    letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    rw [add_smul, NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left s).smul_right t)]
    rfl
  strongly_continuous := by
    intro x
    apply Continuous.continuousOn
    have hexp : Continuous (fun t : ℝ =>
        NormedSpace.exp (t • A)) := by
      letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
        NormedAlgebra.restrictScalars ℚ ℝ _
      exact NormedSpace.exp_continuous.comp
        (continuous_id.smul continuous_const)
    exact ((ContinuousLinearMap.apply ℝ E) x).continuous.comp
      hexp

theorem expSemigroup_toFun (t : ℝ) :
    (expSemigroup A).toFun t = NormedSpace.exp (t • A) :=
  rfl

/-- Every vector is in the domain of the generator of
`expSemigroup A`, with generator value `A x`. -/
theorem expSemigroup_hasGen (x : E) :
    (expSemigroup A).HasGen x (A x) := by
  have hderiv : HasDerivAt (fun u : ℝ =>
      NormedSpace.exp (u • A)) A 0 := by
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    simpa using h
  have hcomp := ((ContinuousLinearMap.apply ℝ E) x).hasFDerivAt.comp
    0 hderiv.hasFDerivAt
  have hval : (((ContinuousLinearMap.apply ℝ E) x).comp
      (ContinuousLinearMap.toSpanSingleton ℝ A))
      = ContinuousLinearMap.toSpanSingleton ℝ (A x) := by
    ext h
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hval] at hcomp
  have hAt := hcomp.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hAt
  have hAt2 : Tendsto
      (slope (fun u : ℝ => NormedSpace.exp (u • A) x) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (A x)) := by
    have hm := hAt.mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Set.Ioi (0 : ℝ))
        (t := ({0} : Set ℝ)ᶜ) (fun y hy => ne_of_gt hy))
    have hm2 : Tendsto
        (slope (⇑((ContinuousLinearMap.apply ℝ E) x)
          ∘ fun u => NormedSpace.exp (u • A)) 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (A x)) := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using hm
    have hfun : (⇑((ContinuousLinearMap.apply ℝ E) x)
        ∘ fun u : ℝ => NormedSpace.exp (u • A))
        = (fun u : ℝ => NormedSpace.exp (u • A) x) := by
      funext u
      simp only [Function.comp_apply,
        ContinuousLinearMap.apply_apply]
    rw [hfun] at hm2
    exact hm2
  apply hAt2.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp [slope, expSemigroup_toFun]

theorem expSemigroup_genDom :
    (expSemigroup A).genDom = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact ⟨A x, expSemigroup_hasGen A x⟩

theorem expSemigroup_generator_apply (x : E)
    (hx : x ∈ (expSemigroup A).genDom) :
    (expSemigroup A).generator ⟨x, hx⟩ = A x :=
  (expSemigroup A).hasGen_unique
    ((expSemigroup A).hasGen_genVal hx)
    (expSemigroup_hasGen A x)

end BoundedGenerator

/-! ## 4. Resolvent basics (algebraic)

The resolvent of the (possibly unbounded) generator at a
real parameter `lam`, specified by its two inverse
relations. The integral formula for `R(lam)` is a named
remainder (see the header); everything in this section is
pure algebra from the specification. -/

section Resolvent

variable (S : C0Semigroup E) (lam : ℝ) (R : E →L[ℝ] E)

/-- `R` is the resolvent of the generator of `S` at `lam`:
`R` inverts `lam - A` on the domain (first relation), and
every `R y` lies in the domain with
`(lam - A) (R y) = y` (second relation). -/
def ResolventSpec : Prop :=
  (∀ x (hx : x ∈ S.genDom), R (lam • x - S.genVal hx) = x) ∧
  (∀ y, ∃ h : R y ∈ S.genDom, lam • R y - S.genVal h = y)

theorem mem_genDom_resolvent (hR : ResolventSpec S lam R)
    (y : E) : R y ∈ S.genDom :=
  (hR.2 y).1

theorem genVal_resolvent (hR : ResolventSpec S lam R)
    (y : E) :
    S.genVal (mem_genDom_resolvent S lam R hR y)
      = lam • R y - y := by
  rw [eq_sub_iff_add_eq]
  have h2 := sub_eq_iff_eq_add.mp (hR.2 y).2
  rw [h2, add_comm]

theorem resolvent_unique {R₁ R₂ : E →L[ℝ] E}
    (h₁ : ResolventSpec S lam R₁) (h₂ : ResolventSpec S lam R₂) :
    R₁ = R₂ := by
  ext y
  have hmem : R₂ y ∈ S.genDom :=
    mem_genDom_resolvent S lam R₂ h₂ y
  have e := h₁.1 (R₂ y) hmem
  have e2 : lam • R₂ y - S.genVal hmem = y := (h₂.2 y).2
  rw [e2] at e
  exact e

/-- The resolvent applied to a generator value:
`R (A x) = lam • R x - x` on the domain. -/
theorem resolvent_apply_gen (hR : ResolventSpec S lam R)
    {x : E} (hx : x ∈ S.genDom) :
    R (S.genVal hx) = lam • R x - x := by
  have e1 := hR.1 x hx
  have h3 : S.genVal hx
      = lam • x - (lam • x - S.genVal hx) := by abel
  rw [h3, map_sub, map_smul, e1]

/-- The resolvent commutes with the semigroup. -/
theorem resolvent_commute (hR : ResolventSpec S lam R)
    {t : ℝ} (ht : 0 ≤ t) (y : E) :
    R (S.toFun t y) = S.toFun t (R y) := by
  have hmem : R y ∈ S.genDom :=
    mem_genDom_resolvent S lam R hR y
  have hmemt : S.toFun t (R y) ∈ S.genDom :=
    S.mem_genDom_apply hmem ht
  have e1 := hR.1 (S.toFun t (R y)) hmemt
  have gv : S.genVal hmemt = S.toFun t (S.genVal hmem) :=
    S.genVal_apply hmem ht
  have gv2 : S.genVal hmem = lam • R y - y :=
    genVal_resolvent S lam R hR y
  have earg : lam • S.toFun t (R y) - S.genVal hmemt
      = S.toFun t y := by
    rw [gv, gv2, ← map_smul, ← map_sub]
    congr 1
    abel
  rw [earg] at e1
  exact e1

/-- The first resolvent identity:
`R(lam) - R(mu) = (mu - lam) • R(lam) ∘L R(mu)`. -/
theorem resolvent_identity {mu : ℝ} {R' : E →L[ℝ] E}
    (hR : ResolventSpec S lam R)
    (hS : ResolventSpec S mu R') :
    R - R' = (mu - lam) • R.comp R' := by
  ext y
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  have hmem : R' y ∈ S.genDom :=
    mem_genDom_resolvent S mu R' hS y
  have e1 := hR.1 (R' y) hmem
  have gv : S.genVal hmem = mu • R' y - y :=
    genVal_resolvent S mu R' hS y
  have earg : lam • R' y - S.genVal hmem
      = y + (lam - mu) • R' y := by
    rw [gv, sub_smul]
    abel
  rw [earg, map_add, map_smul] at e1
  have hRy : R y = R' y - (lam - mu) • R (R' y) :=
    eq_sub_of_add_eq e1
  rw [hRy, show (mu - lam) • R (R' y)
      = -((lam - mu) • R (R' y)) by
    rw [← neg_smul, neg_sub]]
  abel

end Resolvent

/-! ## 5. Yosida approximants (general)

For `lam` in the resolvent specification, the Yosida
approximant `A_lam = lam • (lam • R(lam) - 1)`, a bounded
operator. It equals `lam • A R(lam)`, agrees with
`lam • R(lam) A` on the domain, and generates a uniformly
continuous semigroup by \S 3. -/

section Yosida

variable (S : C0Semigroup E) (lam : ℝ) (R : E →L[ℝ] E)

/-- The Yosida approximant of the generator at `lam`
(the parameter `S` is carried for bookkeeping; the
approximant depends only on `lam` and `R`). -/
def yosidaApprox (S : C0Semigroup E) (lam : ℝ)
    (R : E →L[ℝ] E) : E →L[ℝ] E :=
  lam • (lam • R - 1)

theorem yosidaApprox_apply (y : E) :
    yosidaApprox S lam R y = lam • (lam • R y - y) := by
  simp [yosidaApprox]

/-- `A_lam = lam • A R(lam)`: the approximant is `lam`
times the generator applied after the resolvent. -/
theorem yosidaApprox_eq (hR : ResolventSpec S lam R)
    (y : E) :
    yosidaApprox S lam R y
      = lam • S.genVal (mem_genDom_resolvent S lam R hR y) := by
  rw [yosidaApprox_apply, genVal_resolvent S lam R hR y]

/-- On the domain, `A_lam x = lam • R(lam) (A x)`. -/
theorem yosidaApprox_eq_on_dom (hR : ResolventSpec S lam R)
    {x : E} (hx : x ∈ S.genDom) :
    yosidaApprox S lam R x = lam • R (S.genVal hx) := by
  have e2 : R (S.genVal hx) = lam • R x - x :=
    resolvent_apply_gen S lam R hR hx
  rw [yosidaApprox_apply, e2]

/-- Each Yosida approximant is a bounded operator, hence
generates a uniformly continuous semigroup (\S 3) whose
generator is the approximant itself. -/
theorem yosidaApprox_generates (y : E) :
    (expSemigroup (yosidaApprox S lam R)).HasGen y
      (yosidaApprox S lam R y) :=
  expSemigroup_hasGen _ y

end Yosida

/-! ## 5b. Resolvent families: strong convergence

For a resolvent family defined at every `lam > 0` with the
contraction bound `‖R(lam)‖ <= lam⁻¹`, the convergence
`lam • R(lam) x -> x` holds on the domain by pure algebra
plus the bound; the Yosida convergence `A_lam x -> A x`
then holds on the domain under the stated hypothesis that
`lam • R(lam) z -> z` for all `z` (the all-of-`E` form of
the convergence, which is what density of the domain would
supply - density is a named remainder, see the header).
The convergence `exp(t A_lam) x -> T t x` is likewise a
named remainder. -/

section YosidaFamily

variable (S : C0Semigroup E) (R : ℝ → (E →L[ℝ] E))

theorem resolvent_tendsto_on_dom
    (hR : ∀ lam : ℝ, 0 < lam → ResolventSpec S lam (R lam))
    (hbd : ∀ lam : ℝ, 0 < lam → ‖R lam‖ ≤ lam⁻¹)
    {x : E} (hx : x ∈ S.genDom) :
    Tendsto (fun lam : ℝ => lam • R lam x) atTop (𝓝 x) := by
  have heq : ∀ᶠ lam : ℝ in atTop,
      lam • R lam x - x = R lam (S.genVal hx) := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    have e1 := (hR lam hlam).1 x hx
    have key : R lam (S.genVal hx) = lam • R lam x - x := by
      calc R lam (S.genVal hx)
          = R lam (lam • x - (lam • x - S.genVal hx)) := by
            congr 1
            abel
        _ = R lam (lam • x) - R lam (lam • x - S.genVal hx) :=
            map_sub _ _ _
        _ = lam • R lam x - x := by rw [map_smul, e1]
    exact key.symm
  have hnorm : Tendsto (fun lam : ℝ => R lam (S.genVal hx))
      atTop (𝓝 0) := by
    have htop : Tendsto
        (fun lam : ℝ => lam⁻¹ * ‖S.genVal hx‖) atTop (𝓝 0) := by
      have hinv : Tendsto (fun lam : ℝ => lam⁻¹) atTop
          (𝓝 0) := tendsto_inv_atTop_zero
      simpa using hinv.mul tendsto_const_nhds
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds htop
    · filter_upwards with lam
      exact norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam
        hlam
      calc ‖R lam (S.genVal hx)‖
          ≤ ‖R lam‖ * ‖S.genVal hx‖ :=
            (R lam).le_opNorm _
        _ ≤ lam⁻¹ * ‖S.genVal hx‖ :=
            mul_le_mul_of_nonneg_right (hbd lam hlam)
              (norm_nonneg _)
  have hsub : Tendsto (fun lam : ℝ => lam • R lam x - x)
      atTop (𝓝 0) :=
    (tendsto_congr' heq).mpr hnorm
  have hfin : Tendsto
      (fun lam : ℝ => (lam • R lam x - x) + x) atTop
      (𝓝 (0 + x)) :=
    hsub.add tendsto_const_nhds
  simpa using hfin

/-- Yosida convergence on the domain: `A_lam x -> A x` for
`x` in the domain, under the hypothesis that
`lam • R(lam) z -> z` for every `z` (see the section
header for the status of that hypothesis). -/
theorem yosidaApprox_tendsto
    (hR : ∀ lam : ℝ, 0 < lam → ResolventSpec S lam (R lam))
    (hlim : ∀ z : E, Tendsto (fun lam : ℝ => lam • R lam z)
      atTop (𝓝 z))
    {x : E} (hx : x ∈ S.genDom) :
    Tendsto (fun lam : ℝ => yosidaApprox S lam (R lam) x)
      atTop (𝓝 (S.genVal hx)) := by
  apply (tendsto_congr' _).mpr (hlim (S.genVal hx))
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  exact yosidaApprox_eq_on_dom S lam (R lam) (hR lam hlam) hx

end YosidaFamily
