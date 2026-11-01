/-
# SHELF-2 - THE FRIEDRICHS REPRESENTATION THEOREM (Kato's first
# representation theorem), general form

Working label: SHELF-2 (shelf map row: "Friedrichs
representation theorem: a closed semibounded form yields a
self-adjoint operator + its square root (Kato)"). This is a
general analysis fill: it moves no dial, closes no posted
question, and asserts NO CLAIM beyond its theorems. The
S2-4(b)/FG-2 fences retire only at the generality actually
landed here (see the fence list at the end of this header).

## Step 0 - strike-check inventory (pin: Mathlib v4.35.0-rc3)

Inventory of what the pin owns, checked by direct search of
the pinned Mathlib tree:

* "Friedrichs": NO occurrence anywhere in the pinned
  Mathlib. There is no closed-form -> operator theorem in
  the pin. This brick is therefore a FILL, not a strike.
* Densely defined / unbounded operators and adjoints: YES,
  a real dialect exists -
  `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`:
  `LinearPMap.adjoint` (notation `T†`), the graph adjoint
  for submodules of `E × F`, `LinearPMap.IsFormalAdjoint`,
  `LinearPMap.adjoint_isFormalAdjoint`,
  `LinearPMap.IsFormalAdjoint.le_adjoint`,
  `LinearPMap.adjoint_apply_eq`, and self-adjointness for
  partial maps: `LinearPMap.isSelfAdjoint_def :
  IsSelfAdjoint A ↔ A† = A`. Bounded-operator adjoints live
  in `.../Adjoint.lean` (`ContinuousLinearMap.adjoint`,
  `IsSelfAdjoint` for `→L`), reserved for everywhere-defined
  operators.
* Closed quadratic / sesquilinear forms on Hilbert space:
  NO form-to-operator theory in the pin. `LaxMilgram.lean`
  is the bounded coercive bilinear theorem on the whole
  space (real scalars) - not a densely defined closed form.
  Sesquilinear forms exist only as raw algebra
  (`LinearAlgebra/SesquilinearForm.lean`, matrices).
* Frechet-Riesz for a form-domain inner product: the engine
  exists - `InnerProductSpace.toDual` (Riesz representation
  for any Hilbert space in the pin). Applied to a form
  Hilbert space, this is exactly the classical Friedrichs
  step; the seat module did the same.
* Positive-operator square roots for BOUNDED operators:
  YES, via the continuous functional calculus on the
  C*-algebra of bounded operators (see §7 below, where the
  exact lemmas used are named at their use sites).
* Self-adjointness criteria for unbounded operators: only
  the `LinearPMap` dialect itself (formal adjoints,
  maximality of the adjoint). No ready-made
  "symmetric + range condition => self-adjoint" lemma was
  found in the pin; the range argument is proved by hand
  in §5 from `IsFormalAdjoint.le_adjoint` plus a direct
  domain inclusion for the adjoint.

## Dialect and generality chosen

* Dialect: Mathlib's `LinearPMap` dialect for the operator
  (the pin's unbounded-operator dialect), NOT the seat's
  bare-linear-map-on-a-submodule dialect. The seat module
  `LatticeSliceFriedrichs` (read-only reference, NOT
  edited) carries its Hamiltonian as a linear map on its
  domain submodule and proves self-adjointness only in the
  resolvent sense, noting the `LinearPMap` formalism as
  unconnected there. For the GENERAL theorem the
  `LinearPMap` graph dialect is available and is used:
  self-adjointness is proved as the graph equality
  `T† = T` (equivalently `IsSelfAdjoint T`). The seat's
  resolvent characterization is ALSO proved here
  (`range (T + c) = ⊤` at the Friedrichs shift), so the two
  dialects' contents agree on this construction.
* Generality: `𝕜` is `RCLike` (real or complex), `H` a
  Hilbert space over `𝕜`. No lattice, sector, or
  finite-dimensional content.

## The form, in closed parametrization

A densely defined closed semibounded form is presented in
the parametrization its own proof produces (and every
classical closed semibounded form arises this way): a
Hilbert space `V` (the form domain with the form inner
product), an injective continuous linear inclusion
`J : V →L[𝕜] H` of dense range and operator norm at most
`1`, and a real lower bound `m`. With the Friedrichs shift
`c = 1 - m`, the form is

  `t(x, y) = ⟪x, y⟫_V - c • ⟪Jx, Jy⟫_H`,

so that `t(x, y) + c • ⟪Jx, Jy⟫_H = ⟪x, y⟫_V`: the form
inner product is exactly the Hilbert inner product of `V`
(closedness = completeness of `V`), and
`t(x, x) ≥ m‖Jx‖²` is exactly `‖Jx‖ ≤ ‖x‖` (§1). The form
domain `D(t)` is the range of `J`, dense in `H` by
hypothesis. The classical data is recovered: `D(t)`,
`t` restricted to it, density, closedness,
semiboundedness - all proved below as theorems about this
parametrization, not assumed.

## What it delivers

* §2-§3: the Riesz resolvent `B : H →L[𝕜] V` and the
  bounded resolvent `R = J ∘L B : H →L[𝕜] H` at the
  Friedrichs shift: bounded by `1`, self-adjoint,
  positive, injective.
* §4: the Friedrichs operator `T` as a `LinearPMap`, its
  domain characterized in the classical shape
  `{x ∈ D(t) : ∃ y, ∀ z ∈ D(t), t(z, x) = ⟪Jz, y⟫}`,
  the representation identity `t(z, x) = ⟪Jz, Tx⟫`,
  and inherited semiboundedness `re ⟪Tx, x⟫ ≥ m‖x‖²`.
* §5: self-adjointness in the `LinearPMap` graph dialect,
  `IsSelfAdjoint T` (i.e. `T† = T`), fully proved; plus
  the resolvent-sense characterization
  `range (T + c) = ⊤`.
* §6-§7 (Kato square root): see the seam statement there.

## Fences

This landing retires the S2-4(b)/FG-2 fence "the general
Friedrichs representation theorem" at exactly the
generality above: RCLike Hilbert spaces, forms in closed
parametrization, graph-dialect self-adjointness. It does
not touch the seat's own residues (the seat's `H' =
(ker T̂_c)⊥` equality, any semigroup identification, or
any continuum/uniformity clause), and it moves no dial.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace ThetLogos

open scoped InnerProduct LinearPMap

section FriedrichsExtension

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]


/-! ## §1. The form and its elementary properties -/

/-- The Friedrichs shift `c = 1 - m`, as an element of `𝕜`. -/
noncomputable def friedrichsShift (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : 𝕜 := ((1 - m : ℝ) : 𝕜)

/-- **The closed semibounded form** `t` on the form domain
(parametrized by `V`): `t(x, y) = ⟪x, y⟫_V - c • ⟪Jx, Jy⟫_H`
with `c = 1 - m`. Sesquilinear (conjugate-linear in the
first argument, linear in the second, matching the pin's
inner-product convention), Hermitian, semibounded below
by `m` - all proved in this section. -/
noncomputable def friedrichsForm (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x y : V) : 𝕜 :=
  inner 𝕜 x y - friedrichsShift J m hJinj hJle hJdense * inner 𝕜 (J x) (J y)

theorem friedrichsForm_add_left (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x₁ x₂ y : V) :
    friedrichsForm J m hJinj hJle hJdense (x₁ + x₂) y
      = friedrichsForm J m hJinj hJle hJdense x₁ y + friedrichsForm J m hJinj hJle hJdense x₂ y := by
  rw [friedrichsForm, friedrichsForm, friedrichsForm,
    inner_add_left, map_add, inner_add_left]
  ring

theorem friedrichsForm_add_right (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x y₁ y₂ : V) :
    friedrichsForm J m hJinj hJle hJdense x (y₁ + y₂)
      = friedrichsForm J m hJinj hJle hJdense x y₁ + friedrichsForm J m hJinj hJle hJdense x y₂ := by
  rw [friedrichsForm, friedrichsForm, friedrichsForm,
    inner_add_right, map_add, inner_add_right]
  ring

theorem friedrichsForm_smul_left (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (a : 𝕜) (x y : V) :
    friedrichsForm J m hJinj hJle hJdense (a • x) y
      = (starRingEnd 𝕜) a * friedrichsForm J m hJinj hJle hJdense x y := by
  rw [friedrichsForm, friedrichsForm, inner_smul_left, map_smul,
    inner_smul_left]
  ring

theorem friedrichsForm_smul_right (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (a : 𝕜) (x y : V) :
    friedrichsForm J m hJinj hJle hJdense x (a • y)
      = a * friedrichsForm J m hJinj hJle hJdense x y := by
  rw [friedrichsForm, friedrichsForm, inner_smul_right, map_smul,
    inner_smul_right]
  ring

/-- **Hermitian symmetry** of the form:
`conj (t(x, y)) = t(y, x)`. -/
theorem friedrichsForm_conj_symm (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x y : V) :
    (starRingEnd 𝕜) (friedrichsForm J m hJinj hJle hJdense x y)
      = friedrichsForm J m hJinj hJle hJdense y x := by
  have hc : (starRingEnd 𝕜) (friedrichsShift J m hJinj hJle hJdense)
      = friedrichsShift J m hJinj hJle hJdense := by
    simp [friedrichsShift]
  rw [friedrichsForm, friedrichsForm,
    map_sub, map_mul, inner_conj_symm y x, inner_conj_symm (J y) (J x), hc]

/-- The form inner product identity: `t` plus the shifted
ambient pairing is the Hilbert inner product of `V`. This
is the closedness clause in this parametrization. -/
theorem friedrichsForm_add_shift (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x y : V) :
    friedrichsForm J m hJinj hJle hJdense x y + friedrichsShift J m hJinj hJle hJdense * inner 𝕜 (J x) (J y)
      = inner 𝕜 x y := by
  rw [friedrichsForm, sub_add_cancel]

/-- The diagonal of the form is real, with the explicit
value `‖x‖² - (1 - m)‖Jx‖²`. -/
theorem friedrichsForm_self_re (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x : V) :
    RCLike.re (friedrichsForm J m hJinj hJle hJdense x x)
      = ‖x‖ ^ 2 - (1 - m) * ‖J x‖ ^ 2 := by
  simp only [friedrichsForm, friedrichsShift, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, ← RCLike.ofReal_sub,
    RCLike.ofReal_re]

/-- **Semiboundedness of the form**: `t(x, x) ≥ m‖Jx‖²` on
the diagonal (real part; the diagonal is real by Hermitian
symmetry). This is exactly the hypothesis `‖Jx‖ ≤ ‖x‖`
read through the shift. -/
theorem friedrichsForm_self_lower (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x : V) :
    m * ‖J x‖ ^ 2 ≤ RCLike.re (friedrichsForm J m hJinj hJle hJdense x x) := by
  rw [friedrichsForm_self_re J m hJinj hJle hJdense x]
  have h := hJle x
  have hsq : ‖J x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    gcongr
  nlinarith [hsq, sq_nonneg ‖J x‖]

/-- The form domain `D(t)`: the range of `J`, a submodule
of `H`, dense by hypothesis. -/
noncomputable def friedrichsFormDomain (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : Submodule 𝕜 H :=
  LinearMap.range J.toLinearMap

theorem friedrichsFormDomain_dense (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    Dense (friedrichsFormDomain J m hJinj hJle hJdense : Set H) := by
  show Dense (Set.range (J : V → H))
  exact hJdense

/-! ## §2. The Riesz resolvent on the form space -/

/-- The pairing functional of `f ∈ H` on the form Hilbert
space: `x ↦ ⟪f, Jx⟫`, continuous since `‖Jx‖ ≤ ‖x‖`. This
is the functional the Friedrichs argument feeds to Riesz. -/
noncomputable def friedrichsFunctional (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) : V →L[𝕜] 𝕜 :=
  (innerSL 𝕜 f).comp J

theorem friedrichsFunctional_apply (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) (x : V) :
    friedrichsFunctional J m hJinj hJle hJdense f x = inner 𝕜 f (J x) :=
  rfl

/-- **The Riesz representative**: the unique `u_f ∈ V` with
`⟪u_f, x⟫_V = ⟪f, Jx⟫_H` for all `x` - Frechet-Riesz
(`InnerProductSpace.toDual`) applied to the form Hilbert
space. At the Friedrichs shift this is the resolvent
equation `(T + c) u_f = f` in weak form. -/
noncomputable def friedrichsRep (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) : V :=
  (InnerProductSpace.toDual 𝕜 V).symm (friedrichsFunctional J m hJinj hJle hJdense f)

theorem friedrichsRep_spec (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) (x : V) :
    inner 𝕜 (friedrichsRep J m hJinj hJle hJdense f) x = inner 𝕜 f (J x) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜)
    (E := V) (x := x) (y := friedrichsFunctional J m hJinj hJle hJdense f)
  exact h

/-- Uniqueness of form-space vectors by their pairings in
the first slot - the definiteness that makes the Riesz
representative well-defined as a function of `f`. -/
theorem friedrichsRep_unique (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) {u₁ u₂ : V}
    (h : ∀ x : V, inner 𝕜 u₁ x = inner 𝕜 u₂ x) : u₁ = u₂ := by
  have hsub : ∀ x : V, inner 𝕜 (u₁ - u₂) x = 0 := fun x => by
    rw [inner_sub_left, h x, sub_self]
  have hself := hsub (u₁ - u₂)
  rw [inner_self_eq_zero] at hself
  exact sub_eq_zero.mp hself

theorem friedrichsRep_add (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f g : H) :
    friedrichsRep J m hJinj hJle hJdense (f + g)
      = friedrichsRep J m hJinj hJle hJdense f + friedrichsRep J m hJinj hJle hJdense g := by
  apply friedrichsRep_unique J m hJinj hJle hJdense
  intro x
  rw [inner_add_left, friedrichsRep_spec J m hJinj hJle hJdense, friedrichsRep_spec J m hJinj hJle hJdense,
    friedrichsRep_spec J m hJinj hJle hJdense, inner_add_left]

theorem friedrichsRep_smul (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (a : 𝕜) (f : H) :
    friedrichsRep J m hJinj hJle hJdense (a • f)
      = a • friedrichsRep J m hJinj hJle hJdense f := by
  apply friedrichsRep_unique J m hJinj hJle hJdense
  intro x
  rw [inner_smul_left, friedrichsRep_spec J m hJinj hJle hJdense, friedrichsRep_spec J m hJinj hJle hJdense,
    inner_smul_left]

/-- The Riesz representative as a linear map `H →ₗ[𝕜] V`. -/
noncomputable def friedrichsRepLin (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →ₗ[𝕜] V where
  toFun := friedrichsRep J m hJinj hJle hJdense
  map_add' := friedrichsRep_add J m hJinj hJle hJdense
  map_smul' := friedrichsRep_smul J m hJinj hJle hJdense

/-- The resolvent bound `‖u_f‖ ≤ ‖f‖`: from
`‖u_f‖² = re ⟪f, Ju_f⟫ ≤ ‖f‖ · ‖u_f‖` (Cauchy-Schwarz plus
`‖J‖ ≤ 1`), divided through. -/
theorem friedrichsRep_norm_le (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    ‖friedrichsRep J m hJinj hJle hJdense f‖ ≤ ‖f‖ := by
  have hspec := friedrichsRep_spec J m hJinj hJle hJdense f (friedrichsRep J m hJinj hJle hJdense f)
  have hnorm : ‖friedrichsRep J m hJinj hJle hJdense f‖ ^ 2
      = RCLike.re (inner 𝕜 f (J (friedrichsRep J m hJinj hJle hJdense f))) := by
    rw [← hspec, inner_self_eq_norm_sq_to_K]
    simp
  have hle : ‖friedrichsRep J m hJinj hJle hJdense f‖ ^ 2
      ≤ ‖f‖ * ‖friedrichsRep J m hJinj hJle hJdense f‖ := by
    rw [hnorm]
    calc RCLike.re (inner 𝕜 f (J (friedrichsRep J m hJinj hJle hJdense f)))
        ≤ ‖inner 𝕜 f (J (friedrichsRep J m hJinj hJle hJdense f))‖ :=
          RCLike.re_le_norm _
      _ ≤ ‖f‖ * ‖friedrichsRep J m hJinj hJle hJdense f‖ := by
          refine le_trans (norm_inner_le_norm _ _) ?_
          exact mul_le_mul_of_nonneg_left (hJle _) (norm_nonneg _)
  rcases eq_or_ne ‖friedrichsRep J m hJinj hJle hJdense f‖ 0 with hu0 | hu0
  · rw [hu0]; exact norm_nonneg _
  · have hpos' : 0 < ‖friedrichsRep J m hJinj hJle hJdense f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
    have h2 : ‖friedrichsRep J m hJinj hJle hJdense f‖ * ‖friedrichsRep J m hJinj hJle hJdense f‖
        ≤ ‖f‖ * ‖friedrichsRep J m hJinj hJle hJdense f‖ := by
      rwa [pow_two] at hle
    exact le_of_mul_le_mul_right h2 hpos'

/-- **The form-space resolvent** `B : H →L[𝕜] V` as a
continuous linear map of bound `1`. -/
noncomputable def friedrichsResolventForm (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →L[𝕜] V :=
  (friedrichsRepLin J m hJinj hJle hJdense).mkContinuous 1 (fun f => by
    rw [one_mul]
    exact friedrichsRep_norm_le J m hJinj hJle hJdense f)

theorem friedrichsResolventForm_apply (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    friedrichsResolventForm J m hJinj hJle hJdense f = friedrichsRep J m hJinj hJle hJdense f :=
  rfl

/-! ## §3. The bounded resolvent on `H` -/

/-- **The Friedrichs resolvent at the shift `c = 1 - m`**,
`R = J ∘L B : H →L[𝕜] H`. -/
noncomputable def friedrichsResolvent (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →L[𝕜] H :=
  J ∘L friedrichsResolventForm J m hJinj hJle hJdense

theorem friedrichsResolvent_apply (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    friedrichsResolvent J m hJinj hJle hJdense f = J (friedrichsRep J m hJinj hJle hJdense f) :=
  rfl

/-- **Symmetry of the resolvent**: `⟪Rf, g⟫ = ⟪f, Rg⟫` -
the conjugate symmetry of the form inner product,
transported through the Riesz characterization on both
sides. -/
theorem friedrichsResolvent_symmetric (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f g : H) :
    inner 𝕜 (friedrichsResolvent J m hJinj hJle hJdense f) g
      = inner 𝕜 f (friedrichsResolvent J m hJinj hJle hJdense g) := by
  calc inner 𝕜 (friedrichsResolvent J m hJinj hJle hJdense f) g
      = (starRingEnd 𝕜) (inner 𝕜 g
          (J (friedrichsRep J m hJinj hJle hJdense f))) := by
        rw [friedrichsResolvent_apply J m hJinj hJle hJdense]
        exact (inner_conj_symm _ _).symm
    _ = (starRingEnd 𝕜) (inner 𝕜
          (friedrichsRep J m hJinj hJle hJdense g)
          (friedrichsRep J m hJinj hJle hJdense f)) := by
        rw [← friedrichsRep_spec J m hJinj hJle hJdense]
    _ = inner 𝕜 (friedrichsRep J m hJinj hJle hJdense f)
          (friedrichsRep J m hJinj hJle hJdense g) :=
        inner_conj_symm _ _
    _ = inner 𝕜 f (J (friedrichsRep J m hJinj hJle hJdense g)) :=
        friedrichsRep_spec J m hJinj hJle hJdense f
          (friedrichsRep J m hJinj hJle hJdense g)
    _ = inner 𝕜 f (friedrichsResolvent J m hJinj hJle hJdense g) := by
        rw [friedrichsResolvent_apply J m hJinj hJle hJdense]

/-- The resolvent is self-adjoint as a bounded operator. -/
theorem friedrichsResolvent_isSelfAdjoint (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    IsSelfAdjoint (friedrichsResolvent J m hJinj hJle hJdense) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  exact friedrichsResolvent_symmetric J m hJinj hJle hJdense x y

/-- **Positivity of the resolvent**: `⟪Rf, f⟫ = ‖u_f‖²`,
a nonnegative real. -/
theorem friedrichsResolvent_inner_self (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    inner 𝕜 (friedrichsResolvent J m hJinj hJle hJdense f) f
      = ((‖friedrichsRep J m hJinj hJle hJdense f‖ ^ 2 : ℝ) : 𝕜) := by
  rw [friedrichsResolvent_apply J m hJinj hJle hJdense]
  have h := friedrichsRep_spec J m hJinj hJle hJdense f (friedrichsRep J m hJinj hJle hJdense f)
  have h2 : inner 𝕜 (J (friedrichsRep J m hJinj hJle hJdense f)) f
      = (starRingEnd 𝕜) (inner 𝕜 f (J (friedrichsRep J m hJinj hJle hJdense f))) :=
    (inner_conj_symm _ _).symm
  rw [h2, ← h, inner_conj_symm, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow]

/-- **Injectivity of the resolvent**: if `Rf = 0` then the
representative is zero, so `f` pairs trivially with the
dense form domain, hence `f = 0`. -/
theorem friedrichsResolvent_injective (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    Function.Injective (friedrichsResolvent J m hJinj hJle hJdense) := by
  have key : ∀ f : H, friedrichsResolvent J m hJinj hJle hJdense f = 0
      → f = 0 := by
    intro f hf
    rw [friedrichsResolvent_apply J m hJinj hJle hJdense] at hf
    have hrep0 : friedrichsRep J m hJinj hJle hJdense f = 0 :=
      hJinj (by rw [hf, map_zero])
    have hpair : ∀ x : V, inner 𝕜 f (J x) = 0 := by
      intro x
      have h := friedrichsRep_spec J m hJinj hJle hJdense f x
      rw [hrep0, inner_zero_left] at h
      exact h.symm
    exact (hJdense).eq_of_inner_left 𝕜
      (fun x => by rw [hpair x, inner_zero_left])
  intro a b hab
  have hsub : friedrichsResolvent J m hJinj hJle hJdense (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

/-! ## §4. The Friedrichs operator -/

/-- The inverse of the resolvent, as a linear map on its
range: `f ↦ R⁻¹ f`, carried on `↥(range R)`. -/
noncomputable def friedrichsInvResolvent (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    ↥(LinearMap.range (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap)
      →ₗ[𝕜] H :=
  (LinearEquiv.ofInjective
    (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap
    (by exact friedrichsResolvent_injective J m hJinj hJle hJdense)).symm.toLinearMap

/-- **The Friedrichs operator** `T`, as a partially defined
linear operator (`LinearPMap`) on `H`: domain the range of
the resolvent, `T = R⁻¹ - c` at the shift `c = 1 - m`,
i.e. `T(R f) = f - c • R f`. -/
noncomputable def friedrichsOperator (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →ₗ.[𝕜] H where
  domain := LinearMap.range (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap
  toFun := friedrichsInvResolvent J m hJinj hJle hJdense
    - (friedrichsShift J m hJinj hJle hJdense) •
        (LinearMap.range (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap).subtype

theorem friedrichsOperator_domain (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsOperator J m hJinj hJle hJdense).domain
      = LinearMap.range (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap :=
  rfl

/-- The preimage of a domain element: the unique `f` with
`R f = x`. -/
noncomputable def friedrichsPreimage (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) : H :=
  friedrichsInvResolvent J m hJinj hJle hJdense x

theorem friedrichsResolvent_preimage (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    friedrichsResolvent J m hJinj hJle hJdense (friedrichsPreimage J m hJinj hJle hJdense x)
      = x.1 := by
  have h := LinearEquiv.apply_symm_apply
    (LinearEquiv.ofInjective (friedrichsResolvent J m hJinj hJle hJdense).toLinearMap
      (by exact friedrichsResolvent_injective J m hJinj hJle hJdense)) ⟨x.1, x.2⟩
  have h2 := congrArg Subtype.val h
  rw [LinearEquiv.ofInjective_apply] at h2
  exact h2

/-- **The defining equation of `T`**: `T x = f - c • x`
whenever `x = R f`. -/
theorem friedrichsOperator_eq (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain)
    (f : H) (hf : friedrichsResolvent J m hJinj hJle hJdense f = x.1) :
    friedrichsOperator J m hJinj hJle hJdense x
      = f - (friedrichsShift J m hJinj hJle hJdense) • x.1 := by
  have hpre : friedrichsPreimage J m hJinj hJle hJdense x = f :=
    friedrichsResolvent_injective J m hJinj hJle hJdense (by
      rw [friedrichsResolvent_preimage J m hJinj hJle hJdense x]
      exact hf.symm)
  show friedrichsPreimage J m hJinj hJle hJdense x
      - (friedrichsShift J m hJinj hJle hJdense) • x.1 = f - (friedrichsShift J m hJinj hJle hJdense) • x.1
  rw [hpre]

theorem friedrichsOperator_resolvent (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    friedrichsOperator J m hJinj hJle hJdense
        ⟨friedrichsResolvent J m hJinj hJle hJdense f, LinearMap.mem_range_self _ f⟩
      = f - (friedrichsShift J m hJinj hJle hJdense) • (friedrichsResolvent J m hJinj hJle hJdense f) :=
  friedrichsOperator_eq J m hJinj hJle hJdense _ f rfl

/-- The lift of a domain element to the form space: the
Riesz representative of its preimage. Its `J`-image is the
domain element itself. -/
noncomputable def friedrichsLift (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) : V :=
  friedrichsRep J m hJinj hJle hJdense (friedrichsPreimage J m hJinj hJle hJdense x)

theorem friedrichsLift_image (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    J (friedrichsLift J m hJinj hJle hJdense x) = x.1 := by
  show J (friedrichsRep J m hJinj hJle hJdense (friedrichsPreimage J m hJinj hJle hJdense x))
      = x.1
  rw [← friedrichsResolvent_apply J m hJinj hJle hJdense]
  exact friedrichsResolvent_preimage J m hJinj hJle hJdense x

/-- **The representation identity** (Kato's first
representation theorem, form clause): for `x ∈ D(T)` with
form-space lift `xhat`, and every form-domain vector `z`,
`t(xhat, z) = ⟪Tx, Jz⟫`. -/
theorem friedrichsOperator_representation (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain)
    (z : V) :
    friedrichsForm J m hJinj hJle hJdense (friedrichsLift J m hJinj hJle hJdense x) z
      = inner 𝕜 (friedrichsOperator J m hJinj hJle hJdense x) (J z) := by
  set f := friedrichsPreimage J m hJinj hJle hJdense x with hf
  have hspec := friedrichsRep_spec J m hJinj hJle hJdense f z
  have hTx : friedrichsOperator J m hJinj hJle hJdense x
      = f - (friedrichsShift J m hJinj hJle hJdense) • x.1 :=
    friedrichsOperator_eq J m hJinj hJle hJdense x f
      (friedrichsResolvent_preimage J m hJinj hJle hJdense x)
  rw [friedrichsForm, hTx, friedrichsLift_image J m hJinj hJle hJdense x]
  show inner 𝕜 (friedrichsLift J m hJinj hJle hJdense x) z
      - friedrichsShift J m hJinj hJle hJdense * inner 𝕜 x.1 (J z)
    = inner 𝕜 (f - (friedrichsShift J m hJinj hJle hJdense) • x.1) (J z)
  rw [inner_sub_left, inner_smul_left]
  have hconj : (starRingEnd 𝕜) (friedrichsShift J m hJinj hJle hJdense) = friedrichsShift J m hJinj hJle hJdense := by
    simp [friedrichsShift]
  rw [hconj]
  have hrep : inner 𝕜 (friedrichsLift J m hJinj hJle hJdense x) z
      = inner 𝕜 f (J z) := hspec
  rw [hrep]

/-- The representation identity in the test-first slot
shape (by Hermitian symmetry): `t(z, xhat) = ⟪Jz, Tx⟫`. -/
theorem friedrichsOperator_representation' (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain)
    (z : V) :
    friedrichsForm J m hJinj hJle hJdense z (friedrichsLift J m hJinj hJle hJdense x)
      = inner 𝕜 (J z) (friedrichsOperator J m hJinj hJle hJdense x) := by
  have h := friedrichsOperator_representation J m hJinj hJle hJdense x z
  have hsymm := friedrichsForm_conj_symm J m hJinj hJle hJdense
    (friedrichsLift J m hJinj hJle hJdense x) z
  rw [← hsymm, h, inner_conj_symm]

/-- **Semiboundedness inherited**: `re ⟪Tx, x⟫ ≥ m‖x‖²` on
the operator domain - the form's lower bound, transported
by the representation identity at `z = xhat`. -/
theorem friedrichsOperator_semibounded (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    m * ‖x.1‖ ^ 2
      ≤ RCLike.re (inner 𝕜 (friedrichsOperator J m hJinj hJle hJdense x) x.1) := by
  have h := friedrichsOperator_representation J m hJinj hJle hJdense x
    (friedrichsLift J m hJinj hJle hJdense x)
  rw [friedrichsLift_image J m hJinj hJle hJdense x] at h
  have hlower := friedrichsForm_self_lower J m hJinj hJle hJdense
    (friedrichsLift J m hJinj hJle hJdense x)
  rw [friedrichsLift_image J m hJinj hJle hJdense x] at hlower
  rw [← h]
  exact hlower

/-- **Domain characterization** (the classical shape from
the brick statement): `x ∈ D(T)` iff `x` lies in the form
domain `D(t) = range J` and there is a `y ∈ H` with
`t(z, xhat) = ⟪Jz, y⟫` for every form-domain vector `z`,
where `xhat` is the (unique) lift of `x` to `V`. In that
case `y = Tx`. -/
theorem friedrichsOperator_mem_domain_iff (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (x : H) :
    x ∈ (friedrichsOperator J m hJinj hJle hJdense).domain
      ↔ ∃ xhat : V, J xhat = x
        ∧ ∃ y : H, ∀ z : V,
            friedrichsForm J m hJinj hJle hJdense z xhat = inner 𝕜 (J z) y := by
  constructor
  · intro hx
    refine ⟨friedrichsLift J m hJinj hJle hJdense ⟨x, hx⟩,
      friedrichsLift_image J m hJinj hJle hJdense ⟨x, hx⟩,
      friedrichsOperator J m hJinj hJle hJdense ⟨x, hx⟩, ?_⟩
    intro z
    exact friedrichsOperator_representation' J m hJinj hJle hJdense
      ⟨x, hx⟩ z
  · rintro ⟨xhat, hxhat, y, hy⟩
    -- From the form identity at all `z`, the pairing of `xhat`
    -- against every `z` in the form inner product is the
    -- pairing functional of `y + c • x`; Riesz uniqueness
    -- puts `xhat = B (y + c • x)`, hence `x = R (y + c • x)`.
    have hpair : ∀ z : V, inner 𝕜 xhat z
        = inner 𝕜 (y + (friedrichsShift J m hJinj hJle hJdense) • x) (J z) := by
      intro z
      have h2 : inner 𝕜 z xhat
          = friedrichsForm J m hJinj hJle hJdense z xhat
            + friedrichsShift J m hJinj hJle hJdense * inner 𝕜 (J z) x := by
        have h := friedrichsForm_add_shift J m hJinj hJle hJdense z xhat
        rw [hxhat] at h
        exact h.symm
      calc inner 𝕜 xhat z
          = (starRingEnd 𝕜) (inner 𝕜 z xhat) :=
            (inner_conj_symm xhat z).symm
        _ = (starRingEnd 𝕜) (friedrichsForm J m hJinj hJle hJdense z xhat
              + friedrichsShift J m hJinj hJle hJdense * inner 𝕜 (J z) x) := by
            rw [h2]
        _ = (starRingEnd 𝕜) (inner 𝕜 (J z) y
              + friedrichsShift J m hJinj hJle hJdense * inner 𝕜 (J z) x) := by
            rw [hy z]
        _ = (starRingEnd 𝕜) (inner 𝕜 (J z)
              (y + (friedrichsShift J m hJinj hJle hJdense) • x)) := by
            rw [inner_add_right, inner_smul_right]
        _ = inner 𝕜 (y + (friedrichsShift J m hJinj hJle hJdense) • x) (J z) :=
            inner_conj_symm _ _
    have hrep : xhat = friedrichsRep J m hJinj hJle hJdense (y + (friedrichsShift J m hJinj hJle hJdense) • x) := by
      apply friedrichsRep_unique J m hJinj hJle hJdense
      intro z
      rw [hpair z, friedrichsRep_spec J m hJinj hJle hJdense]
    have hxR : x = friedrichsResolvent J m hJinj hJle hJdense
        (y + (friedrichsShift J m hJinj hJle hJdense) • x) := by
      rw [friedrichsResolvent_apply J m hJinj hJle hJdense, ← hrep]
      exact hxhat.symm
    rw [friedrichsOperator_domain J m hJinj hJle hJdense, hxR]
    exact LinearMap.mem_range_self _ _

/-- On the domain characterized above, the representing
vector `y` is `Tx`. -/
theorem friedrichsOperator_eq_of_representation (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) {x : H}
    (hx : x ∈ (friedrichsOperator J m hJinj hJle hJdense).domain)
    {xhat : V} (hxhat : J xhat = x) {y : H}
    (hy : ∀ z : V, friedrichsForm J m hJinj hJle hJdense z xhat = inner 𝕜 (J z) y) :
    friedrichsOperator J m hJinj hJle hJdense ⟨x, hx⟩ = y := by
  have hTx := friedrichsOperator_representation' J m hJinj hJle hJdense
    ⟨x, hx⟩
  have hlift : friedrichsLift J m hJinj hJle hJdense ⟨x, hx⟩ = xhat :=
    hJinj (by rw [friedrichsLift_image J m hJinj hJle hJdense, hxhat])
  have huniq : ∀ z : V,
      inner 𝕜 (J z) (friedrichsOperator J m hJinj hJle hJdense ⟨x, hx⟩)
        = inner 𝕜 (J z) y := by
    intro z
    rw [← hTx z, hlift]
    exact hy z
  -- both sides pair equally against the dense range of `J`
  have hd : Dense (Set.range (J : V → H)) := hJdense
  have h := hd.eq_of_inner_left (𝕜 := 𝕜)
    (x := friedrichsOperator J m hJinj hJle hJdense ⟨x, hx⟩) (y := y)
  apply h
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  have h2 := huniq z
  rw [← inner_conj_symm (friedrichsOperator J m hJinj hJle hJdense ⟨x, hx⟩) (J z),
    ← inner_conj_symm y (J z), h2]

/-! ## §5. Self-adjointness -/

/-- Density of the range of a bounded self-adjoint
injective operator: the orthogonal complement of the range
lies in the kernel. -/
theorem dense_range_of_isSelfAdjoint_injective
    {A : H →L[𝕜] H} (hA : IsSelfAdjoint A)
    (hinj : Function.Injective A) :
    Dense (LinearMap.range A.toLinearMap : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hortho : (LinearMap.range A.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hAw : A w = 0 := by
      have h := hw (A (A w)) (LinearMap.mem_range_self _ _)
      have hsymm : inner 𝕜 (A (A w)) w = inner 𝕜 (A w) (A w) :=
        hA.isSymmetric (A w) w
      rw [hsymm] at h
      rwa [inner_self_eq_zero] at h
    have h0 : A w = A 0 := by rw [hAw, map_zero]
    exact hinj h0
  have hclosure :
      (LinearMap.range A.toLinearMap).topologicalClosureᗮ
        = ⊥ := by
    rw [Submodule.orthogonal_closure]
    exact hortho
  exact Submodule.orthogonal_eq_bot_iff.mp hclosure

/-- **Density of the operator domain**: the range of the
resolvent is dense in `H`. -/
theorem friedrichsOperator_dense_domain (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    Dense ((friedrichsOperator J m hJinj hJle hJdense).domain
      : Set H) := by
  rw [friedrichsOperator_domain J m hJinj hJle hJdense]
  exact dense_range_of_isSelfAdjoint_injective
    (A := friedrichsResolvent J m hJinj hJle hJdense)
    (friedrichsResolvent_isSelfAdjoint J m hJinj hJle hJdense)
    (friedrichsResolvent_injective J m hJinj hJle hJdense)

/-- **Symmetry of `T`** on its domain: `T` is a formal
adjoint of itself. -/
theorem friedrichsOperator_isFormalAdjoint_self (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsOperator J m hJinj hJle hJdense).IsFormalAdjoint
      (friedrichsOperator J m hJinj hJle hJdense) := by
  intro x y
  have hx := friedrichsOperator_representation J m hJinj hJle hJdense
    x (friedrichsLift J m hJinj hJle hJdense y)
  have hy := friedrichsOperator_representation J m hJinj hJle hJdense
    y (friedrichsLift J m hJinj hJle hJdense x)
  rw [friedrichsLift_image J m hJinj hJle hJdense y] at hx
  rw [friedrichsLift_image J m hJinj hJle hJdense x] at hy
  calc inner 𝕜 (friedrichsOperator J m hJinj hJle hJdense x) y.1
      = friedrichsForm J m hJinj hJle hJdense (friedrichsLift J m hJinj hJle hJdense x)
          (friedrichsLift J m hJinj hJle hJdense y) := hx.symm
    _ = (starRingEnd 𝕜) (friedrichsForm J m hJinj hJle hJdense
          (friedrichsLift J m hJinj hJle hJdense y)
          (friedrichsLift J m hJinj hJle hJdense x)) :=
        (friedrichsForm_conj_symm J m hJinj hJle hJdense _ _).symm
    _ = (starRingEnd 𝕜) (inner 𝕜
          (friedrichsOperator J m hJinj hJle hJdense y) x.1) := by
        rw [hy]
    _ = inner 𝕜 x.1 (friedrichsOperator J m hJinj hJle hJdense y) :=
        inner_conj_symm _ _

/-- **The adjoint-domain lemma**: every `y` in the domain
of `T†` is already in the domain of `T`, with the same
value. The proof is the resolvent trick: with
`w = T† y` and `f = w + c • y`, the element `u = Rf ∈ D(T)`
satisfies `(T + c) u = f`, and pairing against the
surjective range of `T + c` forces `u = y`. -/
theorem friedrichsOperator_adjoint_apply (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (y : (friedrichsOperator J m hJinj hJle hJdense)†.domain) :
    ∃ x : (friedrichsOperator J m hJinj hJle hJdense).domain,
      x.1 = y.1
      ∧ friedrichsOperator J m hJinj hJle hJdense x
        = LinearPMap.adjoint (friedrichsOperator J m hJinj hJle hJdense) y := by
  have hsymm : ∀ a b :
      (friedrichsOperator J m hJinj hJle hJdense).domain,
      inner 𝕜 (friedrichsOperator J m hJinj hJle hJdense a) b.1
        = inner 𝕜 a.1 (friedrichsOperator J m hJinj hJle hJdense b) :=
    fun a b => friedrichsOperator_isFormalAdjoint_self J m hJinj hJle hJdense a b
  have hadj : ∀ a :
      (friedrichsOperator J m hJinj hJle hJdense).domain,
      inner 𝕜 (LinearPMap.adjoint (friedrichsOperator J m hJinj hJle hJdense) y) a.1
        = inner 𝕜 y.1 (friedrichsOperator J m hJinj hJle hJdense a) :=
    fun a => LinearPMap.adjoint_isFormalAdjoint
      (friedrichsOperator_dense_domain J m hJinj hJle hJdense) y a
  have hshift_self : (starRingEnd 𝕜) (friedrichsShift J m hJinj hJle hJdense)
      = friedrichsShift J m hJinj hJle hJdense := by simp [friedrichsShift]
  -- the `(T + c)`-value of a domain element is its preimage
  have hTc : ∀ a :
      (friedrichsOperator J m hJinj hJle hJdense).domain,
      friedrichsOperator J m hJinj hJle hJdense a
        + (friedrichsShift J m hJinj hJle hJdense) • a.1
        = friedrichsPreimage J m hJinj hJle hJdense a := by
    intro a
    have h := friedrichsOperator_eq J m hJinj hJle hJdense a
      (friedrichsPreimage J m hJinj hJle hJdense a)
      (friedrichsResolvent_preimage J m hJinj hJle hJdense a)
    rw [h]
    abel
  -- abbreviations for the two resolvent points
  set f : H := LinearPMap.adjoint (friedrichsOperator J m hJinj hJle hJdense) y
    + (friedrichsShift J m hJinj hJle hJdense) • y.1 with hf
  set u : (friedrichsOperator J m hJinj hJle hJdense).domain :=
    ⟨friedrichsResolvent J m hJinj hJle hJdense f,
      LinearMap.mem_range_self _ f⟩ with hu
  have hpre_u : friedrichsPreimage J m hJinj hJle hJdense u = f := by
    apply friedrichsResolvent_injective J m hJinj hJle hJdense
    rw [friedrichsResolvent_preimage J m hJinj hJle hJdense u, hu]
  have hTc_u : friedrichsOperator J m hJinj hJle hJdense u
      + (friedrichsShift J m hJinj hJle hJdense) • u.1 = f := by
    have h := hTc u
    rwa [hpre_u] at h
  -- the pairing identity: `u` and `y` pair equally against
  -- every vector of `H`
  have hu_eq : ∀ h : H, inner 𝕜 u.1 h = inner 𝕜 y.1 h := by
    intro h
    set a : (friedrichsOperator J m hJinj hJle hJdense).domain :=
      ⟨friedrichsResolvent J m hJinj hJle hJdense h,
        LinearMap.mem_range_self _ h⟩ with ha
    have hpre_a : friedrichsPreimage J m hJinj hJle hJdense a = h := by
      apply friedrichsResolvent_injective J m hJinj hJle hJdense
      rw [friedrichsResolvent_preimage J m hJinj hJle hJdense a, ha]
    have hTc_a : friedrichsOperator J m hJinj hJle hJdense a
        + (friedrichsShift J m hJinj hJle hJdense) • a.1 = h := by
      have h2 := hTc a
      rwa [hpre_a] at h2
    have hTu : friedrichsOperator J m hJinj hJle hJdense u
        = f - (friedrichsShift J m hJinj hJle hJdense) • u.1 := by
      have h2 := hTc_u
      rw [← h2]
      abel
    calc inner 𝕜 u.1 h
        = inner 𝕜 u.1 (friedrichsOperator J m hJinj hJle hJdense a
            + (friedrichsShift J m hJinj hJle hJdense) • a.1) := by rw [hTc_a]
      _ = inner 𝕜 u.1 (friedrichsOperator J m hJinj hJle hJdense a)
            + (friedrichsShift J m hJinj hJle hJdense) * inner 𝕜 u.1 a.1 := by
          rw [inner_add_right, inner_smul_right]
      _ = inner 𝕜 (friedrichsOperator J m hJinj hJle hJdense u) a.1
            + (friedrichsShift J m hJinj hJle hJdense) * inner 𝕜 u.1 a.1 := by
          have e1 : inner 𝕜 u.1 (friedrichsOperator J m hJinj hJle hJdense a)
              = (starRingEnd 𝕜) (inner 𝕜
                  (friedrichsOperator J m hJinj hJle hJdense a) u.1) :=
            (inner_conj_symm _ _).symm
          rw [e1, hsymm a u, inner_conj_symm]
      _ = inner 𝕜 (f - (friedrichsShift J m hJinj hJle hJdense) • u.1) a.1
            + (friedrichsShift J m hJinj hJle hJdense) * inner 𝕜 u.1 a.1 := by
          rw [hTu]
      _ = inner 𝕜 f a.1 := by
          rw [inner_sub_left, inner_smul_left, hshift_self]
          abel
      _ = inner 𝕜 (LinearPMap.adjoint (friedrichsOperator J m hJinj hJle hJdense) y) a.1
            + (friedrichsShift J m hJinj hJle hJdense) * inner 𝕜 y.1 a.1 := by
          rw [hf, inner_add_left, inner_smul_left, hshift_self]
      _ = inner 𝕜 y.1 (friedrichsOperator J m hJinj hJle hJdense a)
            + (friedrichsShift J m hJinj hJle hJdense) * inner 𝕜 y.1 a.1 := by
          rw [hadj a]
      _ = inner 𝕜 y.1 (friedrichsOperator J m hJinj hJle hJdense a
            + (friedrichsShift J m hJinj hJle hJdense) • a.1) := by
          rw [inner_add_right, inner_smul_right]
      _ = inner 𝕜 y.1 h := by rw [hTc_a]
  have hu_y : u.1 = y.1 := by
    have hself : inner 𝕜 (u.1 - y.1) (u.1 - y.1) = 0 := by
      have h1 := hu_eq (u.1 - y.1)
      have h2 := hu_eq u.1
      have h3 := hu_eq y.1
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        ← h2, ← h3]
      exact sub_self _
    rw [inner_self_eq_zero, sub_eq_zero] at hself
    exact hself
  refine ⟨u, hu_y, ?_⟩
  have hTu : friedrichsOperator J m hJinj hJle hJdense u
      = f - (friedrichsShift J m hJinj hJle hJdense) • u.1 := by
    have h2 := hTc_u
    rw [← h2]
    abel
  rw [hTu, hu_y, hf]
  abel

/-- **The resolvent-sense characterization** (the seat
dialect's self-adjointness content, also proved here):
`T + c` maps `D(T)` onto all of `H` - every `f` is
`c • x + Tx` for `x = Rf`. -/
theorem friedrichsOperator_add_shift_surjective (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    ∃ x : (friedrichsOperator J m hJinj hJle hJdense).domain,
      (friedrichsShift J m hJinj hJle hJdense) • x.1
        + friedrichsOperator J m hJinj hJle hJdense x = f := by
  refine ⟨⟨friedrichsResolvent J m hJinj hJle hJdense f,
    LinearMap.mem_range_self _ f⟩, ?_⟩
  rw [friedrichsOperator_resolvent J m hJinj hJle hJdense f]
  abel

/-- `T ≤ T†`: maximality of the adjoint applied to the
formal self-adjointness of `T`. -/
theorem friedrichsOperator_le_adjoint (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    friedrichsOperator J m hJinj hJle hJdense
      ≤ (friedrichsOperator J m hJinj hJle hJdense)† :=
  (friedrichsOperator_isFormalAdjoint_self J m hJinj hJle hJdense).le_adjoint
    (friedrichsOperator_dense_domain J m hJinj hJle hJdense)

/-- `T† ≤ T`: the adjoint-domain lemma, in the order
dialect (domain inclusion plus agreement on the domain). -/
theorem friedrichsOperator_adjoint_le (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsOperator J m hJinj hJle hJdense)†
      ≤ friedrichsOperator J m hJinj hJle hJdense := by
  constructor
  · intro y hy
    obtain ⟨x, hx, -⟩ := friedrichsOperator_adjoint_apply J m hJinj hJle hJdense ⟨y, hy⟩
    have hx' : x.1 = y := hx
    rw [← hx']
    exact x.2
  · intro x y hxy
    obtain ⟨u, hu1, hu2⟩ := friedrichsOperator_adjoint_apply J m hJinj hJle hJdense x
    have hy : y = u := Subtype.ext (hxy.symm.trans hu1.symm)
    rw [hy]
    exact hu2.symm

/-- **SELF-ADJOINTNESS of the Friedrichs operator**, in
the pin's `LinearPMap` graph dialect: `T† = T`, i.e.
`IsSelfAdjoint T`. Fully proved - not a resolvent-sense
substitute (that characterization is
`friedrichsOperator_add_shift_surjective` above, also
proved). -/
theorem friedrichsOperator_isSelfAdjoint (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    IsSelfAdjoint (friedrichsOperator J m hJinj hJle hJdense) := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (friedrichsOperator_adjoint_le J m hJinj hJle hJdense) (friedrichsOperator_le_adjoint J m hJinj hJle hJdense)

/-- The operator is closed (a general consequence of
self-adjointness in the pin's dialect). -/
theorem friedrichsOperator_isClosed (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsOperator J m hJinj hJle hJdense).IsClosed :=
  (friedrichsOperator_isSelfAdjoint J m hJinj hJle hJdense).isClosed

/-! ## §6. Positivity of the resolvent, C*-algebra form -/

/-- Uniqueness of vectors in `H` by their pairings in the
second slot. -/
theorem eq_of_inner_right_H {a b : H}
    (h : ∀ x : H, inner 𝕜 x a = inner 𝕜 x b) : a = b := by
  have hsub : ∀ x : H, inner 𝕜 x (a - b) = 0 := fun x => by
    rw [inner_sub_right, h x, sub_self]
  have hself := hsub (a - b)
  rw [inner_self_eq_zero] at hself
  exact sub_eq_zero.mp hself

/-- The adjoint of the form-space resolvent is the
inclusion: `B† = J` (the Riesz characterization read
backwards). -/
theorem friedrichsResolventForm_adjoint (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    ContinuousLinearMap.adjoint (friedrichsResolventForm J m hJinj hJle hJdense) = J := by
  ext x
  apply eq_of_inner_right_H (𝕜 := 𝕜)
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right,
    friedrichsResolventForm_apply J m hJinj hJle hJdense]
  exact friedrichsRep_spec J m hJinj hJle hJdense f x

/-- The resolvent factors as `R = B† ∘L B` (with `B† = J`),
hence is nonnegative in the C*-algebra order on bounded
operators: `0 ≤ R`. -/
theorem friedrichsResolvent_nonneg (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    0 ≤ friedrichsResolvent J m hJinj hJle hJdense := by
  rw [ContinuousLinearMap.le_def, sub_zero]
  have hfactor : friedrichsResolvent J m hJinj hJle hJdense
      = ContinuousLinearMap.adjoint
          (friedrichsResolventForm J m hJinj hJle hJdense)
        ∘L (friedrichsResolventForm J m hJinj hJle hJdense) := by
    have e : friedrichsResolvent J m hJinj hJle hJdense
        = J ∘L (friedrichsResolventForm J m hJinj hJle hJdense) := rfl
    rw [e, friedrichsResolventForm_adjoint J m hJinj hJle hJdense]
  rw [hfactor]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The resolvent is positive as a bounded operator
(Mathlib's `ContinuousLinearMap.IsPositive`). -/
theorem friedrichsResolvent_isPositive (J : V →L[𝕜] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsResolvent J m hJinj hJle hJdense).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨friedrichsResolvent_isSelfAdjoint J m hJinj hJle hJdense, ?_⟩
  intro f
  show 0 ≤ RCLike.re (inner 𝕜 (friedrichsResolvent J m hJinj hJle hJdense f) f)
  rw [friedrichsResolvent_inner_self J m hJinj hJle hJdense f]
  simp [sq_nonneg]

end FriedrichsExtension

section FriedrichsSqrtComplex

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## §7. The Kato square root

GENERALITY BOUNDARY (named, at this pin): this section is
stated over `ℂ`. The bounded square root is built with
the pin's `CFC.sqrt`, whose real continuous functional
calculus for bounded-operator algebras is available at
`ℂ` but does not synthesize at an abstract `RCLike`
field in this pin (the instance search for
`Module ℝ (H →L[𝕜] H)` fails at a general `RCLike`
field `𝕜`; the pin's own note in
`Mathlib/Analysis/InnerProductSpace/StarOrder.lean`
records that the real CFC for `H →L[𝕜] H` is, for the
moment, only had for `𝕜 := ℂ`). The core construction
(§§1-6) is proved at full `RCLike` generality; only this
square-root clause is `ℂ`-bound.

The shifted operator `T + c` (with `c = 1 - m ≥` the
Friedrichs shift; `T + c = R⁻¹` on `D(T)`) has a
self-adjoint square root `S`, constructed as the inverse
of the bounded square root `√R` of the resolvent
(continuous functional calculus on the C*-algebra of
bounded operators). What is proved here:

* `S` is a self-adjoint `LinearPMap` (`S† = S`), positive
  on its domain;
* `D(T) ⊆ D(S)`, and on `D(T)`: `S² = T + c` and the Kato
  identity `‖Sx‖² = ‖xhat‖²_V` - the form norm of the lift
  is the graph norm of the root.

NAMED REMAINDER (Seam A, open on the face): the exact
domain equality `D(S) = D(t)` (i.e. `range √R = range J`
as subsets of `H`) and hence the Kato identity on all of
`D(t)`, not only on `D(T)`, are NOT proved here. The
obstruction at this pin is the intertwining
`J ∘ (BJ)^{1/2} = (JB)^{1/2} ∘ J` for the form-space
resolvent product, which the pin's CFC does not supply
for noncommuting products. -/

/-- The bounded square root of the resolvent, by the
continuous functional calculus. -/
noncomputable def friedrichsSqrtResolvent (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →L[ℂ] H :=
  CFC.sqrt (friedrichsResolvent J m hJinj hJle hJdense)

theorem friedrichsSqrtResolvent_mul_self (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    friedrichsSqrtResolvent J m hJinj hJle hJdense
      * friedrichsSqrtResolvent J m hJinj hJle hJdense
      = friedrichsResolvent J m hJinj hJle hJdense :=
  CFC.sqrt_mul_sqrt_self _ (friedrichsResolvent_nonneg J m hJinj hJle hJdense)

theorem friedrichsSqrtResolvent_apply_apply (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    friedrichsSqrtResolvent J m hJinj hJle hJdense
        (friedrichsSqrtResolvent J m hJinj hJle hJdense f)
      = friedrichsResolvent J m hJinj hJle hJdense f := by
  have h := friedrichsSqrtResolvent_mul_self J m hJinj hJle hJdense
  have h2 := DFunLike.congr_fun h f
  rwa [ContinuousLinearMap.mul_apply] at h2

theorem friedrichsSqrtResolvent_isSelfAdjoint (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    IsSelfAdjoint (friedrichsSqrtResolvent J m hJinj hJle hJdense) := by
  show IsSelfAdjoint (CFC.sqrt (friedrichsResolvent J m hJinj hJle hJdense))
  cfc_tac

theorem friedrichsSqrtResolvent_symmetric (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (a b : H) :
    inner ℂ (friedrichsSqrtResolvent J m hJinj hJle hJdense a) b
      = inner ℂ a (friedrichsSqrtResolvent J m hJinj hJle hJdense b) :=
  (friedrichsSqrtResolvent_isSelfAdjoint J m hJinj hJle hJdense).isSymmetric a b

theorem friedrichsSqrtResolvent_injective (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    Function.Injective (friedrichsSqrtResolvent J m hJinj hJle hJdense) := by
  have key : ∀ x : H, friedrichsSqrtResolvent J m hJinj hJle hJdense x = 0
      → x = 0 := by
    intro x hx
    have hR : friedrichsResolvent J m hJinj hJle hJdense x = 0 := by
      rw [← friedrichsSqrtResolvent_apply_apply J m hJinj hJle hJdense x, hx,
        map_zero]
    have h0 : friedrichsResolvent J m hJinj hJle hJdense x
        = friedrichsResolvent J m hJinj hJle hJdense 0 := by
      rw [hR, map_zero]
    exact friedrichsResolvent_injective J m hJinj hJle hJdense h0
  intro a b hab
  have hsub : friedrichsSqrtResolvent J m hJinj hJle hJdense (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

/-- Positivity of `√R` as a bounded operator: `√R = s ∘L s`
for `s = √(√R)`, so `⟪√R f, f⟫ = ‖s f‖²`. -/
theorem friedrichsSqrtResolvent_inner_self_nonneg (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (f : H) :
    0 ≤ RCLike.re (inner ℂ (friedrichsSqrtResolvent J m hJinj hJle hJdense f) f) := by
  set s := CFC.sqrt (friedrichsSqrtResolvent J m hJinj hJle hJdense) with hs
  have hss : s * s = friedrichsSqrtResolvent J m hJinj hJle hJdense :=
    CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
  have hsf : friedrichsSqrtResolvent J m hJinj hJle hJdense f = s (s f) := by
    have h2 := DFunLike.congr_fun hss f
    rw [ContinuousLinearMap.mul_apply] at h2
    exact h2.symm
  have hsymm : ∀ a b : H, inner ℂ (s a) b = inner ℂ a (s b) :=
    fun a b => (IsSelfAdjoint.of_nonneg
      (CFC.sqrt_nonneg (friedrichsSqrtResolvent J m hJinj hJle hJdense))).isSymmetric a b
  rw [hsf, hsymm (s f) f, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sq_nonneg _

/-- **The Kato square root** `S = (T + c)^{1/2}` as a
partially defined operator: the inverse of `√R`. -/
noncomputable def friedrichsSqrt (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) : H →ₗ.[ℂ] H where
  domain := LinearMap.range
    (friedrichsSqrtResolvent J m hJinj hJle hJdense).toLinearMap
  toFun := (LinearEquiv.ofInjective
    (friedrichsSqrtResolvent J m hJinj hJle hJdense).toLinearMap
    (by exact friedrichsSqrtResolvent_injective J m hJinj hJle hJdense)).symm.toLinearMap

/-- The resolvent preimage of an `S`-domain element:
`√R (S x) = x`. -/
theorem friedrichsSqrt_resolvent_preimage (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsSqrt J m hJinj hJle hJdense).domain) :
    friedrichsSqrtResolvent J m hJinj hJle hJdense
        (friedrichsSqrt J m hJinj hJle hJdense x) = x.1 := by
  have h := LinearEquiv.apply_symm_apply
    (LinearEquiv.ofInjective
      (friedrichsSqrtResolvent J m hJinj hJle hJdense).toLinearMap
      (by exact friedrichsSqrtResolvent_injective J m hJinj hJle hJdense)) ⟨x.1, x.2⟩
  have h2 := congrArg Subtype.val h
  rw [LinearEquiv.ofInjective_apply] at h2
  exact h2

/-- The value of `S` at a domain element is its unique
`√R`-preimage. -/
theorem friedrichsSqrt_injective_value (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsSqrt J m hJinj hJle hJdense).domain)
    (a : H) (ha : friedrichsSqrtResolvent J m hJinj hJle hJdense a = x.1) :
    friedrichsSqrt J m hJinj hJle hJdense x = a :=
  friedrichsSqrtResolvent_injective J m hJinj hJle hJdense (by
    rw [friedrichsSqrt_resolvent_preimage J m hJinj hJle hJdense x]
    exact ha.symm)

theorem friedrichsSqrt_apply (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) (a : H) :
    friedrichsSqrt J m hJinj hJle hJdense
        ⟨friedrichsSqrtResolvent J m hJinj hJle hJdense a,
          LinearMap.mem_range_self _ a⟩ = a :=
  friedrichsSqrt_injective_value J m hJinj hJle hJdense _ a rfl

theorem friedrichsSqrt_isFormalAdjoint_self (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    (friedrichsSqrt J m hJinj hJle hJdense).IsFormalAdjoint
      (friedrichsSqrt J m hJinj hJle hJdense) := by
  intro x y
  obtain ⟨a, ha⟩ : ∃ a : H,
      friedrichsSqrtResolvent J m hJinj hJle hJdense a = x.1 := x.2
  obtain ⟨b, hb⟩ : ∃ b : H,
      friedrichsSqrtResolvent J m hJinj hJle hJdense b = y.1 := y.2
  have hx : friedrichsSqrt J m hJinj hJle hJdense x = a :=
    friedrichsSqrt_injective_value J m hJinj hJle hJdense x a ha
  have hy : friedrichsSqrt J m hJinj hJle hJdense y = b :=
    friedrichsSqrt_injective_value J m hJinj hJle hJdense y b hb
  rw [hx, hy, ← ha, ← hb]
  exact (friedrichsSqrtResolvent_symmetric J m hJinj hJle hJdense a b).symm

theorem friedrichsSqrt_dense_domain (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    Dense ((friedrichsSqrt J m hJinj hJle hJdense).domain
      : Set H) :=
  dense_range_of_isSelfAdjoint_injective
    (A := friedrichsSqrtResolvent J m hJinj hJle hJdense)
    (friedrichsSqrtResolvent_isSelfAdjoint J m hJinj hJle hJdense)
    (friedrichsSqrtResolvent_injective J m hJinj hJle hJdense)

/-- The adjoint-domain lemma for `S`, by the same trick as
for `T` but one level down: pairing against the points
`√R a` (on which `S` is explicit) forces any adjoint
vector back into the range of `√R`. -/
theorem friedrichsSqrt_adjoint_apply (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (y : (friedrichsSqrt J m hJinj hJle hJdense)†.domain) :
    ∃ x : (friedrichsSqrt J m hJinj hJle hJdense).domain,
      x.1 = y.1
      ∧ friedrichsSqrt J m hJinj hJle hJdense x
        = LinearPMap.adjoint (friedrichsSqrt J m hJinj hJle hJdense) y := by
  have hadj : ∀ a :
      (friedrichsSqrt J m hJinj hJle hJdense).domain,
      inner ℂ (LinearPMap.adjoint (friedrichsSqrt J m hJinj hJle hJdense) y) a.1
        = inner ℂ y.1 (friedrichsSqrt J m hJinj hJle hJdense a) :=
    fun a => LinearPMap.adjoint_isFormalAdjoint
      (friedrichsSqrt_dense_domain J m hJinj hJle hJdense) y a
  set w := LinearPMap.adjoint (friedrichsSqrt J m hJinj hJle hJdense) y with hw
  refine ⟨⟨friedrichsSqrtResolvent J m hJinj hJle hJdense w,
    LinearMap.mem_range_self _ w⟩, ?_, ?_⟩
  · -- `√R w = y` by pairing against every `a`
    apply eq_of_inner_right_H (𝕜 := ℂ)
    intro a
    calc inner ℂ a (friedrichsSqrtResolvent J m hJinj hJle hJdense w)
        = inner ℂ (friedrichsSqrtResolvent J m hJinj hJle hJdense a) w :=
          (friedrichsSqrtResolvent_symmetric J m hJinj hJle hJdense a w).symm
      _ = (starRingEnd ℂ) (inner ℂ w
            (friedrichsSqrtResolvent J m hJinj hJle hJdense a)) :=
          (inner_conj_symm _ _).symm
      _ = (starRingEnd ℂ) (inner ℂ y.1 a) := by
          congr 1
          have h := hadj ⟨friedrichsSqrtResolvent J m hJinj hJle hJdense a,
            LinearMap.mem_range_self _ a⟩
          rw [friedrichsSqrt_apply J m hJinj hJle hJdense a] at h
          exact h
      _ = inner ℂ a y.1 := inner_conj_symm _ _
  · exact friedrichsSqrt_apply J m hJinj hJle hJdense w

/-- **Self-adjointness of the Kato square root**: `S† = S`. -/
theorem friedrichsSqrt_isSelfAdjoint (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J) :
    IsSelfAdjoint (friedrichsSqrt J m hJinj hJle hJdense) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · constructor
    · intro y hy
      obtain ⟨x, hx, -⟩ := friedrichsSqrt_adjoint_apply J m hJinj hJle hJdense ⟨y, hy⟩
      have hx' : x.1 = y := hx
      rw [← hx']
      exact x.2
    · intro x y hxy
      obtain ⟨u, hu1, hu2⟩ := friedrichsSqrt_adjoint_apply J m hJinj hJle hJdense x
      have hy : y = u := Subtype.ext (hxy.symm.trans hu1.symm)
      rw [hy]
      exact hu2.symm
  · exact (friedrichsSqrt_isFormalAdjoint_self J m hJinj hJle hJdense).le_adjoint
      (friedrichsSqrt_dense_domain J m hJinj hJle hJdense)

/-- **Positivity of `S`** on its domain. -/
theorem friedrichsSqrt_inner_self_nonneg (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsSqrt J m hJinj hJle hJdense).domain) :
    0 ≤ RCLike.re (inner ℂ (friedrichsSqrt J m hJinj hJle hJdense x)
      x.1) := by
  obtain ⟨a, ha⟩ : ∃ a : H,
      friedrichsSqrtResolvent J m hJinj hJle hJdense a = x.1 := x.2
  have hx : friedrichsSqrt J m hJinj hJle hJdense x = a :=
    friedrichsSqrt_injective_value J m hJinj hJle hJdense x a ha
  rw [hx, ← ha, ← friedrichsSqrtResolvent_symmetric J m hJinj hJle hJdense a a]
  exact friedrichsSqrtResolvent_inner_self_nonneg J m hJinj hJle hJdense a

/-- `D(T) ⊆ D(S)`: an operator-domain element, seen as a
point of `H`, lies in the domain of `S` - it is
`√R (√R f)` for its resolvent preimage `f`. -/
theorem friedrichsOperatorDomain_le_sqrtDomain (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    x.1 ∈ (friedrichsSqrt J m hJinj hJle hJdense).domain := by
  refine ⟨friedrichsSqrtResolvent J m hJinj hJle hJdense
    (friedrichsPreimage J m hJinj hJle hJdense x), ?_⟩
  show friedrichsSqrtResolvent J m hJinj hJle hJdense
      (friedrichsSqrtResolvent J m hJinj hJle hJdense
        (friedrichsPreimage J m hJinj hJle hJdense x)) = x.1
  rw [friedrichsSqrtResolvent_apply_apply J m hJinj hJle hJdense]
  exact friedrichsResolvent_preimage J m hJinj hJle hJdense x

/-- The value of `S` at an operator-domain element:
`S x = √R f` for the resolvent preimage `f` of `x`. -/
theorem friedrichsSqrt_apply_operatorDomain (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    friedrichsSqrt J m hJinj hJle hJdense
        ⟨x.1, friedrichsOperatorDomain_le_sqrtDomain J m hJinj hJle hJdense x⟩
      = friedrichsSqrtResolvent J m hJinj hJle hJdense
          (friedrichsPreimage J m hJinj hJle hJdense x) := by
  apply friedrichsSqrt_injective_value J m hJinj hJle hJdense
  rw [friedrichsSqrtResolvent_apply_apply J m hJinj hJle hJdense]
  exact friedrichsResolvent_preimage J m hJinj hJle hJdense x

/-- **The Kato identity on `D(T)`**:
`‖S x‖² = ‖xhat‖²` - the graph norm of the square root is
the form norm of the lift. -/
theorem friedrichsSqrt_kato_identity (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    ‖friedrichsSqrt J m hJinj hJle hJdense
        ⟨x.1, friedrichsOperatorDomain_le_sqrtDomain J m hJinj hJle hJdense x⟩‖ ^ 2
      = ‖friedrichsLift J m hJinj hJle hJdense x‖ ^ 2 := by
  have hnorm : ∀ z : H, ‖z‖ ^ 2 = RCLike.re (inner ℂ z z) := by
    intro z
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  have hnormV : ∀ z : V, ‖z‖ ^ 2 = RCLike.re (inner ℂ z z) := by
    intro z
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  rw [friedrichsSqrt_apply_operatorDomain J m hJinj hJle hJdense x,
    hnorm, hnormV]
  have h1 : RCLike.re (inner ℂ (friedrichsSqrtResolvent J m hJinj hJle hJdense
        (friedrichsPreimage J m hJinj hJle hJdense x))
      (friedrichsSqrtResolvent J m hJinj hJle hJdense
        (friedrichsPreimage J m hJinj hJle hJdense x)))
    = RCLike.re (inner ℂ (friedrichsResolvent J m hJinj hJle hJdense
        (friedrichsPreimage J m hJinj hJle hJdense x))
      (friedrichsPreimage J m hJinj hJle hJdense x)) := by
    congr 1
    rw [← friedrichsSqrtResolvent_symmetric J m hJinj hJle hJdense
        (friedrichsSqrtResolvent J m hJinj hJle hJdense
          (friedrichsPreimage J m hJinj hJle hJdense x))
        (friedrichsPreimage J m hJinj hJle hJdense x),
      friedrichsSqrtResolvent_apply_apply J m hJinj hJle hJdense]
  rw [h1, friedrichsResolvent_preimage J m hJinj hJle hJdense x]
  have h2 : inner ℂ (friedrichsLift J m hJinj hJle hJdense x)
      (friedrichsLift J m hJinj hJle hJdense x)
    = inner ℂ (friedrichsPreimage J m hJinj hJle hJdense x) x.1 := by
    have h := friedrichsRep_spec J m hJinj hJle hJdense
      (friedrichsPreimage J m hJinj hJle hJdense x)
      (friedrichsLift J m hJinj hJle hJdense x)
    rwa [friedrichsLift_image J m hJinj hJle hJdense x] at h
  have h3 : RCLike.re (inner ℂ (friedrichsPreimage J m hJinj hJle hJdense x)
      x.1)
    = RCLike.re (inner ℂ x.1
        (friedrichsPreimage J m hJinj hJle hJdense x)) := by
    have hconj := inner_conj_symm (𝕜 := ℂ)
      (friedrichsPreimage J m hJinj hJle hJdense x) x.1
    have hre := congrArg RCLike.re hconj
    simp only [RCLike.conj_re] at hre
    exact hre.symm
  rw [← h3, ← h2]

/-- **`S² = T + c` on `D(T)`**: for `x ∈ D(T)`, the vector
`S x` lies in `D(S)` and `S (S x) = Tx + c • x` - the
square of the root is the shifted Friedrichs operator, on
the operator domain. -/
theorem friedrichsSqrt_sq_on_operatorDomain (J : V →L[ℂ] H) (m : ℝ) (hJinj : Function.Injective J) (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (x : (friedrichsOperator J m hJinj hJle hJdense).domain) :
    ∃ y : (friedrichsSqrt J m hJinj hJle hJdense).domain,
      y.1 = friedrichsSqrt J m hJinj hJle hJdense
          ⟨x.1, friedrichsOperatorDomain_le_sqrtDomain J m hJinj hJle hJdense x⟩
      ∧ friedrichsSqrt J m hJinj hJle hJdense y
        = friedrichsOperator J m hJinj hJle hJdense x
          + (friedrichsShift J m hJinj hJle hJdense) • x.1 := by
  refine ⟨⟨friedrichsSqrtResolvent J m hJinj hJle hJdense
      (friedrichsPreimage J m hJinj hJle hJdense x),
      LinearMap.mem_range_self _ _⟩, ?_, ?_⟩
  · exact (friedrichsSqrt_apply_operatorDomain J m hJinj hJle hJdense x).symm
  · rw [friedrichsSqrt_apply J m hJinj hJle hJdense]
    have h := friedrichsOperator_eq J m hJinj hJle hJdense x
      (friedrichsPreimage J m hJinj hJle hJdense x)
      (friedrichsResolvent_preimage J m hJinj hJle hJdense x)
    rw [h]
    abel

end FriedrichsSqrtComplex

end ThetLogos
