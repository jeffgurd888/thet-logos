/-
# SHELF-1c - analytic semigroups / sectorial (working label)

Brick SHELF-1c of the SHELF line: holomorphic extension in
complex time of the bounded-generator semigroup, and the
sectorial read-backs the bounded/finite seats honestly
carry. Built against SHELF-1a (`SemigroupCore.lean`:
`C0Semigroup`, `HasGen`, `expSemigroup`, `ResolventSpec`)
and SHELF-1b (`SemigroupGeneration.lean`: `DissBound`,
`HasResolventAt`, Lumer-Phillips / Hille-Yosida), which are
consumed, not modified. NO CLAIM beyond the theorems
below.

## Probe of the pin (Mathlib v4.35.0-rc3), done first

* Sectorial operators: ABSENT. Grep for `sectorial` over
  `Mathlib/Analysis` (and the whole tree spot-checked)
  returns nothing: no sectorial-operator definition, no
  sectorial resolvent estimate, no analytic-semigroup
  definition, no holomorphic semigroup material.
* Fractional powers of operators: ABSENT. The pin has
  scalar `Complex.cpow` / `Real.rpow` only; no operator
  fractional-power API.
* What the pin DOES have, and what this brick consumes:
  `NormedSpace.exp` in a Banach algebra with
  `NormedSpace.exp_add_of_commute` and
  `NormedSpace.exp_analytic`; the complex-time derivative
  API `hasDerivAt_exp_smul_const` /
  `hasDerivAt_exp_smul_const'` /
  `hasFDerivAt_exp_smul_const`
  (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`),
  valid for `u • A` with `u : ℂ` in a Banach algebra over
  `ℂ`; and the Banach-algebra resolvent API
  `resolvent` / `resolventSet` (root-level definitions) with
  `spectrum.mem_resolventSet_of_norm_lt_mul` and
  `spectrum.resolvent_tendsto_cobounded`
  (`Mathlib/Analysis/Normed/Algebra/Spectrum.lean`).
* Relation to SHELF-1a's named remainders: 1c is NOT one
  of them (the Laplace resolvent integral formula remains
  a named remainder of 1a/1b, untouched here). 1c is the
  registered analytic extension of the same bounded seat
  whose real-time semigroup is 1a's `expSemigroup`.

## The seat, and why the extension is entire here

SHELF-1a is real: `expSemigroup A` for `A : E →L[ℝ] E`.
The bounded seat over `ℂ` is taken here directly: for a
COMPLEX Banach space `E` and a bounded `A : E →L[ℂ] E`,
`cexpSemigroup A z = NormedSpace.exp (z • A)`. At a
bounded seat the holomorphic extension is not confined
to a sector: it is entire (differentiable, indeed
analytic, at every `z : ℂ`), the semigroup law holds for
ALL complex times (a group law, with inverse
`cexpSemigroup A (-z)`), and the growth bound
`‖cexpSemigroup A z‖ ≤ Real.exp (‖z‖ * ‖A‖)` holds in
every direction. Finite-dimensional complex seats are
instances of this seat (every operator there is bounded);
no separate finite-dimensional hypothesis is needed.

## Sectorial read-backs proved at this seat

* Smoothing/intertwining: `cexpSemigroup A z` commutes
  with `A`, is surjective (two-sided inverse
  `cexpSemigroup A (-z)`), and every orbit
  `z ↦ cexpSemigroup A z x` is differentiable with
  derivative `cexpSemigroup A z (A x)` — at the bounded
  seat the "domain" is all of `E`, so this is the exact
  form smoothing takes here.
* Real-axis read-back: restriction to real times recovers
  a semigroup law on `ℝ` and the bound
  `‖cexpSemigroup A t‖ ≤ Real.exp (t * ‖A‖)` for `t ≥ 0`.
  (No contraction claim: `A` is an arbitrary bounded
  operator, not assumed dissipative in 1b's `DissBound`
  sense.)
* Resolvent decay: for `‖A‖ * ‖(1 : E →L[ℂ] E)‖ < ‖lam‖`,
  `lam` lies in `resolventSet ℂ A`, and
  `resolvent A → 0` along `Bornology.cobounded ℂ`: the
  `O(|lam|⁻¹)` decay at infinity, in all directions —
  the bounded seat's sectorial exterior estimate.

## The seam (pre-named PARTIAL)

PARTIAL at the unbounded sectorial theory. NOT proved
here, and not silently replaced by the bounded seat:
sectorial operators proper (unbounded, densely defined,
with resolvent bounds in a sector), fractional powers of
such operators, and maximal regularity. The missing pin
API, named exactly: there is no `sectorial` definition
or sectorial resolvent-estimate lemma, no analytic /
holomorphic semigroup definition for unbounded
generators, and no operator fractional-power (`cpow` /
`rpow` for operators) API in Mathlib v4.35.0-rc3; and in
the corpus, SHELF-1a's generator dialect (`HasGen`,
`genDom`) is real-scalar only, so there is no complex
unbounded-generator vocabulary to state the unbounded
theory in. General analysis fill only: moves no dial,
closes no posted question. NO CLAIM on its face.
-/

import ThetLogos.SemigroupCore
import ThetLogos.SemigroupGeneration
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace ThetLogos

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-! ## 1. The complex-time exponential at the bounded seat -/

/-- The holomorphic extension of the bounded-generator
semigroup to complex time: for a bounded operator `A` on
a complex Banach space, `cexpSemigroup A z` is
`NormedSpace.exp (z • A)` in the Banach algebra
`E →L[ℂ] E`. At real times this is the complex analogue
of SHELF-1a's `expSemigroup`. -/
noncomputable def cexpSemigroup (A : E →L[ℂ] E) (z : ℂ) :
    E →L[ℂ] E :=
  NormedSpace.exp (z • A)

theorem cexpSemigroup_zero (A : E →L[ℂ] E) :
    cexpSemigroup A 0 = 1 := by
  simp [cexpSemigroup, NormedSpace.exp_zero]

theorem cexpSemigroup_apply_zero (A : E →L[ℂ] E) (x : E) :
    cexpSemigroup A 0 x = x := by
  rw [cexpSemigroup_zero]; rfl

/-- The group law in complex time: for ALL `z w : ℂ`
(no sign or sector restriction at the bounded seat),
`cexpSemigroup A (z + w)` is the composition of the two
factors. -/
theorem cexpSemigroup_add (A : E →L[ℂ] E) (z w : ℂ) :
    cexpSemigroup A (z + w)
      = (cexpSemigroup A z).comp (cexpSemigroup A w) := by
  letI : NormedAlgebra ℚ (E →L[ℂ] E) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have h : NormedSpace.exp ((z + w) • A)
      = NormedSpace.exp (z • A) * NormedSpace.exp (w • A) := by
    rw [add_smul, NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left z).smul_right w)]
  rw [cexpSemigroup, cexpSemigroup, cexpSemigroup, h]
  rfl

theorem cexpSemigroup_add_apply (A : E →L[ℂ] E) (z w : ℂ)
    (x : E) :
    cexpSemigroup A (z + w) x
      = cexpSemigroup A z (cexpSemigroup A w x) := by
  rw [cexpSemigroup_add]; rfl

/-- Two-sided inverse in complex time:
`cexpSemigroup A (-z)` undoes `cexpSemigroup A z`. -/
theorem cexpSemigroup_neg_comp (A : E →L[ℂ] E) (z : ℂ) :
    (cexpSemigroup A (-z)).comp (cexpSemigroup A z) = 1 := by
  rw [← cexpSemigroup_add, neg_add_cancel, cexpSemigroup_zero]

theorem cexpSemigroup_comp_neg (A : E →L[ℂ] E) (z : ℂ) :
    (cexpSemigroup A z).comp (cexpSemigroup A (-z)) = 1 := by
  rw [← cexpSemigroup_add, add_neg_cancel, cexpSemigroup_zero]

/-- Smoothing read-back, surjectivity form: at the bounded
seat every vector is in the range of `cexpSemigroup A z`
(the range is all of `E`, since the inverse is again an
exponential). -/
theorem cexpSemigroup_surjective (A : E →L[ℂ] E) (z : ℂ) :
    Function.Surjective (cexpSemigroup A z) := by
  intro x
  refine ⟨cexpSemigroup A (-z) x, ?_⟩
  have h := ContinuousLinearMap.ext_iff.mp
    (cexpSemigroup_comp_neg A z) x
  simpa using h

/-! ## 2. Growth bound: `‖exp (z • A)‖ ≤ exp (‖z‖ ‖A‖)` -/

theorem cexp_norm_one_le : ‖(1 : E →L[ℂ] E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simp)

theorem cexp_norm_pow_le (X : E →L[ℂ] E) (n : ℕ) :
    ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  cases n with
  | zero => simpa using cexp_norm_one_le (E := E)
  | succ k => exact norm_pow_le' X (Nat.succ_pos k)

/-- The Banach-algebra exponential bound over `ℂ`, from
the defining series (the complex analogue of SHELF-1b's
`norm_exp_le`). -/
theorem cexp_norm_exp_le (X : E →L[ℂ] E) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have h1 : NormedSpace.exp X
      = ∑' n : ℕ, ((Nat.factorial n : ℂ))⁻¹ • X ^ n :=
    congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ)) X
  rw [h1]
  calc ‖∑' n : ℕ, ((Nat.factorial n : ℂ))⁻¹ • X ^ n‖
      ≤ ∑' n : ℕ, ‖((Nat.factorial n : ℂ))⁻¹ • X ^ n‖ :=
        norm_tsum_le_tsum_norm
          (NormedSpace.norm_expSeries_summable' X)
    _ ≤ ∑' n : ℕ, ‖X‖ ^ n / (Nat.factorial n : ℝ) :=
        (NormedSpace.norm_expSeries_summable' X).tsum_le_tsum
          (fun n => by
            calc ‖((Nat.factorial n : ℂ))⁻¹ • X ^ n‖
                = ((Nat.factorial n : ℝ))⁻¹ * ‖X ^ n‖ := by
                  rw [norm_smul, norm_inv,
                    Complex.norm_natCast]
              _ ≤ ((Nat.factorial n : ℝ))⁻¹ * ‖X‖ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (cexp_norm_pow_le X n) (by positivity)
              _ = ‖X‖ ^ n / (Nat.factorial n : ℝ) := by
                  rw [div_eq_mul_inv, mul_comm])
          (Real.summable_pow_div_factorial ‖X‖)
    _ = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • ‖X‖ ^ n := by
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    _ = Real.exp ‖X‖ := by
        rw [← congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ))
          ‖X‖]
        exact (congrFun Real.exp_eq_exp_ℝ ‖X‖).symm

/-- The growth bound in complex time, in EVERY direction
(the bounded seat has no sector restriction):
`‖cexpSemigroup A z‖ ≤ Real.exp (‖z‖ * ‖A‖)`. -/
theorem cexpSemigroup_opNorm_le (A : E →L[ℂ] E) (z : ℂ) :
    ‖cexpSemigroup A z‖ ≤ Real.exp (‖z‖ * ‖A‖) := by
  refine le_trans (cexp_norm_exp_le (z • A)) ?_
  apply Real.exp_le_exp.mpr
  rw [norm_smul]

/-! ## 3. Holomorphicity: derivative in complex time -/

/-- The derivative of the operator-valued extension:
`d/dz exp (z • A) = exp (z • A) * A` (operator product). -/
theorem hasDerivAt_cexpSemigroup (A : E →L[ℂ] E) (z : ℂ) :
    HasDerivAt (fun u : ℂ => cexpSemigroup A u)
      (cexpSemigroup A z * A) z :=
  hasDerivAt_exp_smul_const A z

/-- The derivative in the other order:
`d/dz exp (z • A) = A * exp (z • A)`. -/
theorem hasDerivAt_cexpSemigroup' (A : E →L[ℂ] E) (z : ℂ) :
    HasDerivAt (fun u : ℂ => cexpSemigroup A u)
      (A * cexpSemigroup A z) z :=
  hasDerivAt_exp_smul_const' A z

/-- The extension is holomorphic on all of `ℂ`
(differentiable at every complex time). -/
theorem differentiable_cexpSemigroup (A : E →L[ℂ] E) :
    Differentiable ℂ (fun u : ℂ => cexpSemigroup A u) :=
  fun z => (hasDerivAt_cexpSemigroup A z).differentiableAt

/-- The extension is analytic at every complex time. -/
theorem analyticAt_cexpSemigroup (A : E →L[ℂ] E) (z : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => cexpSemigroup A u) z := by
  have hexp : AnalyticAt ℂ NormedSpace.exp (z • A) :=
    NormedSpace.exp_analytic (𝕂 := ℂ) _
  have hsmul : AnalyticAt ℂ (fun u : ℂ => u • A) z :=
    analyticAt_id.smul analyticAt_const
  exact hexp.comp (f := fun u : ℂ => u • A) hsmul

/-- The generator commutes with its complex-time
exponential: `A (exp (zA) x) = exp (zA) (A x)`. -/
theorem cexpSemigroup_commute_apply (A : E →L[ℂ] E) (z : ℂ)
    (x : E) :
    A (cexpSemigroup A z x) = cexpSemigroup A z (A x) := by
  have hcomm : Commute A (NormedSpace.exp (z • A)) :=
    ((Commute.refl A).smul_right z).exp_right
  have h := congrFun (congrArg DFunLike.coe hcomm.eq) x
  simpa [cexpSemigroup, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply] using h

/-- Smoothing read-back, orbit form: every orbit is
holomorphic in complex time, with derivative the
generator applied to the value — for EVERY `x : E`
(at the bounded seat the domain is all of `E`). -/
theorem hasDerivAt_cexpSemigroup_apply (A : E →L[ℂ] E)
    (z : ℂ) (x : E) :
    HasDerivAt (fun u : ℂ => cexpSemigroup A u x)
      (cexpSemigroup A z (A x)) z := by
  have h := (hasDerivAt_cexpSemigroup A z).clm_apply
    (hasDerivAt_const z x)
  have hval : (cexpSemigroup A z * A) x
      = cexpSemigroup A z (A x) := rfl
  rw [hval] at h
  simpa using h

theorem differentiable_cexpSemigroup_apply (A : E →L[ℂ] E)
    (x : E) :
    Differentiable ℂ (fun u : ℂ => cexpSemigroup A u x) :=
  fun z => (hasDerivAt_cexpSemigroup_apply A z x).differentiableAt

/-! ## 4. Real-axis read-backs -/

/-- Restriction to real times recovers the semigroup law
on the real axis (the cast of SHELF-1a's `map_add` at the
complex bounded seat). -/
theorem cexpSemigroup_real_add (A : E →L[ℂ] E) (s t : ℝ) :
    cexpSemigroup A ((s + t : ℝ) : ℂ)
      = (cexpSemigroup A (s : ℂ)).comp (cexpSemigroup A (t : ℂ)) := by
  rw [Complex.ofReal_add]
  exact cexpSemigroup_add A (s : ℂ) (t : ℂ)

/-- On the positive real axis, the growth bound reads
`‖cexpSemigroup A t‖ ≤ Real.exp (t * ‖A‖)`. -/
theorem cexpSemigroup_real_opNorm_le (A : E →L[ℂ] E)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖cexpSemigroup A (t : ℂ)‖ ≤ Real.exp (t * ‖A‖) := by
  have h := cexpSemigroup_opNorm_le A (t : ℂ)
  rwa [Complex.norm_real, Real.norm_of_nonneg ht] at h

/-! ## 5. Resolvent / sector read-backs -/

/-- Exterior resolvent membership: if
`‖A‖ * ‖(1 : E →L[ℂ] E)‖ < ‖lam‖` then `lam` is in the
resolvent set of the bounded operator `A` (the pin's
`spectrum.mem_resolventSet_of_norm_lt_mul`, read back at
this seat). -/
theorem cexp_mem_resolventSet (A : E →L[ℂ] E) {lam : ℂ}
    (h : ‖A‖ * ‖(1 : E →L[ℂ] E)‖ < ‖lam‖) :
    lam ∈ resolventSet ℂ A :=
  spectrum.mem_resolventSet_of_norm_lt_mul h

/-- Exterior resolvent membership from `‖A‖ < ‖lam‖`
alone, using `‖(1 : E →L[ℂ] E)‖ ≤ 1`. -/
theorem cexp_mem_resolventSet_of_norm_lt (A : E →L[ℂ] E)
    {lam : ℂ} (h : ‖A‖ < ‖lam‖) :
    lam ∈ resolventSet ℂ A := by
  apply cexp_mem_resolventSet A
  calc ‖A‖ * ‖(1 : E →L[ℂ] E)‖
      ≤ ‖A‖ * 1 :=
        mul_le_mul_of_nonneg_left cexp_norm_one_le (norm_nonneg _)
    _ = ‖A‖ := mul_one _
    _ < ‖lam‖ := h

/-- Resolvent decay at infinity, in all directions (the
bounded seat's sectorial exterior decay):
`resolvent A → 0` along `Bornology.cobounded ℂ`, i.e.
`resolvent A lam = O(|lam|⁻¹)` in the pin's
`spectrum.resolvent_isBigO_inv` form, restated as a
limit. -/
theorem cexp_resolvent_tendsto_cobounded (A : E →L[ℂ] E) :
    Tendsto (resolvent A) (Bornology.cobounded ℂ) (𝓝 0) :=
  spectrum.resolvent_tendsto_cobounded A

end ThetLogos
