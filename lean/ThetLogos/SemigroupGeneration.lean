/-
# SHELF-1b - generation theorems (working label)

Brick SHELF-1b of the SHELF line: the Lumer-Phillips
theorem (contraction case) and the contraction case of
Hille-Yosida, built against SHELF-1a's landed
`SemigroupCore.lean` (read-only; its `C0Semigroup`
structure, generator dialect `HasGen` / `genDom` /
`genVal`, algebraic resolvent specification
`ResolventSpec`, and Yosida approximants are consumed,
not modified). NO CLAIM beyond the theorems below.

## Hypothesis form chosen for dissipativity (on the face)

`A` is a densely defined operator in 1a's dialect: a
submodule `D` (the domain) and a linear map
`A : D ->l[R] E`. Dissipativity is taken in the
resolvent-bound form (`DissBound`):
`lam * ||x|| <= ||lam • x - A x||` for all `lam > 0` and
`x : D`. This is the classical equivalent of the
duality-pairing form of dissipativity, and it is the
form the proof consumes; the pairing form itself is not
separately formalized (the pin's duality-pairing support
is thin), exactly as the pack permits.

## The hlim consumption, exactly as it went

1a's `yosidaApprox_tendsto` is stated for the generator
of an already-existing semigroup (its `ResolventSpec` is
relative to that semigroup), so it cannot be instantiated
before generation. What this module does instead: it
proves the identical on-domain convergence for the
abstract `A`, and it DISCHARGES the `hlim` hypothesis
(`lam • R(lam) z -> z` for all `z : E`) from density of
`D` + the contraction bound `||R(lam)|| <= lam^-1` + the
on-domain algebra - the route 1a's section 5b header
describes (`resolvent_tendsto_on_dom` is the on-domain
half, proved here for the abstract operator).

## Which of 1a's named remainders this brick discharges

For the Lumer-Phillips class (densely defined,
resolvent-bound-dissipative, with the range condition at
one `lam0 > 0`):
* generator closedness and density: DISCHARGED for this
  class - the constructed semigroup's `genDom` equals
  `D` (hence is dense), and `A` is sequentially
  graph-closed (`lpClosedGraph`).
* `exp(t A_lam) x -> T t x`: DISCHARGED for this class
  (`lpYosidaApprox_exp_tendsto`, pointwise in `x` for
  every `t >= 0`; the underlying convergence of the
  approximant semigroups is uniform on compact time
  intervals, `lpOp_tendsto_uniform_on_Icc`).
* the resolvent integral formula
  `R(lam) x = int_0^infty e^{-lam t} T t x dt`: NOT
  discharged - it remains a named remainder, verbatim.
  What is proved is the algebraic half: the constructed
  resolvent family satisfies 1a's `ResolventSpec` for the
  constructed semigroup at every `lam > 0`
  (`lpSemigroup_resolventSpec`).

## Seams (pre-named in the pack)

* Seam LP-only: Lumer-Phillips FULL and the contraction
  case of Hille-Yosida both land in this module, so this
  seam does not bite. The general-`M` Hille-Yosida
  (quasi-contractive, renorming) case is a named
  remainder, verbatim: for general `M >= 1`, the
  implication from `||(lam - A)^{-n}|| <= M lam^{-n}`
  for all `lam > 0` and all `n` to the generation of a
  semigroup with `||T t|| <= M` is NOT proved in this
  module.
* Seam GEN-ID: does not bite - generator identification
  is proved (`lpSemigroup_hasGen` on the domain, and
  `lpSemigroup_genDom_eq` by the range-condition closing
  argument).
* Seam CONV: does not bite - convergence is proved on
  all of `E`, not only on the domain
  (`yosida_exp_tendsto_lpClass`).

## Fences

General analysis fill only (the SHELF map, section 6):
moves no dial (0/4), closes no posted question, proves
no corpus claim. NO CLAIM on its face.
-/

import ThetLogos.SemigroupCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ThetLogos

open Filter Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-! ## 1. Abstract densely defined operators and their
resolvents -/

/-- `lam - A` as a linear map on the domain `D`. -/
def lamSub (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) (lam : ℝ) :
    D →ₗ[ℝ] E :=
  lam • D.subtype - A

theorem lamSub_apply (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (lam : ℝ) (x : D) :
    lamSub D A lam x = lam • (x : E) - A x := by
  simp [lamSub]

/-- Dissipativity in the resolvent-bound hypothesis form
(see the header): `lam * ||x|| <= ||(lam - A) x||` for
all `lam > 0`, `x : D`. -/
def DissBound (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ x : D,
    lam * ‖(x : E)‖ ≤ ‖lam • (x : E) - A x‖

/-- Under the resolvent bound, `lam - A` is injective for
every `lam > 0`. -/
theorem lamSub_injective (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hd : DissBound D A) {lam : ℝ} (hlam : 0 < lam) :
    Function.Injective (lamSub D A lam) := by
  intro x y hxy
  have h0 : lamSub D A lam (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hb := hd lam hlam (x - y)
  rw [← lamSub_apply] at hb
  rw [h0, norm_zero] at hb
  have hle : ‖((x - y : D) : E)‖ ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using hb) hlam
  have hE : ((x - y : D) : E) = 0 := norm_le_zero_iff.mp hle
  have hD : x - y = 0 := by
    apply Subtype.ext
    simpa using hE
  exact sub_eq_zero.mp hD

/-- The two-sided inverse relations for a candidate
resolvent `R` of `A` at `lam` (the abstract analogue of
1a's `ResolventSpec`). -/
def HasResolventAt (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (lam : ℝ) (R : E →L[ℝ] E) : Prop :=
  (∀ x : D, R (lamSub D A lam x) = (x : E)) ∧
  (∀ y : E, ∃ h : R y ∈ D, lamSub D A lam ⟨R y, h⟩ = y)

/-- The inverse of `lam - A` as a linear map, from
bijectivity (injectivity from `DissBound`, surjectivity
assumed). -/
noncomputable def resolventLin (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) :
    E →ₗ[ℝ] E :=
  D.subtype.comp
    (LinearEquiv.ofBijective (lamSub D A lam)
      ⟨lamSub_injective D A hd hlam, hsurj⟩).symm.toLinearMap

theorem resolventLin_apply (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) (y : E) :
    resolventLin D A hd hlam hsurj y
      = (((LinearEquiv.ofBijective (lamSub D A lam)
        ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y : D) : E) :=
  rfl

theorem lamSub_resolventLin (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) (y : E) :
    lamSub D A lam
      ((LinearEquiv.ofBijective (lamSub D A lam)
        ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y) = y := by
  have h := LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective (lamSub D A lam)
      ⟨lamSub_injective D A hd hlam, hsurj⟩) y
  exact h

theorem resolventLin_apply_le (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) (y : E) :
    ‖resolventLin D A hd hlam hsurj y‖ ≤ lam⁻¹ * ‖y‖ := by
  set e := (LinearEquiv.ofBijective (lamSub D A lam)
    ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y with he
  have hb := hd lam hlam e
  rw [← lamSub_apply, lamSub_resolventLin D A hd hlam hsurj] at hb
  rw [resolventLin_apply]
  calc ‖(e : E)‖ = lam⁻¹ * (lam * ‖(e : E)‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
    _ ≤ lam⁻¹ * ‖y‖ :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hlam.le)

/-- The resolvent of `A` at `lam`, as a bounded operator,
from bijectivity of `lam - A`. -/
noncomputable def resolventOf (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) :
    E →L[ℝ] E :=
  (resolventLin D A hd hlam hsurj).mkContinuous lam⁻¹
    (resolventLin_apply_le D A hd hlam hsurj)

theorem resolventOf_apply (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) (y : E) :
    resolventOf D A hd hlam hsurj y
      = resolventLin D A hd hlam hsurj y :=
  rfl

theorem resolventOf_hasResolventAt (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) :
    HasResolventAt D A lam (resolventOf D A hd hlam hsurj) := by
  constructor
  · intro x
    rw [resolventOf_apply, resolventLin_apply]
    have h := LinearEquiv.symm_apply_apply
      (LinearEquiv.ofBijective (lamSub D A lam)
        ⟨lamSub_injective D A hd hlam, hsurj⟩) x
    exact congrArg (fun z : D => (z : E)) h
  · intro y
    rw [resolventOf_apply, resolventLin_apply]
    refine ⟨?_, ?_⟩
    · exact ((LinearEquiv.ofBijective (lamSub D A lam)
        ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y).prop
    · have h2 : (⟨(((LinearEquiv.ofBijective (lamSub D A lam)
          ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y : D) : E),
          ((LinearEquiv.ofBijective (lamSub D A lam)
          ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y).prop⟩ : D)
          = (LinearEquiv.ofBijective (lamSub D A lam)
            ⟨lamSub_injective D A hd hlam, hsurj⟩).symm y :=
        Subtype.ext rfl
      rw [h2]
      exact lamSub_resolventLin D A hd hlam hsurj y

theorem resolventOf_opNorm_le (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam)
    (hsurj : Function.Surjective (lamSub D A lam)) :
    ‖resolventOf D A hd hlam hsurj‖ ≤ lam⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hlam.le)
    (fun y => by
      rw [resolventOf_apply]
      exact resolventLin_apply_le D A hd hlam hsurj y)

/-- Any resolvent (in the two-sided sense) of a
resolvent-bound-dissipative operator satisfies the
contraction bound `||R|| <= lam^-1`. -/
theorem opNorm_le_of_hasResolventAt (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam : ℝ}
    (hlam : 0 < lam) {R : E →L[ℝ] E}
    (hR : HasResolventAt D A lam R) :
    ‖R‖ ≤ lam⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr hlam.le)
  intro y
  obtain ⟨h, hh⟩ := hR.2 y
  have hb := hd lam hlam ⟨R y, h⟩
  rw [← lamSub_apply, hh] at hb
  calc ‖R y‖ = ‖((⟨R y, h⟩ : D) : E)‖ := rfl
    _ ≤ lam⁻¹ * ‖y‖ := by
      have h2 : lam * ‖R y‖ ≤ ‖y‖ := hb
      calc ‖R y‖ = lam⁻¹ * (lam * ‖R y‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
        _ ≤ lam⁻¹ * ‖y‖ :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam.le)

/-- Propagation of the range condition, one step: if
`lam - A` is surjective and `|mu - lam| < lam`, then
`mu - A` is surjective. Banach fixed-point on
`w |-> R_lam (y + (lam - mu) • w)`. -/
theorem lamSub_surjective_step (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam mu : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu)
    (hsurj : Function.Surjective (lamSub D A lam))
    (hclose : |mu - lam| < lam) :
    Function.Surjective (lamSub D A mu) := by
  intro y
  set R := resolventOf D A hd hlam hsurj with hRdef
  set Φ : E → E := fun w => R (y + (lam - mu) • w) with hΦdef
  have hRbd : ‖R‖ ≤ lam⁻¹ := resolventOf_opNorm_le D A hd hlam hsurj
  have hspec : HasResolventAt D A lam R :=
    resolventOf_hasResolventAt D A hd hlam hsurj
  have hdist : ∀ a b : E, dist (Φ a) (Φ b)
      ≤ (|lam - mu| / lam) * dist a b := by
    intro a b
    have hsub : Φ a - Φ b = R ((lam - mu) • (a - b)) := by
      simp only [hΦdef]
      rw [← map_sub]
      congr 1
      rw [add_sub_add_left_eq_sub, smul_sub]
    rw [dist_eq_norm, hsub]
    calc ‖R ((lam - mu) • (a - b))‖
        ≤ ‖R‖ * ‖(lam - mu) • (a - b)‖ := R.le_opNorm _
      _ = ‖R‖ * (|lam - mu| * ‖a - b‖) :=
        congrArg _ (norm_smul _ _)
      _ ≤ lam⁻¹ * (|lam - mu| * ‖a - b‖) :=
        mul_le_mul_of_nonneg_right hRbd
          (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = (|lam - mu| / lam) * ‖a - b‖ := by
        rw [div_eq_mul_inv]; ring
      _ = (|lam - mu| / lam) * dist a b := by rw [dist_eq_norm]
  have hKnn : (0 : ℝ) ≤ |lam - mu| / lam :=
    div_nonneg (abs_nonneg _) hlam.le
  have hK1 : (⟨|lam - mu| / lam, hKnn⟩ : ℝ≥0) < 1 := by
    have h2 : (|lam - mu| / lam : ℝ) < 1 := by
      rw [abs_sub_comm] at hclose
      exact (div_lt_one hlam).mpr hclose
    exact h2
  have hcontr : ContractingWith
      (⟨|lam - mu| / lam, hKnn⟩ : ℝ≥0) Φ :=
    ⟨hK1, LipschitzWith.of_dist_le_mul (fun a b => by
      show dist (Φ a) (Φ b) ≤ (|lam - mu| / lam) * dist a b
      exact hdist a b)⟩
  obtain ⟨w, hwfix, -, -⟩ := hcontr.exists_fixedPoint 0
    (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  have hwmem : w ∈ D := by
    have h2 : Φ w ∈ D := by
      obtain ⟨h, -⟩ := hspec.2 (y + (lam - mu) • w)
      have h3 : R (y + (lam - mu) • w) = Φ w := rfl
      rwa [h3] at h
    rwa [hwfix] at h2
  refine ⟨⟨w, hwmem⟩, ?_⟩
  have hlamw : lamSub D A lam ⟨w, hwmem⟩ = y + (lam - mu) • w := by
    obtain ⟨h, hh⟩ := hspec.2 (y + (lam - mu) • w)
    have h3 : (⟨R (y + (lam - mu) • w), h⟩ : D) = ⟨w, hwmem⟩ := by
      apply Subtype.ext
      show R (y + (lam - mu) • w) = w
      have h4 : Φ w = R (y + (lam - mu) • w) := rfl
      rw [← h4]; exact hwfix
    rwa [h3] at hh
  rw [lamSub_apply] at hlamw ⊢
  have hA : A ⟨w, hwmem⟩ = lam • w - (y + (lam - mu) • w) := by
    rw [← hlamw]; abel
  rw [hA]
  have : mu • w - (lam • w - (y + (lam - mu) • w)) = y := by
    rw [sub_smul]; abel
  exact this

/-- Propagation of the range condition, all the way:
surjectivity at one `lam0 > 0` gives surjectivity at
every `lam > 0` (steps of ratio `3/2`, by induction). -/
theorem lamSub_surjective_all (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0)) :
    ∀ {lam : ℝ}, 0 < lam →
      Function.Surjective (lamSub D A lam) := by
  intro lam hlam
  obtain ⟨n, hn⟩ : ∃ n : ℕ, lam ≤ lam0 * (3 / 2) ^ n := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 3 / 2 by norm_num)).eventually_ge_atTop
      (lam / lam0)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ht
    refine ⟨N, ?_⟩
    have h2 := hN N le_rfl
    have h3 := (div_le_iff₀ hlam0).mp h2
    rwa [mul_comm] at h3
  have key : ∀ n : ℕ, ∀ mu : ℝ, 0 < mu →
      mu ≤ lam0 * (3 / 2) ^ n →
      Function.Surjective (lamSub D A mu) := by
    intro n
    induction n with
    | zero =>
      intro mu hmu hle
      simp only [pow_zero, mul_one] at hle
      apply lamSub_surjective_step D A hd hlam0 hmu hsurj0
      have h1 : |mu - lam0| = lam0 - mu := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      rw [h1]; linarith
    | succ n ih =>
      intro mu hmu hle
      by_cases h : mu ≤ lam0 * (3 / 2) ^ n
      · exact ih mu hmu h
      · have hmu' : (0 : ℝ) < (2 / 3) * mu :=
          mul_pos (by norm_num) hmu
        have hle' : (2 / 3) * mu ≤ lam0 * (3 / 2) ^ n := by
          calc (2 / 3) * mu ≤ (2 / 3) * (lam0 * (3 / 2) ^ (n + 1)) :=
              mul_le_mul_of_nonneg_left hle (by norm_num)
            _ = lam0 * (3 / 2) ^ n := by
              rw [pow_succ]; ring
        have hs' := ih ((2 / 3) * mu) hmu' hle'
        apply lamSub_surjective_step D A hd hmu' hmu hs'
        have h1 : |mu - (2 / 3) * mu| = (1 / 3) * mu := by
          rw [show mu - (2 / 3) * mu = (1 / 3) * mu by ring,
            abs_of_pos (mul_pos (by norm_num) hmu)]
        rw [h1]; linarith
  exact key n lam hlam hn

/-- The resolvent family of `A`, at every real parameter
(the value at `lam <= 0` is `0`, never used). -/
noncomputable def resolventFam (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0)) :
    ℝ → (E →L[ℝ] E) :=
  fun lam => if h : 0 < lam then
    resolventOf D A hd h
      (lamSub_surjective_all D A hd hlam0 hsurj0 h) else 0

theorem resolventFam_hasResolventAt (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0))
    {lam : ℝ} (hlam : 0 < lam) :
    HasResolventAt D A lam
      (resolventFam D A hd hlam0 hsurj0 lam) := by
  rw [resolventFam, dif_pos hlam]
  exact resolventOf_hasResolventAt D A hd hlam _

theorem resolventFam_opNorm_le (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hd : DissBound D A) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0))
    {lam : ℝ} (hlam : 0 < lam) :
    ‖resolventFam D A hd hlam0 hsurj0 lam‖ ≤ lam⁻¹ :=
  opNorm_le_of_hasResolventAt D A hd hlam
    (resolventFam_hasResolventAt D A hd hlam0 hsurj0 hlam)

/-! ## 2. Resolvent identity, commutation, and the strong
convergence `lam • R(lam) -> id` -/

/-- A resolvent in the two-sided sense is unique. -/
theorem hasResolventAt_unique (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) {lam : ℝ} {R₁ R₂ : E →L[ℝ] E}
    (h₁ : HasResolventAt D A lam R₁)
    (h₂ : HasResolventAt D A lam R₂) : R₁ = R₂ := by
  ext y
  obtain ⟨hm, hmeq⟩ := h₂.2 y
  have e := h₁.1 ⟨R₂ y, hm⟩
  rw [hmeq] at e
  exact e

/-- The first resolvent identity for abstract resolvents:
`R(lam) - R(mu) = (mu - lam) • R(lam) ∘L R(mu)`. -/
theorem hasResolventAt_identity (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) {lam mu : ℝ} {Rlam Rmu : E →L[ℝ] E}
    (hlam : HasResolventAt D A lam Rlam)
    (hmu : HasResolventAt D A mu Rmu) :
    Rlam - Rmu = (mu - lam) • Rlam.comp Rmu := by
  ext y
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  obtain ⟨hm, hmeq⟩ := hmu.2 y
  set x : D := ⟨Rmu y, hm⟩ with hxdef
  have e1 := hlam.1 x
  have hA : A x = mu • (x : E) - y := by
    have h2 : mu • (x : E) - A x = y := by
      have h3 := hmeq
      rwa [lamSub_apply] at h3
    rw [← h2]; abel
  have earg : lamSub D A lam x
      = y + (lam - mu) • (x : E) := by
    rw [lamSub_apply, hA, sub_smul]; abel
  rw [earg, map_add, map_smul] at e1
  have hRy : Rlam y = Rmu y - (lam - mu) • Rlam (x : E) :=
    eq_sub_of_add_eq e1
  show Rlam y - Rmu y = (mu - lam) • Rlam (x : E)
  rw [hRy, show (mu - lam) • Rlam (x : E)
      = -((lam - mu) • Rlam (x : E)) by
    rw [← neg_smul, neg_sub]]
  abel

/-- Resolvents at different parameters commute. -/
theorem hasResolventAt_commute (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) {lam mu : ℝ} {Rlam Rmu : E →L[ℝ] E}
    (hlam : HasResolventAt D A lam Rlam)
    (hmu : HasResolventAt D A mu Rmu) (y : E) :
    Rlam (Rmu y) = Rmu (Rlam y) := by
  by_cases h : lam = mu
  · subst h
    rw [hasResolventAt_unique D A hlam hmu]
  · have hne : (mu - lam) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm h)
    have i1 : Rlam y - Rmu y
        = (mu - lam) • Rlam (Rmu y) := by
      have h2 := hasResolventAt_identity D A hlam hmu
      have h3 := congrFun (congrArg DFunLike.coe h2) y
      simpa using h3
    have i2 : Rmu y - Rlam y
        = (lam - mu) • Rmu (Rlam y) := by
      have h2 := hasResolventAt_identity D A hmu hlam
      have h3 := congrFun (congrArg DFunLike.coe h2) y
      simpa using h3
    have key : (mu - lam) • Rlam (Rmu y)
        = (mu - lam) • Rmu (Rlam y) := by
      have e2 : (mu - lam) • Rmu (Rlam y)
          = Rlam y - Rmu y := by
        have h3 : (mu - lam) • Rmu (Rlam y)
            = -((lam - mu) • Rmu (Rlam y)) := by
          rw [← neg_smul, neg_sub]
        rw [h3, ← i2]
        exact neg_sub _ _
      rw [← i1, ← e2]
    calc Rlam (Rmu y)
        = (mu - lam)⁻¹ • ((mu - lam) • Rlam (Rmu y)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (mu - lam)⁻¹ • ((mu - lam) • Rmu (Rlam y)) := by
          rw [key]
      _ = Rmu (Rlam y) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The resolvent applied to a generator value:
`R (A x) = lam • R x - x` on the domain. -/
theorem hasResolventAt_apply_gen (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) {lam : ℝ} {R : E →L[ℝ] E}
    (hR : HasResolventAt D A lam R) (x : D) :
    R (A x) = lam • R (x : E) - (x : E) := by
  have e1 := hR.1 x
  calc R (A x)
      = R (lam • (x : E) - lamSub D A lam x) := by
        congr 1
        rw [lamSub_apply]; abel
    _ = R (lam • (x : E)) - R (lamSub D A lam x) :=
        map_sub _ _ _
    _ = lam • R (x : E) - (x : E) := by rw [map_smul, e1]

/-- On the domain, `lam • R(lam) x -> x`: pure algebra
plus the contraction bound (the abstract analogue of
1a's `resolvent_tendsto_on_dom`). -/
theorem resolvent_smul_tendsto_on_dom
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (R : ℝ → (E →L[ℝ] E))
    (hspec : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    (hbd : ∀ lam : ℝ, 0 < lam → ‖R lam‖ ≤ lam⁻¹)
    {x : D} :
    Tendsto (fun lam : ℝ => lam • R lam (x : E)) atTop
      (𝓝 (x : E)) := by
  have heq : ∀ᶠ lam : ℝ in atTop,
      lam • R lam (x : E) - (x : E) = R lam (A x) := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (hasResolventAt_apply_gen D A (hspec lam hlam) x).symm
  have hnorm : Tendsto (fun lam : ℝ => R lam (A x)) atTop
      (𝓝 0) := by
    have htop : Tendsto
        (fun lam : ℝ => lam⁻¹ * ‖A x‖) atTop (𝓝 0) := by
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
      calc ‖R lam (A x)‖
          ≤ ‖R lam‖ * ‖A x‖ := (R lam).le_opNorm _
        _ ≤ lam⁻¹ * ‖A x‖ :=
            mul_le_mul_of_nonneg_right (hbd lam hlam)
              (norm_nonneg _)
  have hsub : Tendsto
      (fun lam : ℝ => lam • R lam (x : E) - (x : E)) atTop
      (𝓝 0) :=
    (tendsto_congr' heq).mpr hnorm
  have hfin : Tendsto
      (fun lam : ℝ => (lam • R lam (x : E) - (x : E)) + (x : E))
      atTop (𝓝 (0 + (x : E))) :=
    hsub.add tendsto_const_nhds
  simpa using hfin

/-- The `hlim` hypothesis of 1a's section 5b, DISCHARGED
for a densely defined operator with the contraction
bound: `lam • R(lam) z -> z` for every `z : E`, by the
on-domain convergence plus density plus the uniform
bound `||lam • R(lam)|| <= 1`. -/
theorem resolvent_smul_tendsto
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hdense : Dense (↑D : Set E))
    (R : ℝ → (E →L[ℝ] E))
    (hspec : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    (hbd : ∀ lam : ℝ, 0 < lam → ‖R lam‖ ≤ lam⁻¹)
    (z : E) :
    Tendsto (fun lam : ℝ => lam • R lam z) atTop (𝓝 z) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hz : z ∈ closure (↑D : Set E) := hdense z
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hwD, hwz⟩ := hz (ε / 3) (by positivity)
  set wD : D := ⟨w, hwD⟩ with hwDdef
  have hon := resolvent_smul_tendsto_on_dom D A R hspec hbd
    (x := wD)
  rw [Metric.tendsto_atTop] at hon
  obtain ⟨N, hN⟩ := hon (ε / 3) (by positivity)
  refine ⟨max N 1, fun lam hlam => ?_⟩
  have hlam0 : 0 < lam :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hlam)
  have hN' : N ≤ lam := le_trans (le_max_left N 1) hlam
  have hdistw : dist (lam • R lam w) w < ε / 3 := hN lam hN'
  have e1 : dist (lam • R lam z) (lam • R lam w) ≤ ‖z - w‖ := by
    calc dist (lam • R lam z) (lam • R lam w)
        = ‖lam • R lam (z - w)‖ := by
          rw [dist_eq_norm, map_sub, smul_sub]
      _ ≤ ‖lam • R lam‖ * ‖z - w‖ := (lam • R lam).le_opNorm _
      _ ≤ 1 * ‖z - w‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          calc ‖lam • R lam‖ = lam * ‖R lam‖ := by
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_pos hlam0]
            _ ≤ lam * lam⁻¹ :=
                mul_le_mul_of_nonneg_left (hbd lam hlam0)
                  hlam0.le
            _ = 1 := mul_inv_cancel₀ hlam0.ne'
      _ = ‖z - w‖ := one_mul _
  have hzw : ‖z - w‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hwz
  calc dist (lam • R lam z) z
      ≤ dist (lam • R lam z) (lam • R lam w)
        + dist (lam • R lam w) z := dist_triangle _ _ _
    _ ≤ dist (lam • R lam z) (lam • R lam w)
        + (dist (lam • R lam w) w + dist w z) := by
          linarith [dist_triangle (lam • R lam w) w z]
    _ < ε / 3 + (ε / 3 + ε / 3) := by
          apply add_lt_add
          · exact lt_of_le_of_lt e1 hzw
          · apply add_lt_add hdistw
            rw [dist_comm]; exact hwz
    _ = ε := by ring

/-! ## 3. Yosida approximants of the abstract operator -/

/-- The Yosida approximant `A_lam = lam • (lam • R(lam) - 1)`
of the abstract operator (the same formula as 1a's
`yosidaApprox`, which is independent of its semigroup
argument). -/
def yosidaA (R : ℝ → (E →L[ℝ] E)) (lam : ℝ) : E →L[ℝ] E :=
  lam • (lam • R lam - 1)

theorem yosidaA_eq_yosidaApprox (S : C0Semigroup E)
    (R : ℝ → (E →L[ℝ] E)) (lam : ℝ) :
    yosidaA R lam = yosidaApprox S lam (R lam) :=
  rfl

theorem yosidaA_apply (R : ℝ → (E →L[ℝ] E)) (lam : ℝ)
    (y : E) :
    yosidaA R lam y = lam • (lam • R lam y - y) := by
  simp [yosidaA]

/-- On the domain, `A_lam x = lam • R(lam) (A x)`. -/
theorem yosidaA_apply_on_dom
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (R : ℝ → (E →L[ℝ] E))
    (hspec : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    {lam : ℝ} (hlam : 0 < lam) (x : D) :
    yosidaA R lam (x : E) = lam • R lam (A x) := by
  rw [yosidaA_apply,
    hasResolventAt_apply_gen D A (hspec lam hlam) x]

/-- Yosida convergence on the domain for the abstract
operator: `A_lam x -> A x`, consuming the discharged
`hlim` exactly as 1a's `yosidaApprox_tendsto` consumes
its stated hypothesis. -/
theorem yosidaA_tendsto_on_dom
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (R : ℝ → (E →L[ℝ] E))
    (hspec : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    (hlim : ∀ z : E, Tendsto (fun lam : ℝ => lam • R lam z)
      atTop (𝓝 z))
    (x : D) :
    Tendsto (fun lam : ℝ => yosidaA R lam (x : E)) atTop
      (𝓝 (A x)) := by
  apply (tendsto_congr' _).mpr (hlim (A x))
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  exact yosidaA_apply_on_dom D A R hspec hlam x

/-- The product expansion for two Yosida approximants:
with `P = R(lam)`, `Q = R(mu)`,
`A_lam (A_mu y) = (lam*mu)^2 • P (Q y) - lam^2*mu • P y
- lam*mu^2 • Q y + lam*mu • y` as vectors. -/
theorem yosidaA_apply_yosidaA
    (R : ℝ → (E →L[ℝ] E)) (lam mu : ℝ) (y : E) :
    yosidaA R lam (yosidaA R mu y)
      = (lam * mu) ^ 2 • R lam (R mu y)
        - (lam ^ 2 * mu) • R lam y
        - (lam * mu ^ 2) • R mu y
        + (lam * mu) • y := by
  simp only [yosidaA_apply, map_sub, map_smul, smul_sub,
    smul_smul]
  module

/-- Yosida approximants at different parameters commute
(as bounded operators), because the resolvents do. -/
theorem yosidaA_commute
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (R : ℝ → (E →L[ℝ] E))
    (hspec : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) :
    Commute (yosidaA R lam) (yosidaA R mu) := by
  apply ContinuousLinearMap.ext
  intro y
  have hmul : ∀ (P Q : E →L[ℝ] E) (z : E),
      (P * Q) z = P (Q z) := fun P Q z => rfl
  rw [hmul, hmul, yosidaA_apply_yosidaA,
    yosidaA_apply_yosidaA,
    hasResolventAt_commute D A (hspec lam hlam)
      (hspec mu hmu) y]
  module

/-! ## 4. Exponential bounds and the Duhamel estimate -/

theorem norm_one_le_clm : ‖(1 : E →L[ℝ] E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simp)

theorem norm_pow_le_clm (X : E →L[ℝ] E) (n : ℕ) :
    ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  cases n with
  | zero => simpa using norm_one_le_clm (E := E)
  | succ k => exact norm_pow_le' X (Nat.succ_pos k)

/-- The Banach-algebra exponential bound
`||exp X|| <= Real.exp ||X||`, from the defining series. -/
theorem norm_exp_le (X : E →L[ℝ] E) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have h1 : NormedSpace.exp X
      = ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • X ^ n :=
    congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) X
  rw [h1]
  calc ‖∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • X ^ n‖
      ≤ ∑' n : ℕ, ‖((Nat.factorial n : ℝ))⁻¹ • X ^ n‖ :=
        norm_tsum_le_tsum_norm
          (NormedSpace.norm_expSeries_summable' X)
    _ ≤ ∑' n : ℕ, ‖X‖ ^ n / (Nat.factorial n : ℝ) :=
        (NormedSpace.norm_expSeries_summable' X).tsum_le_tsum
          (fun n => by
            calc ‖((Nat.factorial n : ℝ))⁻¹ • X ^ n‖
                = ((Nat.factorial n : ℝ))⁻¹ * ‖X ^ n‖ := by
                  rw [norm_smul, Real.norm_eq_abs,
                    abs_of_nonneg (by positivity)]
              _ ≤ ((Nat.factorial n : ℝ))⁻¹ * ‖X‖ ^ n :=
                  mul_le_mul_of_nonneg_left
                    (norm_pow_le_clm X n) (by positivity)
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

/-- `exp (c • 1) = (Real.exp c) • 1` in the operator
algebra, via `algebraMap`. -/
theorem exp_smul_one (c : ℝ) :
    NormedSpace.exp (c • (1 : E →L[ℝ] E))
      = (Real.exp c) • (1 : E →L[ℝ] E) := by
  have h4 : NormedSpace.exp c = Real.exp c :=
    (congrFun Real.exp_eq_exp_ℝ c).symm
  rw [← Algebra.algebraMap_eq_smul_one c,
    ← NormedSpace.algebraMap_exp_comm, h4,
    Algebra.algebraMap_eq_smul_one]

theorem norm_exp_smul_one_le (c : ℝ) :
    ‖NormedSpace.exp (c • (1 : E →L[ℝ] E))‖
      ≤ Real.exp c := by
  rw [exp_smul_one, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos c)]
  calc Real.exp c * ‖(1 : E →L[ℝ] E)‖
      ≤ Real.exp c * 1 :=
        mul_le_mul_of_nonneg_left norm_one_le_clm
          (Real.exp_pos c).le
    _ = Real.exp c := mul_one _

/-- The exponential of a Yosida approximant is a
contraction: `exp (t A_lam) = exp (t lam^2 R_lam) *
exp (-(t lam) • 1)`, and the two factors have norms at
most `Real.exp (t lam)` and `Real.exp (-(t lam))`. -/
theorem exp_yosidaA_opNorm_le
    (R : ℝ → (E →L[ℝ] E))
    (hbd : ∀ lam : ℝ, 0 < lam → ‖R lam‖ ≤ lam⁻¹)
    {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • yosidaA R lam)‖ ≤ 1 := by
  have hdecomp : t • yosidaA R lam
      = (t * lam ^ 2) • R lam
        + (-(t * lam)) • (1 : E →L[ℝ] E) := by
    show t • (lam • (lam • R lam - 1)) = _
    module
  have hcomm : Commute ((t * lam ^ 2) • R lam)
      ((-(t * lam)) • (1 : E →L[ℝ] E)) := by
    have e1 : ((t * lam ^ 2) • R lam)
        * ((-(t * lam)) • (1 : E →L[ℝ] E))
        = (-(t * lam)) • ((t * lam ^ 2) • R lam) := by
      rw [Algebra.mul_smul_comm, mul_one]
    have e2 : ((-(t * lam)) • (1 : E →L[ℝ] E))
        * ((t * lam ^ 2) • R lam)
        = (-(t * lam)) • ((t * lam ^ 2) • R lam) := by
      rw [Algebra.smul_mul_assoc, one_mul]
    exact e1.trans e2.symm
  have hexp : NormedSpace.exp (t • yosidaA R lam)
      = NormedSpace.exp ((t * lam ^ 2) • R lam)
        * NormedSpace.exp
          ((-(t * lam)) • (1 : E →L[ℝ] E)) := by
    letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    rw [hdecomp, NormedSpace.exp_add_of_commute hcomm]
  rw [hexp]
  calc ‖NormedSpace.exp ((t * lam ^ 2) • R lam)
        * NormedSpace.exp
          ((-(t * lam)) • (1 : E →L[ℝ] E))‖
      ≤ ‖NormedSpace.exp ((t * lam ^ 2) • R lam)‖
        * ‖NormedSpace.exp
          ((-(t * lam)) • (1 : E →L[ℝ] E))‖ :=
        norm_mul_le _ _
    _ ≤ Real.exp (t * lam) * Real.exp (-(t * lam)) := by
        apply mul_le_mul _ (norm_exp_smul_one_le _)
          (norm_nonneg _) (Real.exp_pos _).le
        refine le_trans (norm_exp_le _)
          (Real.exp_le_exp.mpr ?_)
        calc ‖(t * lam ^ 2) • R lam‖
            = (t * lam ^ 2) * ‖R lam‖ := by
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg
                  (mul_nonneg ht (pow_nonneg hlam.le 2))]
          _ ≤ (t * lam ^ 2) * lam⁻¹ :=
              mul_le_mul_of_nonneg_left (hbd lam hlam)
                (mul_nonneg ht (pow_nonneg hlam.le 2))
          _ = t * lam := by
              have hne : lam ≠ 0 := hlam.ne'
              field_simp
    _ = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The Duhamel estimate: for commuting bounded `P, Q`
whose exponentials are contractions,
`||exp (tP) x - exp (tQ) x|| <= t * ||(P - Q) x||`.
Proof: differentiate
`s |-> exp (sP) (exp ((t-s) Q) x)` and integrate. -/
theorem duhamel_estimate (P Q : E →L[ℝ] E)
    (hPQ : Commute P Q)
    (hP : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • P)‖ ≤ 1)
    (hQ : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • Q)‖ ≤ 1)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • P) x
        - NormedSpace.exp (t • Q) x‖
      ≤ t * ‖(P - Q) x‖ := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  set F : ℝ → E := fun s => NormedSpace.exp (s • P)
    (NormedSpace.exp ((t - s) • Q) x) with hFdef
  set F' : ℝ → E := fun s => NormedSpace.exp (s • P)
    (NormedSpace.exp ((t - s) • Q) ((P - Q) x)) with hF'def
  have hderiv : ∀ s : ℝ, HasDerivAt F (F' s) s := by
    intro s
    have hc : HasDerivAt
        (fun u : ℝ => NormedSpace.exp (u • P))
        (NormedSpace.exp (s • P) * P) s :=
      hasDerivAt_exp_smul_const P s
    have hu : HasDerivAt
        (fun s : ℝ => NormedSpace.exp ((t - s) • Q) x)
        (-(NormedSpace.exp ((t - s) • Q) * Q) x) s := by
      have hg : HasDerivAt
          (fun v : ℝ => NormedSpace.exp (v • Q))
          (NormedSpace.exp ((t - s) • Q) * Q) (t - s) :=
        hasDerivAt_exp_smul_const Q (t - s)
      have hh : HasDerivAt (fun s : ℝ => t - s) (-1) s :=
        (hasDerivAt_id s).const_sub t
      have hcomp := hg.scomp s hh
      have happ := hcomp.clm_apply (hasDerivAt_const s x)
      simpa using happ
    have hsum := hc.clm_apply hu
    have hcomm1 : Commute P ((t - s) • Q) := by
      have hc1 : Commute P
          (algebraMap ℝ (E →L[ℝ] E) (t - s)) :=
        (Algebra.commutes (t - s) P).symm
      rw [Algebra.smul_def]
      exact hc1.mul_right hPQ
    have hPexp : P (NormedSpace.exp ((t - s) • Q) x)
        = NormedSpace.exp ((t - s) • Q) (P x) := by
      have h2 : Commute P
          (NormedSpace.exp ((t - s) • Q)) :=
        hcomm1.exp_right
      have h3 := congrFun (congrArg DFunLike.coe h2.eq) x
      exact h3
    have hid : (NormedSpace.exp (s • P) * P)
          (NormedSpace.exp ((t - s) • Q) x)
        + NormedSpace.exp (s • P)
          (-(NormedSpace.exp ((t - s) • Q) * Q) x)
        = F' s := by
      rw [hF'def]
      show (NormedSpace.exp (s • P) * P)
            (NormedSpace.exp ((t - s) • Q) x)
          + NormedSpace.exp (s • P)
            (-(NormedSpace.exp ((t - s) • Q) * Q) x)
        = NormedSpace.exp (s • P)
            (NormedSpace.exp ((t - s) • Q) ((P - Q) x))
      have step1 : (NormedSpace.exp (s • P) * P)
            (NormedSpace.exp ((t - s) • Q) x)
          = NormedSpace.exp (s • P)
            (NormedSpace.exp ((t - s) • Q) (P x)) := by
        show NormedSpace.exp (s • P)
          (P (NormedSpace.exp ((t - s) • Q) x)) = _
        rw [hPexp]
      have step2 : NormedSpace.exp (s • P)
            (-(NormedSpace.exp ((t - s) • Q) * Q) x)
          = - NormedSpace.exp (s • P)
            (NormedSpace.exp ((t - s) • Q) (Q x)) := by
        show NormedSpace.exp (s • P)
          (-(NormedSpace.exp ((t - s) • Q) (Q x))) = _
        rw [map_neg]
      rw [step1, step2, ← sub_eq_add_neg, ← map_sub,
        ← map_sub, ContinuousLinearMap.sub_apply]
    rwa [hid] at hsum
  have hF'cont : Continuous F' := by
    rw [hF'def]
    apply Continuous.clm_apply
    · exact NormedSpace.exp_continuous.comp
        (continuous_id.smul continuous_const)
    · apply Continuous.clm_apply
      · exact NormedSpace.exp_continuous.comp
          ((continuous_const.sub continuous_id).smul
            continuous_const)
      · exact continuous_const
  have hInt : IntervalIntegrable F' MeasureTheory.volume 0 t :=
    hF'cont.intervalIntegrable 0 t
  have hFTC : ∫ s in (0 : ℝ)..t, F' s = F t - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s) hInt
  have hFt : F t = NormedSpace.exp (t • P) x := by
    rw [hFdef]
    simp only [sub_self, zero_smul, NormedSpace.exp_zero,
      ContinuousLinearMap.one_apply]
  have hF0 : F 0 = NormedSpace.exp (t • Q) x := by
    rw [hFdef]
    simp only [zero_smul, NormedSpace.exp_zero,
      ContinuousLinearMap.one_apply, sub_zero]
  calc ‖NormedSpace.exp (t • P) x
        - NormedSpace.exp (t • Q) x‖
      = ‖∫ s in (0 : ℝ)..t, F' s‖ := by
        rw [hFTC, hFt, hF0]
    _ ≤ ‖(P - Q) x‖ * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun s hs => by
            have hs0 : 0 ≤ s := by
              have h2 : s ∈ Set.Ioc (0 : ℝ) t := by
                rwa [Set.uIoc_of_le ht] at hs
              exact h2.1.le
            have hts : 0 ≤ t - s := by
              have h2 : s ∈ Set.Ioc (0 : ℝ) t := by
                rwa [Set.uIoc_of_le ht] at hs
              exact sub_nonneg.mpr h2.2
            have h2 : ‖NormedSpace.exp ((t - s) • Q)
                  ((P - Q) x)‖ ≤ ‖(P - Q) x‖ := by
              calc ‖NormedSpace.exp ((t - s) • Q)
                    ((P - Q) x)‖
                  ≤ ‖NormedSpace.exp ((t - s) • Q)‖
                    * ‖(P - Q) x‖ :=
                    (NormedSpace.exp
                      ((t - s) • Q)).le_opNorm _
                _ ≤ 1 * ‖(P - Q) x‖ :=
                    mul_le_mul_of_nonneg_right
                      (hQ (t - s) hts) (norm_nonneg _)
                _ = ‖(P - Q) x‖ := one_mul _
            calc ‖F' s‖
                ≤ ‖NormedSpace.exp (s • P)‖
                  * ‖NormedSpace.exp ((t - s) • Q)
                    ((P - Q) x)‖ :=
                  (NormedSpace.exp (s • P)).le_opNorm _
              _ ≤ 1 * ‖(P - Q) x‖ :=
                  mul_le_mul (hP s hs0) h2 (norm_nonneg _)
                    zero_le_one
              _ = ‖(P - Q) x‖ := one_mul _)
    _ = t * ‖(P - Q) x‖ := by
        rw [sub_zero, abs_of_nonneg ht, mul_comm]

/-- The one-sided Duhamel corollary (`Q = 0`):
`||exp (tP) x - x|| <= t * ||P x||` when `exp (tP)` is a
contraction. -/
theorem exp_sub_norm_le (P : E →L[ℝ] E)
    (hP : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • P)‖ ≤ 1)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • P) x - x‖ ≤ t * ‖P x‖ := by
  have h := duhamel_estimate P 0 (Commute.zero_right P)
    hP (fun s _ => by
      simpa using norm_one_le_clm (E := E)) x ht
  simpa using h

/-! ## 5. The Lumer-Phillips construction

Throughout this section, `D, A` are the densely defined
operator, `hdiss` the resolvent-bound dissipativity,
`hdense` the density, and `hsurj0` the range condition
at `lam0 > 0`. -/

section LPConstruction

variable (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
  (hdiss : DissBound D A) (hdense : Dense (↑D : Set E))
  {lam0 : ℝ} (hlam0 : 0 < lam0)
  (hsurj0 : Function.Surjective (lamSub D A lam0))

/-- The Yosida approximants of the LP data. -/
noncomputable def lpYosida (lam : ℝ) : E →L[ℝ] E :=
  yosidaA (resolventFam D A hdiss hlam0 hsurj0) lam

theorem lpYosida_exp_opNorm_le {lam : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
      lam)).toFun t‖ ≤ 1 := by
  rw [expSemigroup_toFun]
  exact exp_yosidaA_opNorm_le _
    (fun lam hlam => resolventFam_opNorm_le D A hdiss hlam0 hsurj0 hlam) hlam ht

theorem lpYosida_tendsto (hdense : Dense (↑D : Set E)) (x : D) :
    Tendsto (fun lam : ℝ =>
      lpYosida D A hdiss hlam0 hsurj0 lam (x : E)) atTop
      (𝓝 (A x)) :=
  yosidaA_tendsto_on_dom D A _
    (fun lam hlam =>
      resolventFam_hasResolventAt D A hdiss hlam0 hsurj0
        hlam)
    (fun z => resolvent_smul_tendsto D A hdense _
      (fun lam hlam =>
        resolventFam_hasResolventAt D A hdiss hlam0 hsurj0
          hlam)
      (fun lam hlam =>
        resolventFam_opNorm_le D A hdiss hlam0 hsurj0 hlam)
      z) x

theorem lpYosida_duhamel {lam mu : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (z : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun t z
      - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        mu)).toFun t z‖
      ≤ t * ‖lpYosida D A hdiss hlam0 hsurj0 lam z
        - lpYosida D A hdiss hlam0 hsurj0 mu z‖ := by
  rw [expSemigroup_toFun, expSemigroup_toFun]
  have h := duhamel_estimate
    (lpYosida D A hdiss hlam0 hsurj0 lam)
    (lpYosida D A hdiss hlam0 hsurj0 mu)
    (yosidaA_commute D A _
      (fun lam hlam =>
        resolventFam_hasResolventAt D A hdiss hlam0 hsurj0
          hlam) hlam hmu)
    (fun s hs => exp_yosidaA_opNorm_le _
      (fun lam hlam => resolventFam_opNorm_le D A hdiss hlam0 hsurj0 hlam)
      hlam hs)
    (fun s hs => exp_yosidaA_opNorm_le _
      (fun lam hlam => resolventFam_opNorm_le D A hdiss hlam0 hsurj0 hlam)
      hmu hs) z ht
  rwa [ContinuousLinearMap.sub_apply] at h

/-- The Cauchy estimate: for every `z` (not only domain
points) and `t >= 0`, the approximant semigroups are
uniformly Cauchy as `lam, mu -> infty`. -/
theorem lpApprox_cauchy (hdense : Dense (↑D : Set E)) (z : E) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, ∀ lam ≥ N, ∀ mu ≥ N,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t z
        - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          mu)).toFun t z‖ < ε := by
  have hz : z ∈ closure (↑D : Set E) := hdense z
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hwD, hwz⟩ := hz (ε / 4) (by positivity)
  set wD : D := ⟨w, hwD⟩ with hwDdef
  have hon := lpYosida_tendsto D A hdiss hlam0 hsurj0 hdense
    wD
  rw [Metric.tendsto_atTop] at hon
  obtain ⟨N, hN⟩ := hon (ε / (4 * (t + 1))) (by positivity)
  refine ⟨max N 1, fun lam hlam mu hmu => ?_⟩
  have hlam0' : 0 < lam :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hlam)
  have hmu0' : 0 < mu :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hmu)
  have hNlam : N ≤ lam := le_trans (le_max_left N 1) hlam
  have hNmu : N ≤ mu := le_trans (le_max_left N 1) hmu
  have hzw2 : ‖z - w‖ < ε / 4 := by
    rwa [dist_eq_norm] at hwz
  have htri : ‖lpYosida D A hdiss hlam0 hsurj0 lam w
      - lpYosida D A hdiss hlam0 hsurj0 mu w‖
      < ε / (2 * (t + 1)) := by
    have step1 : ‖lpYosida D A hdiss hlam0 hsurj0 lam w
        - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        ≤ ‖lpYosida D A hdiss hlam0 hsurj0 lam w - A wD‖
          + ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖ := by
      have h := norm_add_le
        (lpYosida D A hdiss hlam0 hsurj0 lam w - A wD)
        (A wD - lpYosida D A hdiss hlam0 hsurj0 mu w)
      rwa [sub_add_sub_cancel] at h
    refine lt_of_le_of_lt step1 ?_
    have d1 : dist (lpYosida D A hdiss hlam0 hsurj0 lam w)
        (A wD) < ε / (4 * (t + 1)) := hN lam hNlam
    have d2 : dist (lpYosida D A hdiss hlam0 hsurj0 mu w)
        (A wD) < ε / (4 * (t + 1)) := hN mu hNmu
    rw [dist_eq_norm] at d1 d2
    have d2' : ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        < ε / (4 * (t + 1)) := by
      rwa [norm_sub_rev] at d2
    calc ‖lpYosida D A hdiss hlam0 hsurj0 lam w - A wD‖
          + ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        < ε / (4 * (t + 1)) + ε / (4 * (t + 1)) :=
          add_lt_add d1 d2'
      _ = ε / (2 * (t + 1)) := by
          rw [← add_div,
            show ε + ε = 2 * ε by ring,
            show (4 : ℝ) * (t + 1) = 2 * (2 * (t + 1)) by ring,
            mul_div_mul_left _ _
              (show (2 : ℝ) ≠ 0 by norm_num)]
  have hmiddle : t * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
      - lpYosida D A hdiss hlam0 hsurj0 mu w‖ ≤ ε / 2 := by
    have ht1 : (t + 1) ≠ 0 := by linarith
    calc t * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
          - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        ≤ t * (ε / (2 * (t + 1))) :=
          mul_le_mul_of_nonneg_left (le_of_lt htri) ht
      _ = (ε / 2) * (t / (t + 1)) := by
          field_simp
      _ ≤ (ε / 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by linarith : (0 : ℝ) < t + 1)]
          linarith
      _ = ε / 2 := mul_one _
  have e1 : ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun t z
      - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        mu)).toFun t z‖
      ≤ ‖z - w‖ + t * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
          - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        + ‖z - w‖ := by
    have hsplit : (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z
        - (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun t z
        = (expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t
            (z - w)
          + ((expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t w
            - (expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun t w)
          + (expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun t
              (w - z) := by
      rw [map_sub, map_sub]; abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add_left (norm_add_le
        ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t (z - w))
        ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t w
          - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            mu)).toFun t w)) _) ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun t (z - w)‖
          ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun t‖ * ‖z - w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖z - w‖ :=
            mul_le_mul_of_nonneg_right
              (lpYosida_exp_opNorm_le D A hdiss hlam0
                hsurj0 hlam0' ht) (norm_nonneg _)
        _ = ‖z - w‖ := one_mul _
    · exact lpYosida_duhamel D A hdiss hlam0 hsurj0
        hlam0' hmu0' w ht
    · calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            mu)).toFun t (w - z)‖
          ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              mu)).toFun t‖ * ‖w - z‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖w - z‖ :=
            mul_le_mul_of_nonneg_right
              (lpYosida_exp_opNorm_le D A hdiss hlam0
                hsurj0 hmu0' ht) (norm_nonneg _)
        _ = ‖z - w‖ := by rw [one_mul, norm_sub_rev]
  refine lt_of_le_of_lt e1 ?_
  linarith [hmiddle, hzw2]

/-- The pointwise limit of the approximant semigroups. -/
noncomputable def lpLimit (t : ℝ) (z : E) : E :=
  Filter.limUnder atTop
    (fun lam => (expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z)

theorem lpLimit_tendsto (hdense : Dense (↑D : Set E)) {t : ℝ} (ht : 0 ≤ t) (z : E) :
    Tendsto (fun lam => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z)
      atTop (𝓝 (lpLimit D A hdiss hlam0 hsurj0 t z)) := by
  have hcau : CauchySeq (fun lam => (expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := lpApprox_cauchy D A hdiss hlam0 hsurj0 hdense z ht hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm]; exact hN m hm n hn⟩
  exact hcau.tendsto_limUnder

theorem lpLimit_apply_le (hdense : Dense (↑D : Set E)) {t : ℝ} (ht : 0 ≤ t) (z : E) :
    ‖lpLimit D A hdiss hlam0 hsurj0 t z‖ ≤ ‖z‖ := by
  have hT := (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense
    ht z).norm
  have hev : ∀ᶠ lam : ℝ in atTop,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun t z‖ ≤ ‖z‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam
      hlam
    have hlam0' : 0 < lam := lt_of_lt_of_le one_pos hlam
    calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t z‖
        ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun t‖ * ‖z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖z‖ :=
          mul_le_mul_of_nonneg_right
            (lpYosida_exp_opNorm_le D A hdiss hlam0
              hsurj0 hlam0' ht) (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  exact le_of_tendsto_of_tendsto hT tendsto_const_nhds hev

/-- The limit operator at time `t >= 0`, as a linear map. -/
noncomputable def lpLimitLin (t : ℝ) (ht : 0 ≤ t) :
    E →ₗ[ℝ] E where
  toFun := lpLimit D A hdiss hlam0 hsurj0 t
  map_add' := by
    intro a b
    show lpLimit D A hdiss hlam0 hsurj0 t (a + b)
      = lpLimit D A hdiss hlam0 hsurj0 t a
        + lpLimit D A hdiss hlam0 hsurj0 t b
    apply tendsto_nhds_unique
      (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense ht
        (a + b))
    have e : (fun lam => (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t
          (a + b))
        = fun lam => (expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t a
          + (expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t b := by
      funext lam
      exact map_add _ _ _
    rw [e]
    exact (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense ht
      a).add (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense
      ht b)
  map_smul' := by
    intro c a
    show lpLimit D A hdiss hlam0 hsurj0 t (c • a)
      = c • lpLimit D A hdiss hlam0 hsurj0 t a
    apply tendsto_nhds_unique
      (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense ht
        (c • a))
    have e : (fun lam => (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t
          (c • a))
        = fun lam => c • (expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t a := by
      funext lam
      exact map_smul _ _ _
    rw [e]
    exact (lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense ht
      a).const_smul c

/-- The limit operator at time `t`, as a bounded operator
(the value at `t < 0` is `1`, unconstrained by the
semigroup axioms). -/
noncomputable def lpOp (t : ℝ) : E →L[ℝ] E :=
  if h : 0 ≤ t then
    (lpLimitLin D A hdiss hdense hlam0 hsurj0 t h).mkContinuous
      1 (fun z => by
        show ‖lpLimit D A hdiss hlam0 hsurj0 t z‖ ≤ 1 * ‖z‖
        rw [one_mul]
        exact lpLimit_apply_le D A hdiss hlam0 hsurj0 hdense
          h z)
  else 1

theorem lpOp_apply {t : ℝ} (ht : 0 ≤ t) (z : E) :
    lpOp D A hdiss hdense hlam0 hsurj0 t z
      = lpLimit D A hdiss hlam0 hsurj0 t z := by
  rw [lpOp, dif_pos ht]
  rfl

theorem lpOp_tendsto {t : ℝ} (ht : 0 ≤ t) (z : E) :
    Tendsto (fun lam => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z)
      atTop (𝓝 (lpOp D A hdiss hdense hlam0 hsurj0 t z)) := by
  rw [lpOp_apply D A hdiss hdense hlam0 hsurj0 ht]
  exact lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense ht z

theorem lpOp_opNorm_le {t : ℝ} (ht : 0 ≤ t) :
    ‖lpOp D A hdiss hdense hlam0 hsurj0 t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
    rw [lpOp_apply D A hdiss hdense hlam0 hsurj0 ht]
    calc ‖lpLimit D A hdiss hlam0 hsurj0 t z‖
        ≤ ‖z‖ := lpLimit_apply_le D A hdiss hlam0 hsurj0 hdense ht z
      _ = 1 * ‖z‖ := (one_mul _).symm)

theorem lpOp_zero : lpOp D A hdiss hdense hlam0 hsurj0 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  rw [lpOp_apply D A hdiss hdense hlam0 hsurj0 le_rfl]
  have hT := lpLimit_tendsto D A hdiss hlam0 hsurj0 hdense
    le_rfl z
  have hconst : (fun lam => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun 0 z)
      = fun _ => z := by
    funext lam
    exact C0Semigroup.map_zero_apply _ _
  rw [hconst] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

theorem lpOp_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (z : E) :
    lpOp D A hdiss hdense hlam0 hsurj0 (s + t) z
      = lpOp D A hdiss hdense hlam0 hsurj0 s
        (lpOp D A hdiss hdense hlam0 hsurj0 t z) := by
  have hst : 0 ≤ s + t := add_nonneg hs ht
  have key : ∀ lam ≥ (1 : ℝ),
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun (s + t) z
        - lpOp D A hdiss hdense hlam0 hsurj0 s
          (lpOp D A hdiss hdense hlam0 hsurj0 t z)‖
      ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun t z
          - lpOp D A hdiss hdense hlam0 hsurj0 t z‖
        + ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s
            (lpOp D A hdiss hdense hlam0 hsurj0 t z)
          - lpOp D A hdiss hdense hlam0 hsurj0 s
            (lpOp D A hdiss hdense hlam0 hsurj0 t z)‖ := by
    intro lam hlam
    have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam
    have hfac : (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun (s + t) z
        = (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s ((expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z) :=
      C0Semigroup.map_add_apply _ hs ht z
    rw [hfac]
    have hdecomp : (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s
        ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t z)
        - lpOp D A hdiss hdense hlam0 hsurj0 s
          (lpOp D A hdiss hdense hlam0 hsurj0 t z)
        = ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s ((expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z)
          - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s
            (lpOp D A hdiss hdense hlam0 hsurj0 t z))
          + ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun s
              (lpOp D A hdiss hdense hlam0 hsurj0 t z)
            - lpOp D A hdiss hdense hlam0 hsurj0 s
              (lpOp D A hdiss hdense hlam0 hsurj0 t z)) := by
      abel
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) (add_le_add_left ?_ _)
    rw [← map_sub]
    calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s ((expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun t z
          - lpOp D A hdiss hdense hlam0 hsurj0 t z)‖
        ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s‖
          * ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun t z
            - lpOp D A hdiss hdense hlam0 hsurj0 t z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun t z
            - lpOp D A hdiss hdense hlam0 hsurj0 t z‖ :=
          mul_le_mul_of_nonneg_right
            (lpYosida_exp_opNorm_le D A hdiss hlam0 hsurj0
              hlampos hs) (norm_nonneg _)
      _ = ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun t z
            - lpOp D A hdiss hdense hlam0 hsurj0 t z‖ :=
          one_mul _
  have hg : Tendsto (fun lam =>
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t z
        - lpOp D A hdiss hdense hlam0 hsurj0 t z‖
      + ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s
          (lpOp D A hdiss hdense hlam0 hsurj0 t z)
        - lpOp D A hdiss hdense hlam0 hsurj0 s
          (lpOp D A hdiss hdense hlam0 hsurj0 t z)‖)
      atTop (𝓝 0) := by
    have g1 : Tendsto (fun lam =>
        ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun t z
          - lpOp D A hdiss hdense hlam0 hsurj0 t z‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (lpOp_tendsto D A hdiss hdense hlam0 hsurj0 ht z)
    have g2 : Tendsto (fun lam =>
        ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s
            (lpOp D A hdiss hdense hlam0 hsurj0 t z)
          - lpOp D A hdiss hdense hlam0 hsurj0 s
            (lpOp D A hdiss hdense hlam0 hsurj0 t z)‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (lpOp_tendsto D A hdiss hdense hlam0 hsurj0 hs
          (lpOp D A hdiss hdense hlam0 hsurj0 t z))
    simpa using g1.add g2
  have hlim : Tendsto (fun lam =>
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun (s + t) z
        - lpOp D A hdiss hdense hlam0 hsurj0 s
          (lpOp D A hdiss hdense hlam0 hsurj0 t z)‖)
      atTop (𝓝 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun lam => norm_nonneg _)
      ?_ hg
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam
      hlam
    exact key lam hlam
  have hT2 : Tendsto (fun lam => (expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun (s + t) z)
      atTop (𝓝 (lpOp D A hdiss hdense hlam0 hsurj0 s
        (lpOp D A hdiss hdense hlam0 hsurj0 t z))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  exact tendsto_nhds_unique
    (lpOp_tendsto D A hdiss hdense hlam0 hsurj0 hst z) hT2

/-- Eventual bound on the Yosida approximants at a domain
point. -/
theorem lpYosida_apply_norm_le_eventually
    (hdense : Dense (↑D : Set E)) (x : D) :
    ∀ᶠ lam : ℝ in atTop,
      ‖lpYosida D A hdiss hlam0 hsurj0 lam (x : E)‖
        ≤ ‖A x‖ + 1 := by
  have hT := lpYosida_tendsto D A hdiss hlam0 hsurj0 hdense x
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨N, hN⟩ := hT 1 one_pos
  filter_upwards [eventually_ge_atTop N] with lam hlam
  have hd := hN lam hlam
  rw [dist_eq_norm] at hd
  calc ‖lpYosida D A hdiss hlam0 hsurj0 lam (x : E)‖
      = ‖(lpYosida D A hdiss hlam0 hsurj0 lam (x : E)
        - A x) + A x‖ := by rw [sub_add_cancel]
    _ ≤ ‖lpYosida D A hdiss hlam0 hsurj0 lam (x : E) - A x‖
        + ‖A x‖ := norm_add_le _ _
    _ ≤ 1 + ‖A x‖ := add_le_add hd.le le_rfl
    _ = ‖A x‖ + 1 := add_comm _ _

/-- On the domain, the limit semigroup moves a point by at
most `t * (‖A x‖ + 1)`. -/
theorem lpOp_sub_le_of_mem {t : ℝ} (ht : 0 ≤ t) (x : D) :
    ‖lpOp D A hdiss hdense hlam0 hsurj0 t (x : E) - (x : E)‖
      ≤ t * (‖A x‖ + 1) := by
  have hnorm : Tendsto (fun lam =>
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t (x : E) - (x : E)‖) atTop
      (𝓝 ‖lpOp D A hdiss hdense hlam0 hsurj0 t (x : E)
        - (x : E)‖) :=
    ((lpOp_tendsto D A hdiss hdense hlam0 hsurj0 ht
      (x : E)).sub_const (x : E)).norm
  have hev : ∀ᶠ lam : ℝ in atTop,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun t (x : E) - (x : E)‖
        ≤ t * (‖A x‖ + 1) := by
    filter_upwards [lpYosida_apply_norm_le_eventually D A
      hdiss hlam0 hsurj0 hdense x,
      eventually_ge_atTop (1 : ℝ)] with lam hlam hlam1
    have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam1
    rw [expSemigroup_toFun]
    refine le_trans (exp_sub_norm_le _
      (fun s hs => exp_yosidaA_opNorm_le _
        (fun mu hmu => resolventFam_opNorm_le D A hdiss
          hlam0 hsurj0 hmu) hlampos hs) _ ht)
      (mul_le_mul_of_nonneg_left hlam ht)
  exact le_of_tendsto_of_tendsto hnorm tendsto_const_nhds hev

/-- Lipschitz-type bound for domain orbits of the limit
semigroup. -/
theorem lpOp_orbit_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x : D) :
    ‖lpOp D A hdiss hdense hlam0 hsurj0 a (x : E)
      - lpOp D A hdiss hdense hlam0 hsurj0 b (x : E)‖
      ≤ |a - b| * (‖A x‖ + 1) := by
  rcases le_total a b with h | h
  · have hba : 0 ≤ b - a := sub_nonneg.mpr h
    have e : lpOp D A hdiss hdense hlam0 hsurj0 b (x : E)
        = lpOp D A hdiss hdense hlam0 hsurj0 a
          (lpOp D A hdiss hdense hlam0 hsurj0 (b - a)
            (x : E)) := by
      conv_lhs => rw [show b = a + (b - a) by ring]
      exact lpOp_add D A hdiss hdense hlam0 hsurj0 ha hba
        (x : E)
    rw [norm_sub_rev, e, ← map_sub]
    calc ‖lpOp D A hdiss hdense hlam0 hsurj0 a
          (lpOp D A hdiss hdense hlam0 hsurj0 (b - a) (x : E)
            - (x : E))‖
        ≤ ‖lpOp D A hdiss hdense hlam0 hsurj0 a‖
          * ‖lpOp D A hdiss hdense hlam0 hsurj0 (b - a)
              (x : E) - (x : E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ((b - a) * (‖A x‖ + 1)) :=
          mul_le_mul
            (lpOp_opNorm_le D A hdiss hdense hlam0 hsurj0 ha)
            (lpOp_sub_le_of_mem D A hdiss hdense hlam0
              hsurj0 hba x) (norm_nonneg _) zero_le_one
      _ = |a - b| * (‖A x‖ + 1) := by
          rw [one_mul, abs_of_nonpos (sub_nonpos.mpr h),
            neg_sub]
  · have hab : 0 ≤ a - b := sub_nonneg.mpr h
    have e : lpOp D A hdiss hdense hlam0 hsurj0 a (x : E)
        = lpOp D A hdiss hdense hlam0 hsurj0 b
          (lpOp D A hdiss hdense hlam0 hsurj0 (a - b)
            (x : E)) := by
      conv_lhs => rw [show a = b + (a - b) by ring]
      exact lpOp_add D A hdiss hdense hlam0 hsurj0 hb hab
        (x : E)
    rw [e, ← map_sub]
    calc ‖lpOp D A hdiss hdense hlam0 hsurj0 b
          (lpOp D A hdiss hdense hlam0 hsurj0 (a - b) (x : E)
            - (x : E))‖
        ≤ ‖lpOp D A hdiss hdense hlam0 hsurj0 b‖
          * ‖lpOp D A hdiss hdense hlam0 hsurj0 (a - b)
              (x : E) - (x : E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ((a - b) * (‖A x‖ + 1)) :=
          mul_le_mul
            (lpOp_opNorm_le D A hdiss hdense hlam0 hsurj0 hb)
            (lpOp_sub_le_of_mem D A hdiss hdense hlam0
              hsurj0 hab x) (norm_nonneg _) zero_le_one
      _ = |a - b| * (‖A x‖ + 1) := by
          rw [one_mul, abs_of_nonneg hab]

theorem lpOp_continuousAt_zero (z : E) :
    ContinuousAt (fun t => lpOp D A hdiss hdense hlam0
      hsurj0 t z) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hz : z ∈ closure (↑D : Set E) := hdense z
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hwD, hwz⟩ := hz (ε / 4) (by positivity)
  set wD : D := ⟨w, hwD⟩ with hwDdef
  have hzw : ‖z - w‖ < ε / 4 := by rwa [dist_eq_norm] at hwz
  have h0z : lpOp D A hdiss hdense hlam0 hsurj0 0 z = z := by
    have h := congrArg (fun T : E →L[ℝ] E => T z)
      (lpOp_zero D A hdiss hdense hlam0 hsurj0)
    exact h
  refine ⟨ε / (4 * (‖A wD‖ + 1)), by positivity, ?_⟩
  intro t ht
  rw [Real.dist_eq, sub_zero] at ht
  rw [h0z, dist_eq_norm]
  by_cases ht0 : 0 ≤ t
  · have hC : (0 : ℝ) < ‖A wD‖ + 1 := by
      have h1 := norm_nonneg (A wD)
      linarith
    have htC : t * (‖A wD‖ + 1) < ε / 4 := by
      have htlt : t < ε / (4 * (‖A wD‖ + 1)) :=
        lt_of_le_of_lt (le_abs_self t) ht
      have h2 := (lt_div_iff₀ (by positivity :
        (0 : ℝ) < 4 * (‖A wD‖ + 1))).mp htlt
      have e : t * (4 * (‖A wD‖ + 1))
          = 4 * (t * (‖A wD‖ + 1)) := by ring
      linarith
    have hsplit : lpOp D A hdiss hdense hlam0 hsurj0 t z - z
        = (lpOp D A hdiss hdense hlam0 hsurj0 t z
          - lpOp D A hdiss hdense hlam0 hsurj0 t w)
          + (lpOp D A hdiss hdense hlam0 hsurj0 t w - w)
          + (w - z) := by abel
    calc ‖lpOp D A hdiss hdense hlam0 hsurj0 t z - z‖
        ≤ ‖lpOp D A hdiss hdense hlam0 hsurj0 t z
            - lpOp D A hdiss hdense hlam0 hsurj0 t w‖
          + ‖lpOp D A hdiss hdense hlam0 hsurj0 t w - w‖
          + ‖w - z‖ := by
          rw [hsplit]
          exact le_trans (norm_add_le _ _)
            (add_le_add_left (norm_add_le _ _) _)
      _ ≤ ‖z - w‖ + (t * (‖A wD‖ + 1)) + ‖z - w‖ := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · rw [← map_sub]
            exact le_trans (ContinuousLinearMap.le_opNorm
              _ _) (le_trans (mul_le_mul_of_nonneg_right
              (lpOp_opNorm_le D A hdiss hdense hlam0 hsurj0
                ht0) (norm_nonneg _)) (by rw [one_mul]))
          · exact lpOp_sub_le_of_mem D A hdiss hdense hlam0
              hsurj0 ht0 wD
          · rw [norm_sub_rev]
      _ < ε := by linarith
  · have htz : lpOp D A hdiss hdense hlam0 hsurj0 t z
        = z := by
      have h1 : lpOp D A hdiss hdense hlam0 hsurj0 t = 1 :=
        dif_neg ht0
      rw [h1]
      exact ContinuousLinearMap.one_apply z
    rw [htz, sub_self, norm_zero]
    exact hε

theorem lpOp_continuousOn (z : E) :
    ContinuousOn (fun t => lpOp D A hdiss hdense hlam0
      hsurj0 t z) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  have hz : z ∈ closure (↑D : Set E) := hdense z
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hwD, hwz⟩ := hz (ε / 4) (by positivity)
  set wD : D := ⟨w, hwD⟩ with hwDdef
  have hzw : ‖z - w‖ < ε / 4 := by rwa [dist_eq_norm] at hwz
  have ht0' : 0 ≤ t0 := ht0
  refine ⟨ε / (4 * (‖A wD‖ + 1)), by positivity, ?_⟩
  intro a ha had
  have ha' : 0 ≤ a := ha
  rw [dist_eq_norm] at had ⊢
  have hmid : ‖lpOp D A hdiss hdense hlam0 hsurj0 a (wD : E)
      - lpOp D A hdiss hdense hlam0 hsurj0 t0 (wD : E)‖
      ≤ ‖a - t0‖ * (‖A wD‖ + 1) :=
    lpOp_orbit_sub_le D A hdiss hdense hlam0 hsurj0 ha'
      ht0' wD
  have hmidC : ‖a - t0‖ * (‖A wD‖ + 1) < ε / 4 := by
    have h2 := (lt_div_iff₀ (by positivity :
      (0 : ℝ) < 4 * (‖A wD‖ + 1))).mp had
    have e : ‖a - t0‖ * (4 * (‖A wD‖ + 1))
        = 4 * (‖a - t0‖ * (‖A wD‖ + 1)) := by ring
    linarith
  have hsplit : lpOp D A hdiss hdense hlam0 hsurj0 a z
      - lpOp D A hdiss hdense hlam0 hsurj0 t0 z
      = (lpOp D A hdiss hdense hlam0 hsurj0 a z
        - lpOp D A hdiss hdense hlam0 hsurj0 a w)
        + (lpOp D A hdiss hdense hlam0 hsurj0 a w
          - lpOp D A hdiss hdense hlam0 hsurj0 t0 w)
        + (lpOp D A hdiss hdense hlam0 hsurj0 t0 w
          - lpOp D A hdiss hdense hlam0 hsurj0 t0 z) := by
    abel
  calc ‖lpOp D A hdiss hdense hlam0 hsurj0 a z
        - lpOp D A hdiss hdense hlam0 hsurj0 t0 z‖
      ≤ ‖lpOp D A hdiss hdense hlam0 hsurj0 a z
          - lpOp D A hdiss hdense hlam0 hsurj0 a w‖
        + ‖lpOp D A hdiss hdense hlam0 hsurj0 a w
          - lpOp D A hdiss hdense hlam0 hsurj0 t0 w‖
        + ‖lpOp D A hdiss hdense hlam0 hsurj0 t0 w
          - lpOp D A hdiss hdense hlam0 hsurj0 t0 z‖ := by
        rw [hsplit]
        exact le_trans (norm_add_le _ _)
          (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖z - w‖ + (‖a - t0‖ * (‖A wD‖ + 1)) + ‖z - w‖ := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · rw [← map_sub]
          exact le_trans (ContinuousLinearMap.le_opNorm
            _ _) (le_trans (mul_le_mul_of_nonneg_right
            (lpOp_opNorm_le D A hdiss hdense hlam0 hsurj0
              ha') (norm_nonneg _)) (by rw [one_mul]))
        · exact hmid
        · rw [← map_sub]
          have h3 := le_trans (ContinuousLinearMap.le_opNorm
            (lpOp D A hdiss hdense hlam0 hsurj0 t0)
            (w - z)) (le_trans (mul_le_mul_of_nonneg_right
            (lpOp_opNorm_le D A hdiss hdense hlam0 hsurj0
              ht0') (norm_nonneg (w - z))) (by rw [one_mul]))
          rwa [norm_sub_rev] at h3
    _ < ε := by linarith

/-- The Lumer–Phillips semigroup: the `C0Semigroup`
assembled from the limit operators. -/
noncomputable def lpSemigroup : C0Semigroup E where
  toFun := lpOp D A hdiss hdense hlam0 hsurj0
  map_zero := lpOp_zero D A hdiss hdense hlam0 hsurj0
  map_add := by
    intro s t hs ht
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply]
    exact lpOp_add D A hdiss hdense hlam0 hsurj0 hs ht z
  strongly_continuous := fun z =>
    lpOp_continuousOn D A hdiss hdense hlam0 hsurj0 z

end LPConstruction

/-! ## Generator identification -/

/-- Dissipativity of the generator of any contraction
`C0Semigroup`, in resolvent-bound form: if `y` is the
generator value at `x`, then `lam * ‖x‖ ≤ ‖lam • x - y‖`
for all `lam > 0`. Proved from the difference quotient
by the reverse triangle inequality. -/
theorem gen_diss_bound (S : C0Semigroup E)
    (hS : ∀ t : ℝ, 0 ≤ t → ‖S.toFun t‖ ≤ 1)
    {x y : E} (h : S.HasGen x y)
    {lam : ℝ} (hlam : 0 < lam) :
    lam * ‖x‖ ≤ ‖lam • x - y‖ := by
  have hg : Tendsto
      (fun h : ℝ => ‖lam • x - h⁻¹ • (S.toFun h x - x)‖)
      (𝓝[>] 0) (𝓝 ‖lam • x - y‖) :=
    (tendsto_const_nhds.sub h).norm
  refine ge_of_tendsto hg ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  have hident : lam • x - h⁻¹ • (S.toFun h x - x)
      = h⁻¹ • ((1 + lam * h) • x - S.toFun h x) := by
    have e1 : h⁻¹ • ((1 + lam * h) • x - S.toFun h x)
        = (lam + h⁻¹) • x - h⁻¹ • S.toFun h x := by
      rw [smul_sub, smul_smul,
        show h⁻¹ * (1 + lam * h) = lam + h⁻¹ by
          rw [mul_add, mul_one, mul_left_comm,
            inv_mul_cancel₀ hh0.ne', mul_one, add_comm],
        add_smul]
    rw [e1, add_smul, smul_sub]
    abel
  rw [hident, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hh0.le)]
  have hge : (lam * h) * ‖x‖
      ≤ ‖(1 + lam * h) • x - S.toFun h x‖ := by
    have h1 : ‖(1 + lam * h) • x‖ - ‖S.toFun h x‖
        ≤ ‖(1 + lam * h) • x - S.toFun h x‖ :=
      le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
    have h2 : ‖S.toFun h x‖ ≤ ‖x‖ :=
      le_trans (ContinuousLinearMap.le_opNorm _ _)
        (le_trans (mul_le_mul_of_nonneg_right
          (hS h hh0.le) (norm_nonneg _)) (by rw [one_mul]))
    have h3 : ‖(1 + lam * h) • x‖ = (1 + lam * h) * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg
        (by positivity : (0 : ℝ) ≤ 1 + lam * h)]
    linarith
  have h4 : h⁻¹ * ((lam * h) * ‖x‖) = lam * ‖x‖ := by
    rw [← mul_assoc, mul_left_comm, inv_mul_cancel₀ hh0.ne',
      mul_one]
  calc lam * ‖x‖ = h⁻¹ * ((lam * h) * ‖x‖) := h4.symm
    _ ≤ h⁻¹ * ‖(1 + lam * h) • x - S.toFun h x‖ :=
        mul_le_mul_of_nonneg_left hge
          (inv_nonneg.mpr hh0.le)

section LPGenerator

variable (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
  (hdiss : DissBound D A) (hdense : Dense (↑D : Set E))
  {lam0 : ℝ} (hlam0 : 0 < lam0)
  (hsurj0 : Function.Surjective (lamSub D A lam0))

theorem lpSemigroup_toFun_apply (t : ℝ) (z : E) :
    (lpSemigroup D A hdiss hdense hlam0 hsurj0).toFun t z
      = lpOp D A hdiss hdense hlam0 hsurj0 t z := rfl

/-- Uniform Cauchy estimate: the approximant semigroups
are uniformly Cauchy on compact time intervals `[0, h]`,
for every fixed vector. -/
theorem lpApprox_cauchy_uniform
    (hdense : Dense (↑D : Set E)) (z : E) {h : ℝ}
    (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, ∀ lam ≥ N, ∀ mu ≥ N, ∀ s ∈ Set.Icc 0 h,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s z
        - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          mu)).toFun s z‖ < ε := by
  have hz : z ∈ closure (↑D : Set E) := hdense z
  rw [Metric.mem_closure_iff] at hz
  obtain ⟨w, hwD, hwz⟩ := hz (ε / 4) (by positivity)
  set wD : D := ⟨w, hwD⟩ with hwDdef
  have hon := lpYosida_tendsto D A hdiss hlam0 hsurj0 hdense
    wD
  rw [Metric.tendsto_atTop] at hon
  obtain ⟨N, hN⟩ := hon (ε / (4 * (h + 1))) (by positivity)
  refine ⟨max N 1, fun lam hlam mu hmu s hs => ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hlam0' : 0 < lam :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hlam)
  have hmu0' : 0 < mu :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hmu)
  have hNlam : N ≤ lam := le_trans (le_max_left N 1) hlam
  have hNmu : N ≤ mu := le_trans (le_max_left N 1) hmu
  have hzw2 : ‖z - w‖ < ε / 4 := by
    rwa [dist_eq_norm] at hwz
  have htri : ‖lpYosida D A hdiss hlam0 hsurj0 lam w
      - lpYosida D A hdiss hlam0 hsurj0 mu w‖
      < ε / (2 * (h + 1)) := by
    have step1 : ‖lpYosida D A hdiss hlam0 hsurj0 lam w
        - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        ≤ ‖lpYosida D A hdiss hlam0 hsurj0 lam w - A wD‖
          + ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖ := by
      have h := norm_add_le
        (lpYosida D A hdiss hlam0 hsurj0 lam w - A wD)
        (A wD - lpYosida D A hdiss hlam0 hsurj0 mu w)
      rwa [sub_add_sub_cancel] at h
    refine lt_of_le_of_lt step1 ?_
    have d1 : dist (lpYosida D A hdiss hlam0 hsurj0 lam w)
        (A wD) < ε / (4 * (h + 1)) := hN lam hNlam
    have d2 : dist (lpYosida D A hdiss hlam0 hsurj0 mu w)
        (A wD) < ε / (4 * (h + 1)) := hN mu hNmu
    rw [dist_eq_norm] at d1 d2
    have d2' : ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        < ε / (4 * (h + 1)) := by
      rwa [norm_sub_rev] at d2
    calc ‖lpYosida D A hdiss hlam0 hsurj0 lam w - A wD‖
          + ‖A wD - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        < ε / (4 * (h + 1)) + ε / (4 * (h + 1)) :=
          add_lt_add d1 d2'
      _ = ε / (2 * (h + 1)) := by
          rw [← add_div,
            show ε + ε = 2 * ε by ring,
            show (4 : ℝ) * (h + 1) = 2 * (2 * (h + 1)) by ring,
            mul_div_mul_left _ _
              (show (2 : ℝ) ≠ 0 by norm_num)]
  have hmiddle : s * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
      - lpYosida D A hdiss hlam0 hsurj0 mu w‖ ≤ ε / 2 := by
    calc s * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
          - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        ≤ h * (ε / (2 * (h + 1))) :=
          le_trans (mul_le_mul_of_nonneg_right hs.2
            (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (le_of_lt htri) hh)
      _ = (ε / 2) * (h / (h + 1)) := by
          field_simp
      _ ≤ (ε / 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by linarith : (0 : ℝ) < h + 1)]
          linarith
      _ = ε / 2 := mul_one _
  have e1 : ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun s z
      - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        mu)).toFun s z‖
      ≤ ‖z - w‖ + s * ‖lpYosida D A hdiss hlam0 hsurj0 lam w
          - lpYosida D A hdiss hlam0 hsurj0 mu w‖
        + ‖z - w‖ := by
    have hsplit : (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s z
        - (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun s z
        = (expSemigroup
            (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s
            (z - w)
          + ((expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s w
            - (expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun s w)
          + (expSemigroup
              (lpYosida D A hdiss hlam0 hsurj0 mu)).toFun s
              (w - z) := by
      rw [map_sub, map_sub]; abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add_left (norm_add_le
        ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s (z - w))
        ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s w
          - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            mu)).toFun s w)) _) ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            lam)).toFun s (z - w)‖
          ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              lam)).toFun s‖ * ‖z - w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖z - w‖ :=
            mul_le_mul_of_nonneg_right
              (lpYosida_exp_opNorm_le D A hdiss hlam0
                hsurj0 hlam0' hs0) (norm_nonneg _)
        _ = ‖z - w‖ := one_mul _
    · exact lpYosida_duhamel D A hdiss hlam0 hsurj0
        hlam0' hmu0' w hs0
    · calc ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
            mu)).toFun s (w - z)‖
          ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
              mu)).toFun s‖ * ‖w - z‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖w - z‖ :=
            mul_le_mul_of_nonneg_right
              (lpYosida_exp_opNorm_le D A hdiss hlam0
                hsurj0 hmu0' hs0) (norm_nonneg _)
        _ = ‖z - w‖ := by rw [one_mul, norm_sub_rev]
  refine lt_of_le_of_lt e1 ?_
  linarith [hmiddle, hzw2]

/-- The approximant semigroups converge to the limit
semigroup uniformly on compact time intervals. -/
theorem lpOp_tendsto_uniform_on_Icc (z : E) {h : ℝ}
    (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, ∀ lam ≥ N, ∀ s ∈ Set.Icc 0 h,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s z
        - lpOp D A hdiss hdense hlam0 hsurj0 s z‖ ≤ ε := by
  obtain ⟨N, hN⟩ := lpApprox_cauchy_uniform D A hdiss
    hlam0 hsurj0 hdense z hh (ε := ε / 2) (by positivity)
  refine ⟨N, fun lam hlam s hs => ?_⟩
  have hnorm : Tendsto (fun mu =>
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s z
        - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          mu)).toFun s z‖) atTop
      (𝓝 ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s z
        - lpOp D A hdiss hdense hlam0 hsurj0 s z‖) :=
    (tendsto_const_nhds.sub
      (lpOp_tendsto D A hdiss hdense hlam0 hsurj0 hs.1
        z)).norm
  have hev : ∀ᶠ mu : ℝ in atTop,
      ‖(expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          lam)).toFun s z
        - (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
          mu)).toFun s z‖ ≤ ε := by
    filter_upwards [eventually_ge_atTop N] with mu hmu
    exact (hN lam hlam mu hmu s hs).le.trans
      (by linarith [hε])
  exact le_of_tendsto_of_tendsto hnorm tendsto_const_nhds hev

theorem uIcc_zero_subset_Ici {h : ℝ} (hh : 0 ≤ h) :
    Set.uIcc 0 h ⊆ Set.Ici (0 : ℝ) := by
  intro s hs
  rcases Set.mem_uIcc.mp hs with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Set.mem_Ici.mpr h1
  · exact Set.mem_Ici.mpr (le_trans hh h1)

/-- The integrated identity for the Yosida approximants:
`S_lam h x - x = ∫₀^h S_lam s (A_lam x) ds` on the
domain. -/
theorem lpIntegral_identity_approx (x : D) {lam : ℝ}
    (hlam : 0 < lam) {h : ℝ} (hh : 0 ≤ h) :
    (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun h (x : E) - (x : E)
      = ∫ s in 0..h, (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s
          (lpYosida D A hdiss hlam0 hsurj0 lam (x : E)) := by
  have hderiv : ∀ s ∈ Set.uIcc 0 h, HasDerivAt
      (fun u => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun u
        (x : E))
      ((expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun s (lpYosida D A hdiss hlam0 hsurj0 lam
        (x : E))) s := by
    intro s _
    have hc : HasDerivAt
        (fun u : ℝ => NormedSpace.exp
          (u • lpYosida D A hdiss hlam0 hsurj0 lam))
        (NormedSpace.exp (s • lpYosida D A hdiss hlam0
          hsurj0 lam) * lpYosida D A hdiss hlam0 hsurj0 lam)
        s :=
      hasDerivAt_exp_smul_const
        (lpYosida D A hdiss hlam0 hsurj0 lam) s
    have happ := hc.clm_apply (hasDerivAt_const s (x : E))
    simpa [ContinuousLinearMap.mul_apply, expSemigroup_toFun]
      using happ
  have hint : IntervalIntegrable
      (fun s => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s
        (lpYosida D A hdiss hlam0 hsurj0 lam (x : E)))
      MeasureTheory.volume 0 h :=
    ((expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).strongly_continuous
      _).mono (uIcc_zero_subset_Ici hh) |>.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint
  rw [C0Semigroup.map_zero_apply] at hFTC
  exact hFTC.symm

/-- The integral identity for the limit semigroup:
`S h x - x = ∫₀^h S s (A x) ds` for `x` in the domain. -/
theorem lpIntegral_identity (x : D) {h : ℝ} (hh : 0 ≤ h) :
    (lpSemigroup D A hdiss hdense hlam0 hsurj0).toFun h
        (x : E) - (x : E)
      = ∫ s in 0..h, (lpSemigroup D A hdiss hdense hlam0
          hsurj0).toFun s (A x) := by
  have hLHS : Tendsto (fun lam => (expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun h (x : E)
        - (x : E)) atTop
      (𝓝 ((lpSemigroup D A hdiss hdense hlam0 hsurj0).toFun
        h (x : E) - (x : E))) :=
    (lpOp_tendsto D A hdiss hdense hlam0 hsurj0 hh
      (x : E)).sub_const (x : E)
  have hInt : Tendsto (fun lam => ∫ s in 0..h,
      (expSemigroup (lpYosida D A hdiss hlam0 hsurj0
        lam)).toFun s (lpYosida D A hdiss hlam0 hsurj0 lam
        (x : E))) atTop
      (𝓝 (∫ s in 0..h, (lpSemigroup D A hdiss hdense
        hlam0 hsurj0).toFun s (A x))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N1, hN1⟩ := lpOp_tendsto_uniform_on_Icc D A
      hdiss hdense hlam0 hsurj0 (A x) hh
      (ε := ε / (2 * (h + 1))) (by positivity)
    have hY := lpYosida_tendsto D A hdiss hlam0 hsurj0
      hdense x
    rw [Metric.tendsto_atTop] at hY
    obtain ⟨N2, hN2⟩ := hY (ε / (2 * (h + 1)))
      (by positivity)
    refine ⟨max (max N1 N2) 1, fun lam hlam => ?_⟩
    have hlam1 : N1 ≤ lam :=
      le_trans (le_trans (le_max_left N1 N2)
        (le_max_left _ _)) hlam
    have hlam2 : N2 ≤ lam :=
      le_trans (le_trans (le_max_right N1 N2)
        (le_max_left _ _)) hlam
    have hlampos : 0 < lam :=
      lt_of_lt_of_le one_pos
        (le_trans (le_max_right _ _) hlam)
    have hdY : ‖lpYosida D A hdiss hlam0 hsurj0 lam (x : E)
        - A x‖ < ε / (2 * (h + 1)) := by
      have h2 := hN2 lam hlam2
      rwa [dist_eq_norm] at h2
    have hint1 : IntervalIntegrable
        (fun s => (expSemigroup
          (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun s
          (lpYosida D A hdiss hlam0 hsurj0 lam (x : E)))
        MeasureTheory.volume 0 h :=
      ((expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0
          lam)).strongly_continuous _).mono
        (uIcc_zero_subset_Ici hh) |>.intervalIntegrable
    have hint2 : IntervalIntegrable
        (fun s => (lpSemigroup D A hdiss hdense hlam0
          hsurj0).toFun s (A x)) MeasureTheory.volume 0 h :=
      ((lpSemigroup D A hdiss hdense hlam0
        hsurj0).strongly_continuous (A x)).mono
        (uIcc_zero_subset_Ici hh) |>.intervalIntegrable
    rw [dist_eq_norm, ← intervalIntegral.integral_sub
      hint1 hint2]
    refine lt_of_le_of_lt
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := ε / (h + 1)) (fun s hs => ?_)) ?_
    · have hsI : s ∈ Set.Ioc (0 : ℝ) h := by
        rwa [Set.uIoc_of_le hh] at hs
      have hsC : s ∈ Set.Icc 0 h := ⟨hsI.1.le, hsI.2⟩
      calc ‖(expSemigroup (lpYosida D A hdiss hlam0
            hsurj0 lam)).toFun s (lpYosida D A hdiss hlam0
            hsurj0 lam (x : E))
          - (lpSemigroup D A hdiss hdense hlam0
            hsurj0).toFun s (A x)‖
          = ‖(expSemigroup (lpYosida D A hdiss hlam0
              hsurj0 lam)).toFun s (lpYosida D A hdiss
              hlam0 hsurj0 lam (x : E) - A x)
            + ((expSemigroup (lpYosida D A hdiss hlam0
                hsurj0 lam)).toFun s (A x)
              - (lpSemigroup D A hdiss hdense hlam0
                hsurj0).toFun s (A x))‖ := by
            rw [map_sub]; abel
        _ ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0
              hsurj0 lam)).toFun s (lpYosida D A hdiss
              hlam0 hsurj0 lam (x : E) - A x)‖
            + ‖(expSemigroup (lpYosida D A hdiss hlam0
                hsurj0 lam)).toFun s (A x)
              - (lpSemigroup D A hdiss hdense hlam0
                hsurj0).toFun s (A x)‖ :=
            norm_add_le _ _
        _ ≤ ‖lpYosida D A hdiss hlam0 hsurj0 lam (x : E)
              - A x‖ + (ε / (2 * (h + 1))) := by
            refine add_le_add ?_ (hN1 lam hlam1 s hsC)
            calc ‖(expSemigroup (lpYosida D A hdiss hlam0
                  hsurj0 lam)).toFun s (lpYosida D A hdiss
                  hlam0 hsurj0 lam (x : E) - A x)‖
                ≤ ‖(expSemigroup (lpYosida D A hdiss hlam0
                    hsurj0 lam)).toFun s‖
                  * ‖lpYosida D A hdiss hlam0 hsurj0 lam
                    (x : E) - A x‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖lpYosida D A hdiss hlam0 hsurj0 lam
                    (x : E) - A x‖ :=
                  mul_le_mul_of_nonneg_right
                    (lpYosida_exp_opNorm_le D A hdiss hlam0
                      hsurj0 hlampos hsI.1.le)
                    (norm_nonneg _)
              _ = ‖lpYosida D A hdiss hlam0 hsurj0 lam
                    (x : E) - A x‖ := one_mul _
        _ ≤ ε / (h + 1) := by
            have e : ε / (2 * (h + 1)) + ε / (2 * (h + 1))
                = ε / (h + 1) := by
              rw [← add_div, show ε + ε = 2 * ε by ring,
                mul_div_mul_left _ _
                  (show (2 : ℝ) ≠ 0 by norm_num)]
            linarith [hdY, e]
    · rw [sub_zero, abs_of_nonneg hh]
      by_cases hh0 : h = 0
      · rw [hh0, mul_zero]
        exact hε
      · have hpos : (0 : ℝ) < h + 1 := by linarith
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
        exact mul_lt_mul_of_pos_left (by linarith) hε
  have hRHS : Tendsto (fun lam => (expSemigroup
      (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun h (x : E)
        - (x : E)) atTop
      (𝓝 (∫ s in 0..h, (lpSemigroup D A hdiss hdense
        hlam0 hsurj0).toFun s (A x))) := by
    refine (tendsto_congr' ?_).mpr hInt
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with lam
      hlam
    exact lpIntegral_identity_approx D A hdiss hlam0
      hsurj0 x (lt_of_lt_of_le one_pos hlam) hh
  exact tendsto_nhds_unique hLHS hRHS

/-- Every domain point is a generator point of the
Lumer–Phillips semigroup, with the prescribed value. -/
theorem lpSemigroup_hasGen (x : D) :
    (lpSemigroup D A hdiss hdense hlam0 hsurj0).HasGen
      (x : E) (A x) := by
  show Tendsto (fun h => h⁻¹ • ((lpSemigroup D A hdiss
    hdense hlam0 hsurj0).toFun h (x : E) - (x : E)))
    (𝓝[>] 0) (𝓝 (A x))
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcw : ContinuousWithinAt
      (fun s => (lpSemigroup D A hdiss hdense hlam0
        hsurj0).toFun s (A x)) (Set.Ici 0) 0 :=
    (lpSemigroup D A hdiss hdense hlam0
      hsurj0).strongly_continuous (A x) 0
      (Set.mem_Ici.mpr le_rfl)
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδ'⟩ := hcw (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {h} hhI hdist => ?_⟩
  have hh0 : 0 < h := hhI
  have hhδ : h < δ := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hh0] at hdist
  have hS0 : (lpSemigroup D A hdiss hdense hlam0
      hsurj0).toFun 0 (A x) = A x :=
    C0Semigroup.map_zero_apply _ _
  have hbound : ∀ s ∈ Set.Ioc 0 h,
      ‖(lpSemigroup D A hdiss hdense hlam0 hsurj0).toFun s
        (A x) - A x‖ ≤ ε / 2 := by
    intro s hs
    have hsδ : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
      exact lt_of_le_of_lt hs.2 hhδ
    have h2 := hδ' (Set.mem_Ici.mpr hs.1.le) hsδ
    rw [hS0, dist_eq_norm] at h2
    exact h2.le
  have hint2 : IntervalIntegrable
      (fun s => (lpSemigroup D A hdiss hdense hlam0
        hsurj0).toFun s (A x)) MeasureTheory.volume 0 h :=
    ((lpSemigroup D A hdiss hdense hlam0
      hsurj0).strongly_continuous (A x)).mono
      (uIcc_zero_subset_Ici hh0.le) |>.intervalIntegrable
  have hsub : (∫ s in 0..h, ((lpSemigroup D A hdiss
        hdense hlam0 hsurj0).toFun s (A x) - A x))
      = (∫ s in 0..h, (lpSemigroup D A hdiss hdense hlam0
        hsurj0).toFun s (A x)) - (h - 0) • A x := by
    rw [← intervalIntegral.integral_const (A x)]
    exact intervalIntegral.integral_sub hint2
      intervalIntegrable_const
  have hdiff : h⁻¹ • ((lpSemigroup D A hdiss hdense hlam0
        hsurj0).toFun h (x : E) - (x : E)) - A x
      = h⁻¹ • (∫ s in 0..h, ((lpSemigroup D A hdiss
        hdense hlam0 hsurj0).toFun s (A x) - A x)) := by
    rw [lpIntegral_identity D A hdiss hdense hlam0 hsurj0
      x hh0.le, hsub, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hh0.ne', one_smul]
  rw [dist_eq_norm, hdiff, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hh0.le)]
  calc h⁻¹ * ‖∫ s in 0..h, ((lpSemigroup D A hdiss hdense
        hlam0 hsurj0).toFun s (A x) - A x)‖
      ≤ h⁻¹ * ((ε / 2) * |h - 0|) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s hs => hbound s (by
              rwa [Set.uIoc_of_le hh0.le] at hs)))
          (inv_nonneg.mpr hh0.le)
    _ = ε / 2 := by
        rw [sub_zero, abs_of_nonneg hh0.le,
          show h⁻¹ * ((ε / 2) * h) = (ε / 2) * (h⁻¹ * h) by
            ring, inv_mul_cancel₀ hh0.ne', mul_one]
    _ < ε := by linarith

/-- The generator value of the Lumer–Phillips semigroup
agrees with `A` on the domain. -/
theorem lpSemigroup_genVal (x : D)
    (hx : (x : E) ∈ (lpSemigroup D A hdiss hdense hlam0
      hsurj0).genDom) :
    (lpSemigroup D A hdiss hdense hlam0 hsurj0).genVal hx
      = A x :=
  (lpSemigroup D A hdiss hdense hlam0
    hsurj0).hasGen_unique
    ((lpSemigroup D A hdiss hdense hlam0
      hsurj0).hasGen_genVal hx)
    (lpSemigroup_hasGen D A hdiss hdense hlam0 hsurj0 x)

/-- The generator domain of the Lumer–Phillips semigroup
is exactly `D`. -/
theorem lpSemigroup_genDom_eq :
    (lpSemigroup D A hdiss hdense hlam0 hsurj0).genDom
      = D := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := (lpSemigroup D A hdiss hdense hlam0
      hsurj0).mem_genDom.mp hx
    obtain ⟨u, hu⟩ := hsurj0 (lam0 • x - y)
    have hgen : (lpSemigroup D A hdiss hdense hlam0
        hsurj0).HasGen (x - (u : E)) (y - A u) := by
      have h1 := (lpSemigroup D A hdiss hdense hlam0
        hsurj0).hasGen_add hy ((lpSemigroup D A hdiss
        hdense hlam0 hsurj0).hasGen_smul (-1)
        (lpSemigroup_hasGen D A hdiss hdense hlam0 hsurj0
          u))
      have h2 : x - (u : E) = x + (-1 : ℝ) • (u : E) := by
        rw [sub_eq_add_neg, neg_smul, one_smul]
      have h3 : y - A u = y + (-1 : ℝ) • A u := by
        rw [sub_eq_add_neg, neg_smul, one_smul]
      rw [h2, h3]
      exact h1
    have hdiss' := gen_diss_bound
      (lpSemigroup D A hdiss hdense hlam0 hsurj0)
      (fun t ht => lpOp_opNorm_le D A hdiss hdense hlam0
        hsurj0 ht) hgen hlam0
    have h2 : lamSub D A lam0 u
        = lam0 • (u : E) - A u := lamSub_apply D A lam0 u
    have hu' : lam0 • (u : E) - A u = lam0 • x - y := by
      rw [← h2]; exact hu
    have hzero : lam0 • (x - (u : E)) - (y - A u) = 0 := by
      rw [smul_sub]
      have e : (lam0 • x - lam0 • (u : E)) - (y - A u)
          = (lam0 • x - y) - (lam0 • (u : E) - A u) := by
        abel
      rw [e, hu', sub_self]
    rw [hzero, norm_zero] at hdiss'
    have hnorm0 : ‖x - (u : E)‖ = 0 := by
      have h5 : lam0 * ‖x - (u : E)‖ = 0 :=
        le_antisymm hdiss'
          (mul_nonneg hlam0.le (norm_nonneg _))
      exact (mul_eq_zero.mp h5).resolve_left
        (ne_of_gt hlam0)
    have hxu : x = (u : E) := by
      have h3 : x - (u : E) = 0 := by
        simpa using hnorm0
      exact eq_of_sub_eq_zero h3
    rw [hxu]
    exact u.prop
  · intro x hx
    refine (lpSemigroup D A hdiss hdense hlam0
      hsurj0).mem_genDom.mpr ⟨A ⟨x, hx⟩, ?_⟩
    exact lpSemigroup_hasGen D A hdiss hdense hlam0
      hsurj0 ⟨x, hx⟩

/-- The resolvent family of `A` is the resolvent family
of the Lumer–Phillips semigroup, at every `lam > 0`, in
the sense of `SHELF-1a`'s `ResolventSpec`. -/
theorem lpSemigroup_resolventSpec {lam : ℝ} (hlam : 0 < lam) :
    ResolventSpec
      (lpSemigroup D A hdiss hdense hlam0 hsurj0) lam
      (resolventFam D A hdiss hlam0 hsurj0 lam) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hmem : x ∈ D :=
      (lpSemigroup_genDom_eq D A hdiss hdense hlam0
        hsurj0) ▸ hx
    have hgv : (lpSemigroup D A hdiss hdense hlam0
        hsurj0).genVal hx = A ⟨x, hmem⟩ :=
      lpSemigroup_genVal D A hdiss hdense hlam0 hsurj0
        ⟨x, hmem⟩ hx
    rw [hgv]
    show (resolventFam D A hdiss hlam0 hsurj0 lam)
        (lamSub D A lam ⟨x, hmem⟩) = x
    exact (resolventFam_hasResolventAt D A hdiss hlam0
      hsurj0 hlam).1 ⟨x, hmem⟩
  · intro y
    obtain ⟨hmem, hlamSub⟩ :=
      (resolventFam_hasResolventAt D A hdiss hlam0 hsurj0
        hlam).2 y
    have hmem' : (resolventFam D A hdiss hlam0 hsurj0
        lam) y ∈ (lpSemigroup D A hdiss hdense hlam0
        hsurj0).genDom :=
      (lpSemigroup_genDom_eq D A hdiss hdense hlam0
        hsurj0).symm ▸ hmem
    refine ⟨hmem', ?_⟩
    have hgv : (lpSemigroup D A hdiss hdense hlam0
        hsurj0).genVal hmem'
        = A ⟨(resolventFam D A hdiss hlam0 hsurj0 lam) y,
          hmem⟩ :=
      lpSemigroup_genVal D A hdiss hdense hlam0 hsurj0
        ⟨(resolventFam D A hdiss hlam0 hsurj0 lam) y, hmem⟩
        hmem'
    rw [hgv]
    exact (lamSub_apply D A lam
      ⟨(resolventFam D A hdiss hlam0 hsurj0 lam) y,
        hmem⟩).symm.trans hlamSub

/-- Discharge of `SHELF-1a`'s `hlim` hypothesis for the
Lumer–Phillips class: `lam • R(lam) z -> z` for every
`z`. -/
theorem lpResolvent_smul_tendsto
    (hdense : Dense (↑D : Set E)) (z : E) :
    Tendsto (fun lam => lam • resolventFam D A hdiss
      hlam0 hsurj0 lam z) atTop (𝓝 z) :=
  resolvent_smul_tendsto D A hdense
    (resolventFam D A hdiss hlam0 hsurj0)
    (fun lam hlam => resolventFam_hasResolventAt D A
      hdiss hlam0 hsurj0 hlam)
    (fun lam hlam => resolventFam_opNorm_le D A hdiss
      hlam0 hsurj0 hlam) z

/-- `SHELF-1a`'s Yosida convergence theorem, discharged
for the Lumer–Phillips semigroup: its hypotheses
(`ResolventSpec` at every `lam > 0`, and `hlim`) are
theorems here. -/
theorem lpYosidaApprox_tendsto_on_genDom {x : E}
    (hx : x ∈ (lpSemigroup D A hdiss hdense hlam0
      hsurj0).genDom) :
    Tendsto (fun lam => yosidaApprox
      (lpSemigroup D A hdiss hdense hlam0 hsurj0) lam
      (resolventFam D A hdiss hlam0 hsurj0 lam) x) atTop
      (𝓝 ((lpSemigroup D A hdiss hdense hlam0
        hsurj0).genVal hx)) :=
  yosidaApprox_tendsto
    (lpSemigroup D A hdiss hdense hlam0 hsurj0)
    (resolventFam D A hdiss hlam0 hsurj0)
    (fun lam hlam => lpSemigroup_resolventSpec D A hdiss
      hdense hlam0 hsurj0 hlam)
    (fun z => lpResolvent_smul_tendsto D A hdiss hlam0
      hsurj0 hdense z) hx

/-- Discharge of `SHELF-1a`'s Yosida-approximation
remainder for the Lumer–Phillips class: the exponential
semigroups of the Yosida approximants converge to the
constructed semigroup, for every `t >= 0` and every
vector. -/
theorem lpYosidaApprox_exp_tendsto {t : ℝ} (ht : 0 ≤ t)
    (z : E) :
    Tendsto (fun lam => (expSemigroup (yosidaApprox
      (lpSemigroup D A hdiss hdense hlam0 hsurj0) lam
      (resolventFam D A hdiss hlam0 hsurj0 lam))).toFun
      t z) atTop
      (𝓝 ((lpSemigroup D A hdiss hdense hlam0
        hsurj0).toFun t z)) := by
  have hcong : (fun lam => (expSemigroup (yosidaApprox
      (lpSemigroup D A hdiss hdense hlam0 hsurj0) lam
      (resolventFam D A hdiss hlam0 hsurj0 lam))).toFun
      t z)
      = (fun lam => (expSemigroup
        (lpYosida D A hdiss hlam0 hsurj0 lam)).toFun
        t z) := by
    funext lam
    have hCLM : yosidaApprox
        (lpSemigroup D A hdiss hdense hlam0 hsurj0) lam
        (resolventFam D A hdiss hlam0 hsurj0 lam)
        = lpYosida D A hdiss hlam0 hsurj0 lam := rfl
    rw [hCLM]
  rw [hcong]
  exact lpOp_tendsto D A hdiss hdense hlam0 hsurj0 ht z

end LPGenerator

/-- Sequential graph-closedness of `A` for the
Lumer–Phillips class: if `u n` are domain points with
`u n -> x` and `A (u n) -> y`, then `x` is in the domain
and `A x = y`. (Read off the resolvent at `1`: the
resolvent identity propagates the two convergences to
`x = R(1) (x - y)`.) -/
theorem lpClosedGraph (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hdiss : DissBound D A) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0))
    {u : ℕ → D} {x y : E}
    (hx : Tendsto (fun n => ((u n : E))) atTop (𝓝 x))
    (hy : Tendsto (fun n => A (u n)) atTop (𝓝 y)) :
    ∃ x' : D, (x' : E) = x ∧ A x' = y := by
  obtain ⟨hmem, hlamSub⟩ :=
    (resolventFam_hasResolventAt D A hdiss hlam0 hsurj0
      (lam := 1) one_pos).2 (x - y)
  set w : E := (resolventFam D A hdiss hlam0 hsurj0 1)
    (x - y) with hw
  have hlim : Tendsto
      (fun n => (resolventFam D A hdiss hlam0 hsurj0 1)
        ((1 : ℝ) • ((u n : E)) - A (u n))) atTop
        (𝓝 w) := by
    have harg : Tendsto
        (fun n => (1 : ℝ) • ((u n : E)) - A (u n)) atTop
        (𝓝 ((1 : ℝ) • x - y)) := (hx.const_smul 1).sub hy
    have h2 := ((resolventFam D A hdiss hlam0 hsurj0
      1).continuous.tendsto ((1 : ℝ) • x - y)).comp harg
    simpa only [one_smul, Function.comp_def] using h2
  have hlim2 : Tendsto (fun n => ((u n : E))) atTop
      (𝓝 w) := by
    have e : ∀ n, (resolventFam D A hdiss hlam0 hsurj0 1)
        ((1 : ℝ) • ((u n : E)) - A (u n)) = ((u n : E)) := by
      intro n
      rw [← lamSub_apply D A 1 (u n)]
      exact (resolventFam_hasResolventAt D A hdiss hlam0
        hsurj0 one_pos).1 (u n)
    exact hlim.congr (fun n => e n)
  have hxw : x = w := tendsto_nhds_unique hx hlim2
  refine ⟨⟨w, hmem⟩, hxw.symm, ?_⟩
  have hlam2 : lamSub D A 1 ⟨w, hmem⟩ = x - y := hlamSub
  rw [lamSub_apply, one_smul] at hlam2
  have hcoe : ((⟨w, hmem⟩ : D) : E) = w := rfl
  rw [hcoe, hxw] at hlam2
  calc A ⟨w, hmem⟩ = w - (w - A ⟨w, hmem⟩) := by abel
    _ = w - (w - y) := by rw [hlam2]
    _ = y := by abel

/-! ## Headlines -/

/-- **Lumer–Phillips (contraction case).** Let `A` be a
densely defined operator on a real Banach space `E`,
dissipative in the resolvent-bound form `DissBound`
(`lam * ‖x‖ ≤ ‖lam • x - A x‖` for all `lam > 0` and all
`x` in the domain), and suppose `lam0 - A` is surjective
for some `lam0 > 0`. Then `A` is the generator of a
contraction `C0Semigroup`: there is a strongly
continuous semigroup of contractions whose generator
domain is exactly `D` and whose generator value at
every `x : D` is `A x`. -/
theorem lumer_phillips (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hdiss : DissBound D A)
    (hdense : Dense (↑D : Set E)) {lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hsurj0 : Function.Surjective (lamSub D A lam0)) :
    ∃ S : C0Semigroup E,
      (∀ t : ℝ, 0 ≤ t → ‖S.toFun t‖ ≤ 1)
      ∧ S.genDom = D
      ∧ ∀ x : D, S.HasGen (x : E) (A x) :=
  ⟨lpSemigroup D A hdiss hdense hlam0 hsurj0,
    fun t ht => lpOp_opNorm_le D A hdiss hdense hlam0
      hsurj0 ht,
    lpSemigroup_genDom_eq D A hdiss hdense hlam0 hsurj0,
    fun x => lpSemigroup_hasGen D A hdiss hdense hlam0
      hsurj0 x⟩

/-- **Hille–Yosida (contraction case).** Let `A` be a
densely defined operator on a real Banach space `E`
equipped with a resolvent family `R` defined at every
`lam > 0` (in the two-sided sense of `HasResolventAt`)
satisfying the Hille–Yosida power bounds
`‖R(lam)^n‖ ≤ lam^{-n}` for all `n`. Then `A` generates
a contraction `C0Semigroup`. (Only the `n = 1` bound
and surjectivity at `lam = 1` are consumed: the `n = 1`
bounds at all `lam > 0` give dissipativity, and the
conclusion follows from Lumer–Phillips.) -/
theorem hille_yosida_contraction (D : Submodule ℝ E)
    (A : D →ₗ[ℝ] E) (hdense : Dense (↑D : Set E))
    (R : ℝ → (E →L[ℝ] E))
    (hR : ∀ lam : ℝ, 0 < lam →
      HasResolventAt D A lam (R lam))
    (hpow : ∀ (lam : ℝ), 0 < lam → ∀ n : ℕ,
      ‖(R lam) ^ n‖ ≤ (lam⁻¹) ^ n) :
    ∃ S : C0Semigroup E,
      (∀ t : ℝ, 0 ≤ t → ‖S.toFun t‖ ≤ 1)
      ∧ S.genDom = D
      ∧ ∀ x : D, S.HasGen (x : E) (A x) := by
  have hdiss : DissBound D A := by
    intro lam hlam x
    have h1 : (R lam) (lamSub D A lam x) = (x : E) :=
      (hR lam hlam).1 x
    have hnorm : ‖(x : E)‖ ≤ lam⁻¹ * ‖lamSub D A lam x‖ := by
      calc ‖(x : E)‖ = ‖(R lam) (lamSub D A lam x)‖ := by
            rw [h1]
        _ ≤ ‖R lam‖ * ‖lamSub D A lam x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ lam⁻¹ * ‖lamSub D A lam x‖ :=
            mul_le_mul_of_nonneg_right
              (by
                have h := hpow lam hlam 1
                simpa using h) (norm_nonneg _)
    have h2 : lam * ‖(x : E)‖
        ≤ lam * (lam⁻¹ * ‖lamSub D A lam x‖) :=
      mul_le_mul_of_nonneg_left hnorm hlam.le
    rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul,
      lamSub_apply] at h2
    exact h2
  have hsurj : Function.Surjective (lamSub D A 1) := by
    intro y
    obtain ⟨hmem, hlamSub⟩ := (hR 1 one_pos).2 y
    exact ⟨⟨(R 1) y, hmem⟩, hlamSub⟩
  exact lumer_phillips D A hdiss hdense one_pos hsurj
