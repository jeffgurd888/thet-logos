/-
# SHELF-13 - SELF-ADJOINTNESS CRITERIA (Kato-Rellich seats)

Working label: SHELF-13 (shelf map row: "self-adjointness
criteria - Kato-Rellich type perturbation criteria and
deficiency-index criteria at the seats where they are
statable"). This is a general analysis fill: it moves no
dial, closes no posted question, and asserts NO CLAIM
beyond its theorems.

## Step 0 - probe inventory (pin: Mathlib v4.35.0-rc3)

Checked by direct search of the pinned Mathlib tree and
the corpus tree:

* Kato-Rellich: NO occurrence of "Rellich" anywhere in
  the pinned Mathlib's Analysis / LinearAlgebra trees, and
  no Kato-Rellich theorem in the corpus (the corpus's
  "Kato" occurrences are Kato's FIRST REPRESENTATION
  theorem - the SHELF-2 Friedrichs module - and one
  BosonicInteraction header note recording that its route
  is "not a Mathlib Kato-Rellich or analytic-vector
  criterion"). Deficiency indices: NO occurrence in the
  pin or the corpus. This brick is therefore a FILL, not
  a strike.
* Unbounded-operator API: PRESENT in the pin (contra the
  pack's expectation) - `LinearPMap` with graph adjoint
  `T†`, `LinearPMap.IsFormalAdjoint`,
  `LinearPMap.adjoint_isFormalAdjoint`,
  `LinearPMap.IsFormalAdjoint.le_adjoint`,
  `LinearPMap.adjoint_apply_eq`,
  `LinearPMap.mem_adjoint_domain_of_exists`,
  `LinearPMap.isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A`,
  and `IsSelfAdjoint.dense_domain`. So the unbounded seat
  is statable; what the pin lacks is the RESOLVENT
  MACHINERY the classical unbounded Kato-Rellich proof
  runs on (bounds `‖A(A + iμ)⁻¹‖ ≤ 1`,
  `‖(A + iμ)⁻¹‖ ≤ 1/|μ|` for a general self-adjoint
  `LinearPMap`, a Neumann-series inversion at that seat).
  The unbounded form therefore lands at the seat the pin
  supports - a BOUNDED perturbation of an unbounded
  self-adjoint operator, which is exactly the relative-
  bound case `a = 0 < 1` - and the general relative-bound
  form (`0 < a < 1`, `B` itself unbounded) is the named
  PARTIAL seam of this brick (see the seam statement in
  the §2 header).
* Corpus self-adjointness vocabulary consumed, cited not
  redone: SHELF-2's `ThetLogos/FriedrichsExtension.lean`
  (the Friedrichs module; `friedrichsOperator`,
  `friedrichsOperator_isSelfAdjoint` in the `LinearPMap`
  graph dialect; its bounded resolvent
  `friedrichsResolvent_isSelfAdjoint` in the `→L` dialect);
  `ThetLogos/BosonicESA.lean` (symmetric `LinearPMap`
  package: closability, `closure ≤ adjoint`, the ESA
  restatements - the criteria below are perturbation /
  everywhere-defined criteria, NOT the closure route, and
  nothing here reproves or upgrades `BosonicESA`);
  the Dirac seats own `IsSelfAdjoint` directly for their
  finite operators (e.g. `cycleDirac_selfAdjoint`,
  `InnerFluctuations`' fluctuated Dirac, the
  `FiniteSpectralTriple` / `ConnesDistancePost` seats) -
  cited as prior art, not redone; SHELF-3a's
  `HilbertSchmidt` / `IntegralKernelHS` material is
  adjacent (bounded seats) and not needed here.

## What it delivers

* §1 (bounded seat, FULL): the Kato-Rellich statement at
  the everywhere-defined bounded seat - a self-adjoint
  bounded operator plus a symmetric bounded perturbation
  is self-adjoint, with the classical relative-bound
  hypothesis (`a < 1`) recorded in the form the seat
  carries (at this seat it is not needed, and the proof
  honestly does not use it: every bounded symmetric `B`
  works, because both operators are everywhere defined).
* §2 (unbounded seat, the pin-supported Kato-Rellich
  case): `A` self-adjoint as a `LinearPMap`, `B` bounded
  self-adjoint - the sum on `D(A)` is self-adjoint in the
  graph dialect (`IsSelfAdjoint (pmapAddBounded A B)`),
  with the relative bound at `a = 0`:
  `‖Bx‖ ≤ 0 * ‖Ax‖ + ‖B‖ * ‖x‖`. Domain statement:
  `D(A + B) = D(A)` by construction, and self-adjointness
  gives `D((A+B)†) = D(A)` - a domain equality for the
  PERTURBED operator only.
* §3 (finite / everywhere-defined seats): an everywhere-
  defined symmetric `LinearPMap` is self-adjoint (pure
  graph argument, any dimension); hence a symmetric plain
  linear map is self-adjoint as a `LinearPMap` on the top
  domain. At finite-dimensional complex seats the
  deficiency spaces vanish in the finite form that seat
  carries: `ker (T ∓ i) = ⊥` and `range (T - i) = ⊤` for
  a symmetric `T` (deficiency indices are `(0, 0)`,
  stated as kernel/range facts since the pin has no
  deficiency-index vocabulary).
* §4 (read-backs): the bridge graph Laplacian `lapLin w`
  (`ThetLogos/BridgeCompletion.lean`, which owns symmetry
  only in the `LinearMap.IsSymmetric` dialect) is
  re-derived as graph-dialect self-adjointness through
  §3; and the SHELF-2 Friedrichs operator perturbed by
  any bounded self-adjoint operator is self-adjoint
  through §2.

## Seam / fence notes

* PARTIAL seam (named): the classical unbounded
  Kato-Rellich theorem with a genuinely unbounded
  perturbation `B`, `D(A) ⊆ D(B)`,
  `‖Bx‖ ≤ a‖Ax‖ + b‖x‖`, `0 < a < 1`, is NOT proved
  here. The `LinearPMap` dialect to STATE it exists; the
  missing pin input is the resolvent estimate /
  Neumann-series inversion for general self-adjoint
  `LinearPMap`s described in Step 0. §2 is exactly its
  `a = 0` case.
* SHELF-2 Seam A interaction (NOT closed here, by pack
  order): Seam A is the Friedrichs square-root domain
  equality `D(S) = D(t)` (`range √R = range J`). Nothing
  in this module touches the square root, `√R`, or that
  equality. §2's domain equality `D((A+B)†) = D(A+B)` is
  a statement about the perturbed operator of §2 only;
  it neither uses nor implies Seam A, and Seam A remains
  open exactly as SHELF-2 left it.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Symmetric
import ThetLogos.BridgeCompletion
import ThetLogos.FriedrichsExtension

namespace ThetLogos

open scoped LinearPMap

section BoundedSeat

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-! ## §1. The bounded seat: Kato-Rellich where both
operators are everywhere defined and bounded -/

/-- **Bounded perturbation criterion (bounded seat).** A
self-adjoint bounded operator plus a symmetric bounded
perturbation is self-adjoint. At this seat symmetry of
`B` already gives `IsSelfAdjoint B`
(`LinearMap.IsSymmetric.isSelfAdjoint`), and
self-adjointness is closed under addition. -/
theorem clm_isSelfAdjoint_add_of_isSymmetric
    {A B : H →L[𝕜] H} (hA : IsSelfAdjoint A)
    (hB : (B : H →ₗ[𝕜] H).IsSymmetric) :
    IsSelfAdjoint (A + B) :=
  hA.add hB.isSelfAdjoint

/-- **Kato-Rellich, bounded-seat form.** The classical
statement with its relative-bound hypothesis
`‖Bx‖ ≤ a‖Ax‖ + b‖x‖`, `a < 1`, recorded in the form the
bounded seat carries. Honest note: at the everywhere-
defined bounded seat the bound is NOT needed for the
conclusion (any symmetric bounded `B` works, by
`clm_isSelfAdjoint_add_of_isSymmetric`); the `< 1`
hypothesis becomes essential only when `A` is unbounded,
the seat of §2, where it is used at `a = 0`. The
hypotheses `hrel` / `ha` are therefore carried but
deliberately unused. -/
theorem katoRellich_bounded_seat
    {A B : H →L[𝕜] H} (hA : IsSelfAdjoint A)
    (hB : (B : H →ₗ[𝕜] H).IsSymmetric)
    {a b : ℝ} (_hrel : ∀ x : H, ‖B x‖ ≤ a * ‖A x‖ + b * ‖x‖)
    (_ha : a < 1) :
    IsSelfAdjoint (A + B) :=
  clm_isSelfAdjoint_add_of_isSymmetric hA hB

end BoundedSeat

section UnboundedSeat

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-! ## §2. The unbounded seat: a bounded perturbation of
a self-adjoint `LinearPMap` (Kato-Rellich at `a = 0`)

PARTIAL SEAM (named, see the module header): the general
relative-bound form with `B` unbounded and `0 < a < 1`
is not proved - the pin has no resolvent estimates for
general self-adjoint `LinearPMap`s. Everything below is
the bounded-perturbation case, proved in full. -/

/-- The sum of a partially defined operator `A` and a
bounded operator `B`: domain `D(A)`, value
`Ax + Bx`. -/
def pmapAddBounded (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) :
    H →ₗ.[𝕜] H where
  domain := A.domain
  toFun := A.toFun + (B : H →ₗ[𝕜] H).comp A.domain.subtype

theorem pmapAddBounded_domain (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) :
    (pmapAddBounded A B).domain = A.domain :=
  rfl

theorem pmapAddBounded_apply (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (x : (pmapAddBounded A B).domain) :
    pmapAddBounded A B x = A x + B (x : H) :=
  rfl

/-- The domain of the perturbed operator is dense when
`A` is self-adjoint (its domain is `D(A)`). -/
theorem pmapAddBounded_dense_domain
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A) (B : H →L[𝕜] H) :
    Dense ((pmapAddBounded A B).domain : Set H) :=
  hA.dense_domain

/-- Symmetry of a bounded self-adjoint operator, in
pairing form. -/
theorem clm_inner_apply_symm {B : H →L[𝕜] H}
    (hB : IsSelfAdjoint B) (a b : H) :
    inner 𝕜 (B a) b = inner 𝕜 a (B b) :=
  hB.isSymmetric a b

/-- **The relative bound at `a = 0`.** A bounded
perturbation satisfies the Kato-Rellich relative-bound
estimate with relative bound `0` (and `b = ‖B‖`):
`‖Bx‖ ≤ 0 * ‖Ax‖ + ‖B‖ * ‖x‖` on the domain of `A`. -/
theorem pmapAddBounded_relative_bound_zero
    (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (x : (pmapAddBounded A B).domain) :
    ‖B (x : H)‖ ≤ 0 * ‖A x‖ + ‖B‖ * ‖(x : H)‖ := by
  have h := ContinuousLinearMap.le_opNorm B (x : H)
  simpa only [zero_mul, zero_add] using h

/-- **Symmetry of the sum.** If `A` is self-adjoint as a
`LinearPMap` and `B` is bounded self-adjoint, then
`A + B` is a formal adjoint of itself. -/
theorem pmapAddBounded_isFormalAdjoint_self
    {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (pmapAddBounded A B).IsFormalAdjoint (pmapAddBounded A B) := by
  have hAform : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint
      (T := A) hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  intro x y
  rw [pmapAddBounded_apply, pmapAddBounded_apply,
    inner_add_left, inner_add_right, hAform x y,
    clm_inner_apply_symm hB (x : H) (y : H)]

/-- **The adjoint-domain lemma for the sum.** Every `y`
in the domain of `(A + B)†` is already in `D(A + B)`
(= `D(A)`), with `(A + B) y = (A + B)† y` there. The
proof is the pairing trick: subtracting the bounded part
moves the adjoint relation for `A + B` to an adjoint
relation for `A`, and self-adjointness of `A` closes it;
concretely `A y = (A + B)† y - B y` at the transported
domain element. -/
theorem pmapAddBounded_adjoint_apply
    {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (y : (pmapAddBounded A B)†.domain) :
    ∃ x : (pmapAddBounded A B).domain,
      x.1 = y.1 ∧ pmapAddBounded A B x
        = (pmapAddBounded A B)† y := by
  have hdense : Dense ((pmapAddBounded A B).domain : Set H) :=
    pmapAddBounded_dense_domain hA B
  have hpair : ∀ a : (pmapAddBounded A B).domain,
      inner 𝕜 ((pmapAddBounded A B)† y - B (y : H)) a
        = inner 𝕜 (y : H) (A a) := by
    intro a
    have hadj := LinearPMap.adjoint_isFormalAdjoint
      (T := pmapAddBounded A B) hdense y a
    rw [inner_sub_left, hadj, pmapAddBounded_apply,
      inner_add_right, clm_inner_apply_symm hB (y : H) (a : H),
      add_sub_cancel_right]
  have hyA : (y : H) ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists (T := A) (y : H)
      ⟨(pmapAddBounded A B)† y - B (y : H), hpair⟩
  have hval : A† ⟨(y : H), hyA⟩
      = (pmapAddBounded A B)† y - B (y : H) :=
    LinearPMap.adjoint_apply_eq hA.dense_domain
      ⟨(y : H), hyA⟩ hpair
  have hdom : A†.domain = A.domain :=
    congrArg LinearPMap.domain
      (LinearPMap.isSelfAdjoint_def.mp hA)
  have hy : (y : H) ∈ A.domain := by
    rwa [hdom] at hyA
  have hswap : A† ⟨(y : H), hyA⟩ = A ⟨(y : H), hy⟩ :=
    (le_of_eq (LinearPMap.isSelfAdjoint_def.mp hA)).2 rfl
  refine ⟨⟨(y : H), hy⟩, rfl, ?_⟩
  rw [pmapAddBounded_apply]
  have hgoal : A ⟨(y : H), hy⟩ + B (y : H)
      = (pmapAddBounded A B)† y := by
    rw [← hswap, hval, sub_add_cancel]
  exact hgoal

/-- `T† ≤ T` for the sum: the adjoint-domain lemma in the
order dialect. -/
theorem pmapAddBounded_adjoint_le
    {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (pmapAddBounded A B)† ≤ pmapAddBounded A B := by
  constructor
  · intro y hy
    obtain ⟨x, hx, -⟩ := pmapAddBounded_adjoint_apply hA hB
      ⟨y, hy⟩
    have hx' : x.1 = y := hx
    rw [← hx']
    exact x.2
  · intro x y hxy
    obtain ⟨u, hu1, hu2⟩ := pmapAddBounded_adjoint_apply hA hB x
    have hy : y = u := Subtype.ext (hxy.symm.trans hu1.symm)
    rw [hy]
    exact hu2.symm

/-- **KATO-RELLICH, BOUNDED-PERTURBATION FORM (the seat
the pin supports).** If `A` is self-adjoint as a
partially defined operator (`LinearPMap` graph dialect)
and `B` is a bounded self-adjoint operator, then the sum
`A + B` on `D(A)` is self-adjoint. This is the classical
Kato-Rellich theorem at relative bound `a = 0` (the
bound is `pmapAddBounded_relative_bound_zero`); the
general `0 < a < 1` unbounded-`B` form is the named
PARTIAL seam of the module header. -/
theorem katoRellich_bounded_perturbation
    {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (pmapAddBounded A B) := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (pmapAddBounded_adjoint_le hA hB)
    ((pmapAddBounded_isFormalAdjoint_self hA hB).le_adjoint
      (pmapAddBounded_dense_domain hA B))

end UnboundedSeat

section FiniteSeat

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-! ## §3. Finite / everywhere-defined seats -/

/-- **Everywhere-defined criterion.** A symmetric
partially defined operator whose domain is the whole
space is self-adjoint: symmetry gives `T ≤ T†`, and
`T† ≤ T` is then forced - the adjoint's domain cannot
exceed `⊤ = D(T)`, and the two agree on the domain of
`T`, which is everything. Pure graph argument; no
finite-dimensionality or continuity is used. -/
theorem everywhereDefined_symmetric_isSelfAdjoint
    {T : H →ₗ.[𝕜] H} (hdom : T.domain = ⊤)
    (hsymm : T ≤ T†) :
    IsSelfAdjoint T := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hdom' : T.domain = T†.domain := by
    apply le_antisymm
    · exact hsymm.1
    · rw [hdom]
      exact le_top
  have hle : T† ≤ T := by
    constructor
    · intro y _
      rw [hdom]
      exact Submodule.mem_top
    · intro x y hxy
      exact (hsymm.2 hxy.symm).symm
  exact LinearPMap.eq_of_le_of_domain_eq hle hdom'.symm

/-- **Finite-seat criterion, linear-map form.** A
symmetric plain linear map (in particular any symmetric
operator at a finite-dimensional seat), packaged as a
`LinearPMap` on the top domain, is self-adjoint in the
graph dialect. The corpus previously owned such
operators' symmetry only (`LinearMap.IsSymmetric`); the
graph self-adjointness is the new form. -/
theorem linearMap_toPMap_isSelfAdjoint_of_isSymmetric
    (T : H →ₗ[𝕜] H) (hT : T.IsSymmetric) :
    IsSelfAdjoint (T.toPMap ⊤) := by
  apply everywhereDefined_symmetric_isSelfAdjoint
    (LinearMap.toPMap_domain T ⊤)
  apply LinearPMap.IsFormalAdjoint.le_adjoint
    (T := T.toPMap ⊤) (S := T.toPMap ⊤)
  · show Dense ((T.toPMap ⊤).domain : Set H)
    rw [LinearMap.toPMap_domain, Submodule.top_coe]
    exact dense_univ
  · intro x y
    show inner 𝕜 (T (x : H)) (y : H)
      = inner 𝕜 (x : H) (T (y : H))
    exact hT (x : H) (y : H)

end FiniteSeat

section DeficiencyFinite

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-! ## §3b. Deficiency vanishing at finite complex seats

The pin has no deficiency-index vocabulary; at a finite
seat the content of "deficiency indices `(0, 0)`" is the
pair of kernel facts below (for `T† = T`, which §3 gives
in `LinearPMap` form, the deficiency spaces
`ker (T† ∓ i)` are `ker (T ∓ i)`), plus surjectivity of
`T - i` (von Neumann's range criterion, which at a
finite seat follows from the kernel fact by dimension). -/

/-- Eigenvalue obstruction: a symmetric operator has no
eigenvector with non-real eigenvalue - if `Tx = c • x`
with `im c ≠ 0` then `x = 0`, by reality of
`⟪Tx, x⟫ = ⟪x, Tx⟫` read through `⟪x, x⟫ = ‖x‖²`. -/
theorem eq_zero_of_symmetric_eigenvalue_imag_ne_zero
    {T : Module.End ℂ E} (hT : T.IsSymmetric)
    {c : ℂ} (hc : c.im ≠ 0) {x : E} (hx : T x = c • x) :
    x = 0 := by
  have hself : (starRingEnd ℂ) c * (‖x‖ : ℂ) ^ 2
      = c * (‖x‖ : ℂ) ^ 2 := by
    have h := hT x x
    rw [hx, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K] at h
    exact h
  have hsub : ((starRingEnd ℂ) c - c) * (‖x‖ : ℂ) ^ 2
      = 0 := by
    rw [sub_mul, hself, sub_self]
  have hne : (starRingEnd ℂ) c - c ≠ 0 := by
    intro hcon
    have hcc : (starRingEnd ℂ) c = c := sub_eq_zero.mp hcon
    exact hc ((RCLike.conj_eq_iff_im (K := ℂ)).mp hcc)
  have hr : (‖x‖ : ℂ) = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hr)

/-- **Deficiency space at `+i` vanishes**:
`ker (T - i • 1) = ⊥` for a symmetric `T` at a
finite-dimensional complex seat. -/
theorem finite_symmetric_ker_sub_imag_eq_bot
    (T : Module.End ℂ E) (hT : T.IsSymmetric) :
    LinearMap.ker (T - Complex.I • (1 : Module.End ℂ E))
      = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  rw [LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hx
  exact eq_zero_of_symmetric_eigenvalue_imag_ne_zero hT
    (c := Complex.I) (by simp) hx

/-- **Deficiency space at `-i` vanishes**:
`ker (T + i • 1) = ⊥` for a symmetric `T` at a
finite-dimensional complex seat (written with
`T - (-i) • 1`). -/
theorem finite_symmetric_ker_add_imag_eq_bot
    (T : Module.End ℂ E) (hT : T.IsSymmetric) :
    LinearMap.ker (T - (-Complex.I) • (1 : Module.End ℂ E))
      = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  rw [LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hx
  exact eq_zero_of_symmetric_eigenvalue_imag_ne_zero hT
    (c := -Complex.I) (by simp) hx

/-- **Range criterion at the finite seat**:
`range (T - i • 1) = ⊤` - injectivity (the kernel fact
above) plus finite-dimensionality. This is von Neumann's
surjectivity criterion for self-adjointness, in the
finite form the seat carries. -/
theorem finite_symmetric_range_sub_imag_eq_top
    (T : Module.End ℂ E) (hT : T.IsSymmetric) :
    LinearMap.range (T - Complex.I • (1 : Module.End ℂ E))
      = ⊤ :=
  LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp
      (LinearMap.ker_eq_bot.mp
        (finite_symmetric_ker_sub_imag_eq_bot T hT)))

end DeficiencyFinite

section ReadBack

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## §4. Read-backs through the new criteria -/

/-- **Read-back 1 (finite seat, §3).** The bridge graph
Laplacian `lapLin w` of `ThetLogos.BridgeCompletion` -
owned there as symmetry in the `LinearMap.IsSymmetric`
dialect (`lapLin_isSymmetric`) - is self-adjoint in the
`LinearPMap` graph dialect, re-derived through the
finite-seat criterion
`linearMap_toPMap_isSelfAdjoint_of_isSymmetric`. -/
theorem lapLin_toPMap_isSelfAdjoint
    (w : W → W → ℝ) (hw : ∀ i j, w i j = w j i) :
    IsSelfAdjoint ((lapLin w).toPMap ⊤) :=
  linearMap_toPMap_isSelfAdjoint_of_isSymmetric
    (lapLin w) (lapLin_isSymmetric w hw)

/-- **Read-back 2 (unbounded seat, §2).** The SHELF-2
Friedrichs operator `friedrichsOperator J m hJinj hJle
hJdense` (self-adjoint by
`friedrichsOperator_isSelfAdjoint`), perturbed by any
bounded self-adjoint operator `B`, remains self-adjoint
- through the bounded-perturbation criterion
`katoRellich_bounded_perturbation`. This is a statement
about the perturbed operator only; it does not touch
SHELF-2's Seam A (the square-root domain equality
`D(S) = D(t)`), which remains open. -/
theorem friedrichsOperator_add_bounded_isSelfAdjoint
    (J : V →L[𝕜] H) (m : ℝ)
    (hJinj : Function.Injective J)
    (hJle : ∀ x : V, ‖J x‖ ≤ ‖x‖) (hJdense : DenseRange J)
    (B : H →L[𝕜] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint
      (pmapAddBounded
        (friedrichsOperator J m hJinj hJle hJdense) B) :=
  katoRellich_bounded_perturbation
    (friedrichsOperator_isSelfAdjoint J m hJinj hJle hJdense)
    hB

end ReadBack

#print axioms clm_isSelfAdjoint_add_of_isSymmetric
#print axioms katoRellich_bounded_seat
#print axioms pmapAddBounded_relative_bound_zero
#print axioms pmapAddBounded_isFormalAdjoint_self
#print axioms pmapAddBounded_adjoint_apply
#print axioms pmapAddBounded_adjoint_le
#print axioms katoRellich_bounded_perturbation
#print axioms everywhereDefined_symmetric_isSelfAdjoint
#print axioms linearMap_toPMap_isSelfAdjoint_of_isSymmetric
#print axioms eq_zero_of_symmetric_eigenvalue_imag_ne_zero
#print axioms finite_symmetric_ker_sub_imag_eq_bot
#print axioms finite_symmetric_ker_add_imag_eq_bot
#print axioms finite_symmetric_range_sub_imag_eq_top
#print axioms lapLin_toPMap_isSelfAdjoint
#print axioms friedrichsOperator_add_bounded_isSelfAdjoint

end ThetLogos
