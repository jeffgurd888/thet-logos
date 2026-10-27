import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic

namespace ThetLogos

open WeierstrassCurve Filter TensorProduct
open scoped Topology

/-!
# ThetLogos.BSDRankPin — the Birch–Swinnerton-Dyer rank equality, pinned as a `Prop`

Source: the BSD goal charter (`goals/birch-and-swinnerton-dyer-the-long-project`),
rung 1 (the statement pin), commissioned by Jeff 2026-10-27. Design authority: the
2026-10-19 BSD Mathlib audit — definitions first, analytic continuation carried as
an explicit labeled hypothesis, never hidden inside a definition.

**What this file IS.** A machine-checked *statement* of the rank half of the
Birch–Swinnerton-Dyer conjecture: for a nonsingular Weierstrass curve `E` over `ℚ`,
the order of vanishing at `s = 1` of its L-function equals the rank of its rational
point group. Following Wiles's Clay chapter, that equality *is* the Millennium
statement; the leading-coefficient formula (regulator, Sha, Tamagawa numbers) is
rung 2, a different project, and is absent here by design.

**What this file is NOT.** A proof of the conjecture, or progress toward one.
Parts of the official statement closed by this module: **0**. It pins the
statement; the pinned `Prop` `BSDRankEquality` is the conjecture itself and is
deliberately left unproved.

**Correction to the 2026-10-19 audit, found in this pin.** The audit reported
that Mathlib owns no elliptic-curve L-function. That is no longer true of
Mathlib v4.35.0-rc3: `WeierstrassCurve.LFunction` / `WeierstrassCurve.LSeries`
(`Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`, 2026) define the
formal Dirichlet series from local polynomials `1 - aT + qT²` with
`a = q + 1 - |W(κ)|`. What Mathlib still does *not* own: rank, Sha, regulator,
Tamagawa numbers, and — the point for this pin — analytic continuation of the
L-series to `s = 1`. The continuation therefore remains an explicit labeled
hypothesis below, exactly as the audit prescribed; only its target changed
(the hypothesis now names Mathlib's owned L-series).

**The labeled hypothesis (formalization debt).** `BSDAnalyticData E` is a
structure whose fields *are* the debt, on the statement's face: an integral
model, a holomorphic function `L : ℂ → ℂ`, and the agreement
`L s = E.LSeries s` on the convergence half-plane `Re s > 3/2`. In the
literature this package exists by modularity (settled mathematics); in this
pin it is unproved, and the prose says so. Caveat recorded with it: if no
such package existed for some `E`, the pin would be vacuous at that `E` —
existence of the package is part of the debt, not a theorem of this file.

**Fences and conventions.**
- The algebraic rank is *defined* as the finrank of `ℚ ⊗[ℤ] E(ℚ)`. For the
  rational point group this agrees with the classical rank under finite
  generation (Mordell–Weil, literature, unformalized here); the finrank
  convention reads an infinitely generated group as rank `0`, and that
  convention is part of the pin's statement, recorded here rather than
  hidden. The cardinal-valued positivity results below are
  convention-free.
- The owned Euler factors (`ap`, `localFactor`) are stated at primes of
  good reduction only. Bad-prime factors live on Mathlib's side
  (`localPolynomial`, hence `LSeries`); the owned side fences them out
  and says so.
- The worked curve `y² = x³ - 2` contributes finite proved pieces only:
  the point `(3, 5)`, `Δ = -1728`, `a₅ = 0`, `a₇ = 1`, and the
  Nagell–Lutz arithmetic `25 ∤ Δ`. The Nagell–Lutz theorem itself is not
  in Mathlib and is not proved here: the infinite order of `(3, 5)` is
  carried as the explicit hypothesis `E2InfiniteOrderHypothesis`. That
  labeled gap is the `nagellLutz_seam`.

Honesty tiers in this file:
- **T1 (proved):** everything with a proof term below — the tensor-rank
  sanity lemmas, the point counts, the worked-curve arithmetic.
- **T5 (statement, unproved by design):** `BSDRankEquality`.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The algebraic side: rank of the rational point group -/

/-- The rank space of an elliptic curve over `ℚ`: the rational point group
tensored with `ℚ`. A point of infinite order survives in this space
(`one_tmul_ne_zero_of_infiniteOrder`); torsion dies in it
(`tmul_eq_zero_of_torsion`). -/
abbrev rankSpace (E : WeierstrassCurve ℚ) : Type :=
  ℚ ⊗[ℤ] E.toAffine.Point

/-- The algebraic rank of `E`: the `ℚ`-dimension of its rank space.
See the module header for the finrank convention and its Mordell–Weil
caveat. -/
noncomputable def algebraicRank (E : WeierstrassCurve ℚ) : ℕ :=
  Module.finrank ℚ (rankSpace E)

/-- Pure tensors on torsion elements vanish after tensoring with `ℚ`:
if `n • a = 0` for some `n ≠ 0`, then `q ⊗ₜ a = 0` for every `q`. -/
theorem tmul_eq_zero_of_torsion {A : Type*} [AddCommGroup A] {a : A} {n : ℕ}
    (hn : n ≠ 0) (h : n • a = 0) (q : ℚ) :
    q ⊗ₜ[ℤ] a = 0 := by
  have key : (1 : ℚ) ⊗ₜ[ℤ] a = 0 := by
    have h2 : (n : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ[ℤ] (n • a) := by
      rw [← natCast_zsmul, TensorProduct.tmul_smul]
      congr 1
      simp [zsmul_eq_mul]
    have h1 : ((n : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] a) = 0 := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, h2, h,
        TensorProduct.tmul_zero]
    have h4 : ((1 : ℚ) ⊗ₜ[ℤ] a)
        = ((n : ℚ))⁻¹ • (((n : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] a)) := by
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn : (n : ℚ) ≠ 0),
        one_smul]
    rw [h4, h1, smul_zero]
  calc q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = 0 := by rw [key, smul_zero]

/-- Sanity of the tensor definition: a *finite* abelian group has
tensor-rank zero — every element of `ℚ ⊗[ℤ] A` is a sum of pure tensors
on torsion elements. -/
theorem finrank_tensor_eq_zero_of_finite {A : Type*} [AddCommGroup A]
    [Finite A] : Module.finrank ℚ (ℚ ⊗[ℤ] A) = 0 := by
  have hzero : ∀ x : ℚ ⊗[ℤ] A, x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q a =>
      exact tmul_eq_zero_of_torsion (addOrderOf_pos a).ne'
        (addOrderOf_nsmul_eq_zero a) q
    | add x y hx hy => rw [hx, hy, add_zero]
  have : Subsingleton (ℚ ⊗[ℤ] A) := ⟨fun x y => by rw [hzero x, hzero y]⟩
  exact Module.finrank_eq_zero_of_subsingleton ℚ (ℚ ⊗[ℤ] A)

/-- Sanity of the rank definition: if the rational point group is finite,
the algebraic rank of `E` is `0`. -/
theorem algebraicRank_eq_zero_of_finite (E : WeierstrassCurve ℚ)
    [Finite E.toAffine.Point] : algebraicRank E = 0 :=
  finrank_tensor_eq_zero_of_finite

/-- The `ℤ`-linear map `ℤ → A` sending `n` to `n • p`. -/
noncomputable def zhom {A : Type*} [AddCommGroup A] (p : A) : ℤ →ₗ[ℤ] A :=
  LinearMap.toSpanSingleton ℤ A p

theorem zhom_apply {A : Type*} [AddCommGroup A] (p : A) (n : ℤ) :
    zhom p n = n • p := rfl

theorem zhom_injective {A : Type*} [AddCommGroup A] {p : A}
    (hp : ∀ n : ℤ, n • p = 0 → n = 0) : Function.Injective (zhom p) := by
  intro m n hmn
  have h0 : zhom p (m - n) = 0 := by rw [map_sub, hmn, sub_self]
  rw [zhom_apply] at h0
  exact sub_eq_zero.mp (hp (m - n) h0)

/-- A point of infinite order has nonzero image in the rank space:
flatness of `ℚ` over `ℤ` (localization) keeps `ℤ → A` injective after
tensoring, and `1 ⊗ₜ 1 ≠ 0` in `ℚ ⊗[ℤ] ℤ`. -/
theorem one_tmul_ne_zero_of_infiniteOrder {A : Type*} [AddCommGroup A] {p : A}
    (hp : ∀ n : ℤ, n • p = 0 → n = 0) :
    (1 : ℚ) ⊗ₜ[ℤ] p ≠ 0 := by
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hinj : Function.Injective (LinearMap.lTensor ℚ (zhom p)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (zhom p)
      (zhom_injective hp)
  have hne : ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) ≠ 0 := by
    intro hcon
    have h2 := congrArg (AlgebraTensorModule.rid ℤ ℚ ℚ) hcon
    simp [AlgebraTensorModule.rid_tmul] at h2
  have h3 : (LinearMap.lTensor ℚ (zhom p)) ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) ≠ 0 :=
    fun h => hne (hinj (by rw [h, map_zero]))
  rwa [LinearMap.lTensor_tmul, zhom_apply, one_zsmul] at h3

/-- The independent-singleton lemma, cardinal form (convention-free):
a point of infinite order forces the rank space to have positive
`Module.rank`. -/
theorem rank_pos_of_infiniteOrder {A : Type*} [AddCommGroup A] {p : A}
    (hp : ∀ n : ℤ, n • p = 0 → n = 0) :
    0 < Module.rank ℚ (ℚ ⊗[ℤ] A) := by
  have : Nontrivial (ℚ ⊗[ℤ] A) :=
    ⟨(1 : ℚ) ⊗ₜ[ℤ] p, 0, one_tmul_ne_zero_of_infiniteOrder hp⟩
  exact Module.rank_pos_of_free

/-- The independent-singleton lemma, finrank form: a point of infinite
order forces `1 ≤ finrank`, *given* finite dimensionality of the rank
space. In applications the finite dimensionality is Mordell–Weil
(literature); it is a hypothesis here, not a smuggled fact. -/
theorem one_le_finrank_of_infiniteOrder {A : Type*} [AddCommGroup A]
    [Module.Finite ℚ (ℚ ⊗[ℤ] A)] {p : A}
    (hp : ∀ n : ℤ, n • p = 0 → n = 0) :
    1 ≤ Module.finrank ℚ (ℚ ⊗[ℤ] A) := by
  have : Nontrivial (ℚ ⊗[ℤ] A) :=
    ⟨(1 : ℚ) ⊗ₜ[ℤ] p, 0, one_tmul_ne_zero_of_infiniteOrder hp⟩
  exact Module.finrank_pos

/-! ## The Euler side: local data at primes of good reduction -/

/-- The nonsingular-point predicate in explicit arithmetic form. This is
the computable face of `WeierstrassCurve.Affine.Nonsingular` (via
`nonsingular_iff'` and `equation_iff`): polynomial `evalEval` does not
reduce in the kernel, so point counts are taken against this form. -/
def explNonsing {p : ℕ} (W' : WeierstrassCurve.Affine (ZMod p))
    (xy : ZMod p × ZMod p) : Prop :=
  xy.2 ^ 2 + W'.a₁ * xy.1 * xy.2 + W'.a₃ * xy.2
    = xy.1 ^ 3 + W'.a₂ * xy.1 ^ 2 + W'.a₄ * xy.1 + W'.a₆ ∧
  (W'.a₁ * xy.2 - (3 * xy.1 ^ 2 + 2 * W'.a₂ * xy.1 + W'.a₄) ≠ 0 ∨
    2 * xy.2 + W'.a₁ * xy.1 + W'.a₃ ≠ 0)

instance {p : ℕ} (W' : WeierstrassCurve.Affine (ZMod p)) :
    DecidablePred (explNonsing W') :=
  fun ⟨x, y⟩ => inferInstanceAs (Decidable (
    y ^ 2 + W'.a₁ * x * y + W'.a₃ * y
      = x ^ 3 + W'.a₂ * x ^ 2 + W'.a₄ * x + W'.a₆ ∧
    (W'.a₁ * y - (3 * x ^ 2 + 2 * W'.a₂ * x + W'.a₄) ≠ 0 ∨
      2 * y + W'.a₁ * x + W'.a₃ ≠ 0)))

theorem nonsingular_iff_expl {p : ℕ} (W' : WeierstrassCurve.Affine (ZMod p))
    (xy : ZMod p × ZMod p) : W'.Nonsingular xy.1 xy.2 ↔ explNonsing W' xy :=
  (WeierstrassCurve.Affine.nonsingular_iff' xy.1 xy.2).trans
    (and_congr (WeierstrassCurve.Affine.equation_iff xy.1 xy.2) Iff.rfl)

/-- Point counting: the points of a curve over `ZMod p` are the explicit
nonsingular affine points plus the point at infinity. -/
theorem natCard_point_eq {p : ℕ} [NeZero p]
    (W' : WeierstrassCurve.Affine (ZMod p)) :
    Nat.card W'.Point
      = Nat.card {xy : ZMod p × ZMod p // explNonsing W' xy} + 1 := by
  have e1 : W'.Point ≃ Option {xy : ZMod p × ZMod p // W'.Nonsingular xy.1 xy.2} :=
    WeierstrassCurve.Affine.nonsingularPointEquiv W'
  have e2 : {xy : ZMod p × ZMod p // W'.Nonsingular xy.1 xy.2}
      ≃ {xy : ZMod p × ZMod p // explNonsing W' xy} :=
    Equiv.subtypeEquivProp (funext fun xy => propext (nonsingular_iff_expl W' xy))
  rw [Nat.card_congr (e1.trans e2.optionCongr), Nat.card_eq_fintype_card,
    Fintype.card_option, Nat.card_eq_fintype_card]

/-- The local invariant `a_p` of a curve over `ZMod p`, from the point
count including the point at infinity: `a_p = p + 1 - #points`. This is
the owned Euler-side definition; it is stated for the reduction curve
itself, at any prime (good or bad — the count does not care; the
*use* of `a_p` in an Euler factor is fenced to good reduction by
`localFactor`'s prose and by the analytic package). -/
noncomputable def ap {p : ℕ} (W' : WeierstrassCurve.Affine (ZMod p)) : ℤ :=
  (p : ℤ) + 1 - (Nat.card W'.Point : ℤ)

/-- The local Euler factor at a prime of good reduction:
`1 / (1 - a_p T + p T²)` evaluated at `T = p^{-s}`. Fence: good
reduction only. At bad primes the true local factors are
`1 / (1 ∓ p^{-s})` or `1` according to reduction type; those live on
Mathlib's side (`WeierstrassCurve.localPolynomial`) and are not
rebuilt here. -/
noncomputable def localFactor {p : ℕ} (W' : WeierstrassCurve.Affine (ZMod p))
    (s : ℂ) : ℂ :=
  (1 - (ap W' : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) * (p : ℂ) ^ (-(2 * s)))⁻¹

/-! ## The analytic side: continuation as a labeled hypothesis, and the pin -/

/-- An analytic data package for `E`: the analytic continuation of the
L-series, carried as explicit labeled data — this structure *is* the
formalization debt named in the module header. Its fields: an integral
model of `E`; a holomorphic function `L`; the agreement of `L` with
Mathlib's owned L-series `E.LSeries` on the convergence half-plane
`Re s > 3/2`. In the literature the package exists by modularity; here
it is hypothesized, never constructed. The `notIdenticallyZero` field
keeps `analyticRank` honest (the zero function would have infinite
order of vanishing at every point, which the natural-number readout
would otherwise misreport as rank `0`). -/
structure BSDAnalyticData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  model : WeierstrassCurve ℤ
  model_spec : model.map (Int.castRingHom ℚ) = E
  L : ℂ → ℂ
  differentiableL : Differentiable ℂ L
  notIdenticallyZero : L ≠ 0
  eulerAgreement : ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The analytic rank of a data package: the order of vanishing of `L`
at `s = 1`, read off `meromorphicOrderAt`. Defined, not assumed: for a
holomorphic `L` the order is a nonnegative integer or `⊤` (the locally
zero case, excluded for the true package by `notIdenticallyZero` plus
the identity theorem — the `⊤` readout `0` is the junk case and the
prose of `BSDAnalyticData` owns it). -/
noncomputable def analyticRank {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (D : BSDAnalyticData E) : ℕ :=
  (meromorphicOrderAt D.L 1).untopD 0 |>.toNat

/-- Sanity of the analytic readout: if `L 1 ≠ 0`, the analytic rank
is `0`. -/
theorem analyticRank_eq_zero_of_apply_ne_zero {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (D : BSDAnalyticData E) (h : D.L 1 ≠ 0) :
    analyticRank D = 0 := by
  have hmer : MeromorphicAt D.L 1 := (D.differentiableL.analyticAt 1).meromorphicAt
  have htend : Tendsto D.L (𝓝[≠] 1) (𝓝 (D.L 1)) :=
    Filter.Tendsto.mono_left (D.differentiableL.continuous).continuousAt
      nhdsWithin_le_nhds
  have hord : meromorphicOrderAt D.L 1 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hmer).mp ⟨D.L 1, h, htend⟩
  simp [analyticRank, hord]

/-- **The pin.** The Birch–Swinnerton-Dyer rank equality: for every
nonsingular Weierstrass curve `E` over `ℚ` and every analytic data
package for `E`, the analytic rank equals the algebraic rank. This
`Prop` is the conjecture (Wiles's Clay chapter: the rank equality is
the Millennium statement). It is a statement, not a theorem of this
file: nothing here proves it, and any future claimed proof must be
checked against this unmoving target. -/
def BSDRankEquality : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (D : BSDAnalyticData E),
    analyticRank D = algebraicRank E

/-! ## The worked curve `y² = x³ - 2` -/

/-- The integral model `y² = x³ - 2` over `ℤ`. -/
def E2Int : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, -2⟩

/-- The worked curve `y² = x³ - 2` over `ℚ`. -/
def E2 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -2⟩

/-- Its reduction modulo `5`, as a curve over `ZMod 5`. -/
def E2mod5 : WeierstrassCurve.Affine (ZMod 5) := ⟨0, 0, 0, 0, -2⟩

/-- Its reduction modulo `7`, as a curve over `ZMod 7`. -/
def E2mod7 : WeierstrassCurve.Affine (ZMod 7) := ⟨0, 0, 0, 0, -2⟩

theorem E2Int_model : E2Int.map (Int.castRingHom ℚ) = E2 := by
  ext <;> norm_num [E2Int, E2]

theorem E2Int_map_five : E2Int.map (Int.castRingHom (ZMod 5)) = E2mod5 := by
  ext <;> decide

theorem E2Int_map_seven : E2Int.map (Int.castRingHom (ZMod 7)) = E2mod7 := by
  ext <;> decide

/-- The discriminant of `y² = x³ - 2` is `-1728` (`= -16 · 27 · (-2)²`
up to the standard formula). -/
theorem E2_delta : E2.Δ = -1728 := by
  norm_num [E2, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E2.IsElliptic :=
  ⟨by rw [E2_delta]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-- The rational point `(3, 5)` on `y² = x³ - 2`: `25 = 27 - 2`. -/
def P35 : E2.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (W' := E2.toAffine) (x := 3) (y := 5) (by
    rw [WeierstrassCurve.Affine.equation_iff]; norm_num [E2])

/-- `a₅ = 0` for `y² = x³ - 2`: six points over `ZMod 5` including
infinity, by finite enumeration. -/
theorem ap_five : ap E2mod5 = 0 := by
  rw [ap, natCard_point_eq, Nat.card_eq_fintype_card]; decide

/-- `a₇ = 1` for `y² = x³ - 2`: seven points over `ZMod 7` including
infinity, by finite enumeration. -/
theorem ap_seven : ap E2mod7 = 1 := by
  rw [ap, natCard_point_eq, Nat.card_eq_fintype_card]; decide

/-- The discriminant of the integral model is `-1728` in `ℤ`. -/
theorem E2Int_delta : E2Int.Δ = -1728 := by
  norm_num [E2Int, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The Nagell–Lutz arithmetic for `(3, 5)`, proved: the `y`-coordinate
is nonzero and its square does not divide the discriminant of the
integral model. The Nagell–Lutz theorem — a torsion point with
`y ≠ 0` has `y² ∣ Δ` — would combine with these two facts to give
`(3, 5)` infinite order. That theorem is not in Mathlib; see
`E2InfiniteOrderHypothesis` and the `nagellLutz_seam` in the module
header. -/
theorem five_sq_not_dvd_delta : ¬ ((5 : ℤ) ^ 2 ∣ E2Int.Δ) := by
  rw [E2Int_delta]; decide

/-- The infinite order of `(3, 5)`, carried as an explicitly labeled
hypothesis — the `nagellLutz_seam`. Nagell–Lutz would discharge it
from `five_sq_not_dvd_delta` (and `5 ≠ 0`); nothing in this file
discharges it. -/
def E2InfiniteOrderHypothesis : Prop :=
  ∀ n : ℤ, n • P35 = 0 → n = 0

/-- Rank ≥ 1 reduction, cardinal form (no finiteness hypothesis):
modulo the labeled `nagellLutz_seam` hypothesis, the rank space of
`y² = x³ - 2` has positive rank. -/
theorem E2_rank_pos_of_infiniteOrder (h : E2InfiniteOrderHypothesis) :
    0 < Module.rank ℚ (ℚ ⊗[ℤ] E2.toAffine.Point) :=
  rank_pos_of_infiniteOrder h

/-- Rank ≥ 1 reduction, finrank form: modulo the labeled
`nagellLutz_seam` hypothesis *and* finite dimensionality of the rank
space (Mordell–Weil, literature), `algebraicRank E2 ≥ 1`. -/
theorem E2_one_le_algebraicRank_of_infiniteOrder
    [Module.Finite ℚ (ℚ ⊗[ℤ] E2.toAffine.Point)]
    (h : E2InfiniteOrderHypothesis) :
    1 ≤ algebraicRank E2 :=
  one_le_finrank_of_infiniteOrder h

end ThetLogos
