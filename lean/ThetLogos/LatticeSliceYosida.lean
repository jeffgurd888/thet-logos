/-
# FG-2c-3 — ROUTE B CONSTRUCT: THE YOSIDA APPROXIMANTS AND
# THE CANDIDATE SEMIGROUP

Brick FG-2c-3 of the FG-2c gate paper
(`whitepaper/stage2-fg2c-gate-2026-10-25.md`, §2 Sense B,
§4): the CONSTRUCT half of Route B. PLACEMENT LABEL
(consumed from the gate, not re-decided here): **Stage 2
completeness** work at fixed volume. It is NOT frontier
progress: Items 3 (uniform estimates) and 4 (continuum)
are untouched, and nothing here moves any dial. Dials
0/4. NO CLAIM.

## What this brick consumes

* FG-2b (`LatticeSliceFriedrichs`): the carrier
  `H' := sliceFormClosure`, the Hamiltonian
  `sliceHamOperator` on `D(Ĥ) = range R₁`, symmetric,
  positive (`sliceHamOperator_inner_self_nonneg`), with
  `Ĥ + 1` surjective and `ĤΩ = 0`.
* FG-2c-1 (`LatticeSliceResolvent`): the resolvent family
  `R_λ` at every `λ > 0` as continuous linear maps on
  `H'`, `‖R_λ‖ ≤ λ⁻¹`, symmetric, with range
  `range R_λ = D(Ĥ)` at every weight (domain
  independence), the resolvent equation
  `sliceHamOperator_add_lam_smul`, and `R_λ Ω = λ⁻¹ • Ω`.
* Brick FG-2c-0 of this commission (the Hille–Yosida
  power bound `‖(λ • R_λ)^k‖ ≤ 1`, flagged out of
  FG-2c-1's scope by its own memo): §2 below.

## What this brick proves

The Yosida approximants `Ĥ_n := λ • (1 − λ • R_λ)` at
weight `λ = λₙ := (n : ℝ) + 1` (the shift by one is a
reindexing: every `n : ℕ` is an admissible weight, so
the convergence statements are clean `atTop` statements
about the same cofinal family of approximants) are
bounded, accretive operators on `H'`; the strong
resolvent convergence `λ • R_λ u → u` holds on all of
`H'` (§3, via density of `D(Ĥ)` — derived here from the
landed record: symmetry plus injectivity of `R₁` give
`D(Ĥ)ᗮ = ⊥`); `Ĥ_n v = (λ • R_λ)(Ĥ v) → Ĥ v` holds on
`D(Ĥ)`; the bounded exponentials
`exp(−t Ĥ_n) := NormedSpace.exp ((−t) • Ĥ_n)` are
contractions for `t ≥ 0` (§4, by the factorization
`−t Ĥ_n = (−tλ) • 1 + (tλ²) • R_λ` of commuting parts);
the Duhamel difference identity makes
`exp(−t Ĥ_n) u` Cauchy in `n`, first on `D(Ĥ)` with the
rate `t • (‖Ĥ_n v − Ĥv‖ + ‖Ĥ_m v − Ĥv‖)`, then on all of
`H'` by density and the uniform contraction bound; and
the strong limit `S(t)` is a contraction semigroup on
`H'`: `S(0) = 1`, `‖S(t)‖ ≤ 1`, `S(t) Ω = Ω`, strongly
continuous in `t`, and `S(s + t) = S(s) * S(t)` (§5).

## What this brick does NOT assert (on its face)

**No identification.** Nothing here says `S(t) = T̂_c`,
nor `S(t) = exp(−Ĥ)` in any sense, nor anything about
`Ĥ`'s spectrum. The identification of this candidate
with `T̂_c` is brick FG-2c-4 (the gate's IDENTIFY half,
Sense C) and is not touched. The exponential is
`NormedSpace.exp` of a **bounded** operator — the
library's Banach-algebra exponential; no Hille–Yosida
theorem, no Borel functional calculus, and no spectral
theorem for unbounded operators is invoked or claimed,
because none exists in the pinned Mathlib. Strong
convergence is stated pointwise (`∀ u, Filter.Tendsto
(fun n => ·) atTop (nhds ·)`); there is no
strong-operator topology in the library and none is
pretended.

## The ℚ-algebra note (read before §1)

`NormedSpace.exp` in the pinned Mathlib is defined
through the rational power series, gated internally on
a `Nonempty (Algebra ℚ 𝔸)` choice. For `𝔸 = H' →L[ℂ] H'`
no `Algebra ℚ` (hence no `NormedAlgebra ℚ`) instance
exists in the library; `Algebra ℚ` is a subsingleton
(`Mathlib`'s `algebra_rat_subsingleton`), so the
internal choice is the unique tower structure
`ℚ → ℂ → 𝔸` regardless. The single library lemma that
consumes a `NormedAlgebra ℚ` instance
(`NormedSpace.exp_add_of_commute`) is applied here with
the C*-files' own idiom, a local
`NormedAlgebra.restrictScalars ℚ ℂ _`. Everything else
about `exp` comes from the `ℂ`-algebra API, which
exists outright.
-/

import ThetLogos.LatticeSliceResolvent
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ThetLogos

open MeasureTheory Finset Filter
open scoped Matrix ENNReal NNReal InnerProduct Nat
  Topology

/-! ## §0. Generic Banach-algebra helpers

Facts about `NormedSpace.exp` and the CLM algebra that
are not specific to the slice seat. -/

section YosidaGeneric

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
  [CompleteSpace 𝔸]

/-- Power norm bound from `‖1‖ ≤ 1` (a general
`NormedAlgebra ℂ` does not bound `‖(1 : 𝔸)‖`, so the
hypothesis is carried explicitly; at the CLM seat it
is `clm_one_opNorm_le`). -/
theorem pow_norm_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ∀ n : ℕ, ‖x ^ n‖ ≤ ‖x‖ ^ n := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ k ih =>
      rw [pow_succ]
      exact le_trans (norm_mul_le _ _)
        (mul_le_mul ih (le_refl _) (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _))

/-- The crude exponential bound: `‖exp x‖ ≤ e^{‖x‖}`,
from the defining series and the triangle inequality,
given `‖(1 : 𝔸)‖ ≤ 1`. -/
theorem norm_exp_le_exp_norm (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hnorm : Summable fun n : ℕ => ‖((n ! : ℂ))⁻¹ • x ^ n‖ :=
    NormedSpace.norm_expSeries_summable' x
  have hexp : NormedSpace.exp x
      = ∑' n : ℕ, ((n ! : ℂ))⁻¹ • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hreal : Summable fun n : ℕ => ‖x‖ ^ n / (n ! : ℝ) :=
    Real.summable_pow_div_factorial ‖x‖
  rw [hexp]
  calc ‖∑' n : ℕ, ((n ! : ℂ))⁻¹ • x ^ n‖
      ≤ ∑' n : ℕ, ‖((n ! : ℂ))⁻¹ • x ^ n‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n / (n ! : ℝ) := by
        apply Summable.tsum_le_tsum _ hnorm hreal
        intro n
        calc ‖((n ! : ℂ))⁻¹ • x ^ n‖
            = ((n ! : ℝ))⁻¹ * ‖x ^ n‖ := by
              rw [norm_smul, norm_inv, Complex.norm_natCast]
          _ ≤ ((n ! : ℝ))⁻¹ * ‖x‖ ^ n :=
              mul_le_mul_of_nonneg_left (pow_norm_le h1 x n)
                (by positivity)
          _ = ‖x‖ ^ n / (n ! : ℝ) := by
              rw [div_eq_mul_inv, mul_comm]
    _ = Real.exp ‖x‖ := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The exponential of a scalar multiple of the
identity is the scalar exponential:
`exp (c • 1) = (Complex.exp c) • 1`, through
`algebraMap`. -/
theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : 𝔸)) = (Complex.exp c) • (1 : 𝔸) := by
  rw [← Algebra.algebraMap_eq_smul_one,
    ← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one]

/-- Scalars commute past on the left. -/
theorem commute_smul_left {x y : 𝔸} (h : Commute x y) (c : ℂ) :
    Commute (c • x) y := by
  show (c • x) * y = y * (c • x)
  rw [Algebra.smul_mul_assoc, h.eq, Algebra.mul_smul_comm]

/-- Scalars commute past on the right. -/
theorem commute_smul_right {x y : 𝔸} (h : Commute x y) (c : ℂ) :
    Commute x (c • y) := by
  show x * (c • y) = (c • y) * x
  rw [Algebra.mul_smul_comm, h.eq, Algebra.smul_mul_assoc]

/-- The derivative of a real-affine scalar path through
`exp`: for `r ↦ (a + b • r : ℝ)`, cast to `ℂ` and scaled
into the algebra,
`d/dr exp (((a + b r : ℝ) : ℂ) • x)
  = (b : ℂ) • (exp (((a + b s : ℝ) : ℂ) • x) * x)`
at `r = s`. Assembled from
`hasFDerivAt_exp_smul_const` (taken over `ℝ` from the
start, since the mixed-field chain rule needs one
field) and `HasFDerivAt.comp_hasDerivAt` along the
real affine path. -/
theorem hasDerivAt_exp_affine (x : 𝔸) (a b s : ℝ) :
    HasDerivAt
      (fun r : ℝ => NormedSpace.exp (((a + b * r : ℝ) : ℂ) • x))
      ((b : ℂ) • (NormedSpace.exp (((a + b * s : ℝ) : ℂ) • x) * x))
      s := by
  have hf : HasFDerivAt (fun u : ℂ => NormedSpace.exp (u • x))
      (NormedSpace.exp (((a + b * s : ℝ) : ℂ) • x)
        • (1 : ℂ →L[ℝ] ℂ).smulRight x)
      (((a + b * s : ℝ) : ℂ)) :=
    hasFDerivAt_exp_smul_const ℝ x _
  have hg0 : HasDerivAt (fun y : ℝ => a + b * y) b s := by
    have h := ((hasDerivAt_id s).const_mul b).const_add a
    simpa using h
  have hg : HasDerivAt (fun y : ℝ => ((a + b * y : ℝ) : ℂ))
      (b : ℂ) s :=
    hg0.ofReal_comp
  have hcomp := HasFDerivAt.comp_hasDerivAt s hf hg
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul,
    Algebra.mul_smul_comm] at hcomp
  exact hcomp

/-- The exponential along a complex affine scalar
path, packaged as a definition: at a concrete seat,
applications of this definition carry the §0
instance path, which is what lets the derivative
lemma below and the seat identifications compose
without an instance-diamond clash. -/
noncomputable def yosidaAffineExp (x : 𝔸) (a b z : ℂ) :
    𝔸 :=
  NormedSpace.exp ((a + b * z) • x)

/-- **Derivative of a complex affine exponential
path**: for `z ↦ exp((a + b z) • x)`, the derivative
at `s` is `b • (exp((a + b s) • x) * x)`. The
complex counterpart of `hasDerivAt_exp_affine`,
assembled from `hasFDerivAt_exp_smul_const` over
`ℂ` and the complex affine path. -/
theorem hasDerivAt_exp_affine_complex (x : 𝔸)
    (a b s : ℂ) :
    HasDerivAt
      (fun z : ℂ => yosidaAffineExp x a b z)
      (b • (yosidaAffineExp x a b s * x)) s := by
  have hf : HasFDerivAt
      (fun u : ℂ => NormedSpace.exp (u • x))
      (NormedSpace.exp ((a + b * s) • x)
        • (1 : ℂ →L[ℂ] ℂ).smulRight x)
      (a + b * s) :=
    hasFDerivAt_exp_smul_const ℂ x _
  have hg : HasDerivAt (fun z : ℂ => a + b * z) b
      s := by
    have h1 : HasDerivAt (fun z : ℂ => b * z) b s := by
      simpa using (hasDerivAt_id s).const_mul b
    exact h1.const_add a
  have hcomp := HasFDerivAt.comp_hasDerivAt s hf hg
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul,
    Algebra.mul_smul_comm] at hcomp
  exact hcomp

/-- **The exponential through the consistent
instance path.** At a concrete CLM seat,
`NormedSpace.exp` cannot be elaborated directly:
its `Ring`/`TopologicalSpace` instance arguments
(the canonical CLM ones) do not unify with the
seminormed-ring path that supplies
`IsTopologicalRing` — an instance diamond. Routing
every exponential through this generic definition,
whose instance arguments all derive from the single
local `[NormedRing 𝔸]`, keeps the path consistent;
§4's `sliceYosidaExp` is this map at the slice
seat. -/
noncomputable def yosidaExpOf (x : 𝔸) : 𝔸 :=
  NormedSpace.exp x

theorem yosidaExpOf_zero : yosidaExpOf (0 : 𝔸) = 1 :=
  NormedSpace.exp_zero

/-- The exponential of a sum of commuting elements
splits — `NormedSpace.exp_add_of_commute`, with the
`ℚ`-algebra supplied by restriction of scalars. -/
theorem yosidaExpOf_add_of_commute {x y : 𝔸}
    (h : Commute x y) :
    yosidaExpOf (x + y) = yosidaExpOf x * yosidaExpOf y := by
  letI : NormedAlgebra ℚ 𝔸 :=
    NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  exact NormedSpace.exp_add_of_commute h

/-- An element commuting with `y` commutes with
`exp y`. -/
theorem commute_yosidaExpOf_right {x y : 𝔸}
    (h : Commute x y) : Commute x (yosidaExpOf y) :=
  h.exp_right

/-- The exponential of a scalar multiple of the
identity, in `yosidaExpOf` form (the wrapper keeps
the instance arguments on the §0 path; the bare
`exp_smul_one` does not unify against a
`yosidaExpOf` goal at a concrete seat). -/
theorem yosidaExpOf_smul_one (c : ℂ) :
    yosidaExpOf (c • (1 : 𝔸))
      = (Complex.exp c) • (1 : 𝔸) :=
  exp_smul_one c

/-- The exponential of an `algebraMap` scalar is
the `algebraMap` of the scalar exponential, in
`yosidaExpOf` form (`NormedSpace.algebraMap_exp_comm`
transported through the wrapper, for the same
instance-path reason as `yosidaExpOf_smul_one`). -/
theorem yosidaExpOf_algebraMap_exp (r : ℂ) :
    yosidaExpOf (algebraMap ℂ 𝔸 r)
      = algebraMap ℂ 𝔸 (NormedSpace.exp r) :=
  (NormedSpace.algebraMap_exp_comm r).symm

end YosidaGeneric

section YosidaCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The identity CLM has operator norm at most one. -/
theorem clm_one_opNorm_le : ‖(1 : E →L[ℂ] E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [ContinuousLinearMap.one_apply, one_mul])

/-- Scalars commute past on the left, at the CLM seat
(the §0 generic helper does not unify with the CLM
multiplication instance, so the seat gets its own). -/
theorem clm_commute_smul_left {x y : E →L[ℂ] E}
    (h : Commute x y) (c : ℂ) : Commute (c • x) y := by
  show (c • x) * y = y * (c • x)
  rw [Algebra.smul_mul_assoc, h.eq,
    Algebra.mul_smul_comm]

/-- Scalars commute past on the right, at the CLM
seat. -/
theorem clm_commute_smul_right {x y : E →L[ℂ] E}
    (h : Commute x y) (c : ℂ) : Commute x (c • y) := by
  show x * (c • y) = (c • y) * x
  rw [Algebra.mul_smul_comm, h.eq,
    Algebra.smul_mul_assoc]

end YosidaCLM

/-! ## §1. The Yosida data at the slice seat

The resolvent as a CLM (`FG-2c-1`), the weight
`λₙ = (n : ℝ) + 1`, the contraction `Pₙ = λₙ • R_{λₙ}`,
and the approximant `Ĥₙ = λₙ • (1 − Pₙ)`. -/

section SliceYosida

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The resolvent at weight `λ`, as a continuous
linear map on `H'`** — FG-2c-1's `sliceResolventCLM`
under this brick's name. -/
noncomputable def sliceYosidaR (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) →L[ℂ]
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  sliceResolventCLM μG ρ hN2 hρcont hN β hpos lam hlam

/-- The CLM resolvent and the linear-map resolvent take
the same values. -/
theorem sliceYosidaR_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (f : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam f
      = sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
          hlam f :=
  (sliceResolventCLM_apply μG ρ hN2 hρcont hN β hpos lam
    hlam f).trans
    (sliceResolventLin_apply μG ρ hN2 hρcont hN β hpos
      lam hlam f).symm

/-- **The resolvent bound, in operator norm**:
`‖R_λ‖ ≤ λ⁻¹`. -/
theorem sliceYosidaR_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    ‖sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam‖
      ≤ lam⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr hlam.le) (fun f => by
      rw [sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos
        lam hlam f]
      exact sliceResolvent_norm_le μG ρ hN2 hρcont hN β
        hpos lam hlam f)

/-- **The Yosida weight** `λₙ = (n : ℝ) + 1`: every
natural index is a positive resolvent weight, so the
approximant family indexed by `n : ℕ` is cofinal in
the classical `n → ∞` family. -/
def sliceYosidaWeight (n : ℕ) : ℝ := (n : ℝ) + 1

theorem sliceYosidaWeight_pos (n : ℕ) :
    0 < sliceYosidaWeight n := by
  unfold sliceYosidaWeight
  positivity

theorem sliceYosidaWeight_ne_zero (n : ℕ) :
    sliceYosidaWeight n ≠ 0 :=
  ne_of_gt (sliceYosidaWeight_pos n)

/-- **The scaled resolvent** `Pₙ := λₙ • R_{λₙ}` — the
bounded operator that converges strongly to the
identity (§3). -/
noncomputable def sliceYosidaP (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) →L[ℂ]
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  ((sliceYosidaWeight n : ℂ)) •
    sliceYosidaR μG ρ hN2 hρcont hN β hpos
      (sliceYosidaWeight n) (sliceYosidaWeight_pos n)

/-- **The Yosida approximant**
`Ĥₙ := λₙ • (1 − λₙ • R_{λₙ})` — a bounded operator on
all of `H'`, the `λₙ`-instance of the gate's
`Ĥ_n := n(1 − n • R_n)`. -/
noncomputable def sliceYosidaApprox (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) →L[ℂ]
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
  ((sliceYosidaWeight n : ℂ)) •
    (1 - sliceYosidaP μG ρ hN2 hρcont hN β hpos n)

theorem sliceYosidaApprox_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n u
      = ((sliceYosidaWeight n : ℂ)) •
          (u - sliceYosidaP μG ρ hN2 hρcont hN β hpos n u) := by
  unfold sliceYosidaApprox
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

theorem sliceYosidaP_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    sliceYosidaP μG ρ hN2 hρcont hN β hpos n u
      = ((sliceYosidaWeight n : ℂ)) •
          sliceYosidaR μG ρ hN2 hρcont hN β hpos
            (sliceYosidaWeight n) (sliceYosidaWeight_pos n) u := by
  unfold sliceYosidaP
  rw [ContinuousLinearMap.smul_apply]

/-! ## §2. Brick 0 — the Hille–Yosida power bound and
accretivity

The contraction bounds FG-2c-1's memo flagged out of
its own scope: `‖(λ • R_λ)^k‖ ≤ 1` for every `k`
(induction on the CLM bound), and the accretivity of
the approximants, `Re ⟪Ĥₙ u, u⟫ ≥ 0`, from the symmetry
and positivity of the resolvent pairing plus
Cauchy–Schwarz. -/

/-- **Brick 0a, the scaled bound**: `‖λ • R_λ‖ ≤ 1`. -/
theorem sliceYosida_smulR_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    ‖((lam : ℂ)) • sliceYosidaR μG ρ hN2 hρcont hN β
        hpos lam hlam‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => ?_)
  rw [ContinuousLinearMap.smul_apply, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg hlam.le, one_mul]
  calc lam * ‖sliceYosidaR μG ρ hN2 hρcont hN β hpos
          lam hlam v‖
      ≤ lam * (lam⁻¹ * ‖v‖) :=
        mul_le_mul_of_nonneg_left
          (le_trans (ContinuousLinearMap.le_opNorm _ _)
            (mul_le_mul_of_nonneg_right
              (sliceYosidaR_opNorm_le μG ρ hN2 hρcont hN
                β hpos lam hlam) (norm_nonneg _))) hlam.le
    _ = ‖v‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]

/-- **Brick 0a, the Hille–Yosida power bound**:
`‖(λ • R_λ)^k‖ ≤ 1` for every `k` — induction on `k`
from the scaled bound, exactly the estimate the
Hille–Yosida theorem would consume. -/
theorem sliceYosida_smulR_pow_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (k : ℕ) :
    ‖(((lam : ℂ)) • sliceYosidaR μG ρ hN2 hρcont hN β
        hpos lam hlam) ^ k‖ ≤ 1 := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact clm_one_opNorm_le
  | succ k ih =>
      rw [pow_succ]
      calc ‖(((lam : ℂ)) • sliceYosidaR μG ρ hN2 hρcont
              hN β hpos lam hlam) ^ k
            * (((lam : ℂ)) • sliceYosidaR μG ρ hN2
              hρcont hN β hpos lam hlam)‖
          ≤ ‖(((lam : ℂ)) • sliceYosidaR μG ρ hN2
                hρcont hN β hpos lam hlam) ^ k‖
            * ‖((lam : ℂ)) • sliceYosidaR μG ρ hN2
                hρcont hN β hpos lam hlam‖ :=
            norm_mul_le
              ((((lam : ℂ)) • sliceYosidaR μG ρ hN2
                hρcont hN β hpos lam hlam) ^ k)
              (((lam : ℂ)) • sliceYosidaR μG ρ hN2
                hρcont hN β hpos lam hlam)
        _ ≤ 1 * 1 := by
            refine mul_le_mul ih ?_ ?_ zero_le_one
            · exact sliceYosida_smulR_opNorm_le μG ρ hN2
                hρcont hN β hpos lam hlam
            · exact norm_nonneg
                (((lam : ℂ)) • sliceYosidaR μG ρ hN2
                  hρcont hN β hpos lam hlam)
        _ = 1 := one_mul 1

/-- The scaled approximant resolvent is a contraction:
`‖Pₙ‖ ≤ 1`. -/
theorem sliceYosidaP_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    ‖sliceYosidaP μG ρ hN2 hρcont hN β hpos n‖ ≤ 1 := by
  unfold sliceYosidaP
  exact sliceYosida_smulR_opNorm_le μG ρ hN2 hρcont hN
    β hpos (sliceYosidaWeight n) (sliceYosidaWeight_pos n)

/-- **Brick 0b, accretivity of the approximants**:
`Re ⟪Ĥₙ u, u⟫ ≥ 0` for every `u ∈ H'`. The pairing
`⟪Ĥₙ u, u⟫` is `λₙ ‖u‖² − λₙ² ⟪R_{λₙ} u, u⟫`; the
resolvent pairing is symmetric with nonnegative real
part at most `λₙ⁻¹ ‖u‖²` (pairing positivity plus
Cauchy–Schwarz plus the resolvent bound), and the two
terms cancel to a nonnegative difference. -/
theorem sliceYosidaApprox_accretive (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)) :
    0 ≤ (inner ℂ (sliceYosidaApprox μG ρ hN2 hρcont hN
        β hpos n u) u).re := by
  set a : ℝ := sliceYosidaWeight n with ha
  have hapos : 0 < a := sliceYosidaWeight_pos n
  set R := sliceYosidaR μG ρ hN2 hρcont hN β hpos a
    (sliceYosidaWeight_pos n) with hR
  -- symmetry of the diagonal resolvent pairing
  have hRu : sliceResolvent μG ρ hN2 hρcont hN β hpos
      a (sliceYosidaWeight_pos n) u = R u :=
    (sliceResolventLin_apply μG ρ hN2 hρcont hN β hpos
      a (sliceYosidaWeight_pos n) u).symm.trans
      (sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos a
        (sliceYosidaWeight_pos n) u)
  have hsymm : inner ℂ (R u) u = inner ℂ u (R u) := by
    have h := sliceResolvent_symmetric μG ρ hN2 hρcont
      hN β hpos a (sliceYosidaWeight_pos n) u u
    rw [hRu] at h
    exact h
  have hre : (inner ℂ (R u) u).re = (inner ℂ u (R u)).re :=
    congrArg Complex.re hsymm
  -- the resolvent pairing bound: `re ⟪R u, u⟫ ≤ a⁻¹ ‖u‖²`
  have hpair_nonneg : 0 ≤ (inner ℂ u (R u)).re := by
    have h := sliceResolvent_pairing_nonneg μG ρ hN2
      hρcont hN β hpos a (sliceYosidaWeight_pos n) u
    rwa [hR, sliceYosidaR_apply μG ρ hN2 hρcont hN β
      hpos a (sliceYosidaWeight_pos n) u]
  have hpair_le : (inner ℂ (R u) u).re ≤ a⁻¹ * ‖u‖ ^ 2 := by
    calc (inner ℂ (R u) u).re
        ≤ ‖inner ℂ (R u) u‖ :=
          Complex.re_le_norm _
      _ ≤ ‖R u‖ * ‖u‖ := norm_inner_le_norm _ _
      _ ≤ (a⁻¹ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right
            (calc ‖R u‖ ≤ ‖R‖ * ‖u‖ :=
                    ContinuousLinearMap.le_opNorm R u
              _ ≤ (a⁻¹) * ‖u‖ :=
                    mul_le_mul_of_nonneg_right
                      (sliceYosidaR_opNorm_le μG ρ hN2
                        hρcont hN β hpos a
                        (sliceYosidaWeight_pos n))
                      (norm_nonneg _)) (norm_nonneg _)
      _ = a⁻¹ * ‖u‖ ^ 2 := by ring
  -- expand the approximant pairing (transported to
  -- the ambient space by `sliceFormClosure_inner`:
  -- the generic inner-product lemmas do not unify
  -- against this carrier's inner-product instance,
  -- which is a structure projection)
  have hexp : inner ℂ (sliceYosidaApprox μG ρ hN2
        hρcont hN β hpos n u) u
      = (a : ℂ) * inner ℂ u u
        - ((a : ℂ) * (a : ℂ)) * inner ℂ (R u) u := by
    rw [show sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n u
        = (a : ℂ) • (u - (a : ℂ) • (R u)) from by
      rw [sliceYosidaApprox_apply μG ρ hN2 hρcont hN β
        hpos n u, sliceYosidaP_apply μG ρ hN2 hρcont hN
        β hpos n u],
      sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos,
      sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos,
      sliceFormClosure_inner μG ρ hN2 hρcont hN β hpos]
    show inner ℂ ((a : ℂ) • (u.1 - (a : ℂ) • (R u).1)) u.1
        = (a : ℂ) * inner ℂ u.1 u.1
          - ((a : ℂ) * (a : ℂ)) * inner ℂ (R u).1 u.1
    rw [inner_smul_left, inner_sub_left, inner_smul_left]
    simp only [Complex.conj_ofReal]
    ring
  rw [hexp]
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, sq, Complex.mul_re]
    simp [sq]
  have hre : ∀ (w : ℝ) (z : ℂ),
      ((w : ℂ) * z).re = w * z.re := fun w z => by
    rw [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hmul_re : (((a : ℂ) * (a : ℂ)) * inner ℂ (R u) u).re
      = a ^ 2 * (inner ℂ (R u) u).re := by
    have h1 : ((a : ℂ) * (a : ℂ)) = ((a ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    exact hre _ _
  have hmul_re' : ((a : ℂ) * inner ℂ u u).re
      = a * ‖u‖ ^ 2 := by
    rw [hre, hself]
  rw [Complex.sub_re, hmul_re, hmul_re']
  have hcancel : a * ‖u‖ ^ 2 - a ^ 2 * (inner ℂ (R u) u).re
      ≥ a * ‖u‖ ^ 2 - a ^ 2 * (a⁻¹ * ‖u‖ ^ 2) := by
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_left hpair_le
    positivity
  have hfin : a ^ 2 * (a⁻¹ * ‖u‖ ^ 2) = a * ‖u‖ ^ 2 := by
    rw [pow_two, mul_assoc, mul_inv_cancel_left₀ hapos.ne']
  linarith

/-! ## §3. Brick 1: strong resolvent convergence

Uniqueness for the resolvent equation (accretivity),
the converse-resolvent identity, the core identity
`R_λ(Ĥu + λ•u) = u`, density of the domain, and
`Pₙ → id` strongly on all of `H'`, with `Ĥₙ → Ĥ` on
the domain. -/

/-- The real part of a self-pairing in the ambient
space is the squared norm. -/
theorem sliceYosida_inner_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ z z).re = ‖z‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, sq, Complex.mul_re]
  simp [sq]

/-- The real part of a real scalar multiple:
`((w : ℂ) * z).re = w * z.re`. -/
theorem sliceYosida_ofReal_mul_re (w : ℝ) (z : ℂ) :
    ((w : ℂ) * z).re = w * z.re := by
  rw [Complex.mul_re]
  simp

set_option maxHeartbeats 1600000 in
/-- **Uniqueness for the resolvent equation**: two
domain elements with the same `Ĥ + λ•id` value agree.
Pairing the difference against itself, the real part
is `Re ⟪Ĥw, w⟫ + λ‖w‖²`, a sum of two nonnegative
terms. -/
theorem sliceYosida_add_lam_injective (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (u v : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) (g : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos))
    (hu : sliceHamOperator μG ρ hN2 hρcont hN β hpos u
        + (lam : ℂ) • u.1 = g)
    (hv : sliceHamOperator μG ρ hN2 hρcont hN β hpos v
        + (lam : ℂ) • v.1 = g) :
    u = v := by
  have hdiff : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos (v - u) + (lam : ℂ) • (v - u).1 = 0 := by
    have h1 : sliceHamOperator μG ρ hN2 hρcont hN β
          hpos (v - u)
        = sliceHamOperator μG ρ hN2 hρcont hN β hpos v
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u := map_sub _ _ _
    have h2 : (v - u).1 = v.1 - u.1 := rfl
    rw [h1, h2, smul_sub,
      eq_sub_of_add_eq hv, eq_sub_of_add_eq hu]
    abel
  have hval : (sliceHamOperator μG ρ hN2 hρcont hN β
        hpos (v - u)).1 + (lam : ℂ) • ((v - u).1).1
      = 0 :=
    congrArg Subtype.val hdiff
  have hpair0 : (inner ℂ
        ((sliceHamOperator μG ρ hN2 hρcont hN β hpos
            (v - u)).1 + (lam : ℂ) • ((v - u).1).1)
        ((v - u).1).1).re = 0 := by
    rw [hval]
    simp
  have hexpand : (inner ℂ
        ((sliceHamOperator μG ρ hN2 hρcont hN β hpos
            (v - u)).1 + (lam : ℂ) • ((v - u).1).1)
        ((v - u).1).1).re
      = (inner ℂ (sliceHamOperator μG ρ hN2 hρcont hN
            β hpos (v - u)) (v - u).1).re
        + lam * ‖((v - u).1).1‖ ^ 2 := by
    have t1 : inner ℂ
          ((sliceHamOperator μG ρ hN2 hρcont hN β hpos
              (v - u)).1 + (lam : ℂ) • ((v - u).1).1)
          ((v - u).1).1
        = inner ℂ (sliceHamOperator μG ρ hN2 hρcont
              hN β hpos (v - u)) (v - u).1
          + (lam : ℂ) * inner ℂ ((v - u).1).1
              ((v - u).1).1 := by
      have s1 : inner ℂ
            ((sliceHamOperator μG ρ hN2 hρcont hN β
                hpos (v - u)).1
              + (lam : ℂ) • ((v - u).1).1)
            ((v - u).1).1
          = inner ℂ (sliceHamOperator μG ρ hN2
                hρcont hN β hpos (v - u)).1
              ((v - u).1).1
            + inner ℂ ((lam : ℂ) • ((v - u).1).1)
                ((v - u).1).1 :=
        inner_add_left _ _ _
      have s2 : inner ℂ ((lam : ℂ) • ((v - u).1).1)
            ((v - u).1).1
          = (starRingEnd ℂ) (lam : ℂ)
            * inner ℂ ((v - u).1).1 ((v - u).1).1 :=
        inner_smul_left _ _ _
      have s3 : inner ℂ (sliceHamOperator μG ρ hN2
              hρcont hN β hpos (v - u)).1
            ((v - u).1).1
          = inner ℂ (sliceHamOperator μG ρ hN2
              hρcont hN β hpos (v - u)) (v - u).1 :=
        (sliceFormClosure_inner μG ρ hN2 hρcont hN β
          hpos _ _).symm
      have s4 : (starRingEnd ℂ) (lam : ℂ) = (lam : ℂ) :=
        Complex.conj_ofReal lam
      rw [s1, s2, s3, s4]
    rw [t1, Complex.add_re,
      sliceYosida_ofReal_mul_re,
      sliceYosida_inner_self_re μG ρ hN2 hρcont hN β
        hpos]
  have hnn := sliceHamOperator_inner_self_nonneg μG ρ
    hN2 hρcont hN β hpos (v - u)
  have hsum : (inner ℂ (sliceHamOperator μG ρ hN2
          hρcont hN β hpos (v - u)) (v - u).1).re
        + lam * ‖((v - u).1).1‖ ^ 2 = 0 := by
    rw [← hexpand]
    exact hpair0
  have h2 := (add_eq_zero_iff_of_nonneg hnn
    (mul_nonneg hlam.le (sq_nonneg _))).mp hsum
  have hnorm0 : ‖((v - u).1).1‖ = 0 := by
    have h3 : ‖((v - u).1).1‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2.2 with h | h
      · exact absurd h hlam.ne'
      · exact h
    exact pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)
      |>.mp h3
  have hw1 : (v - u).1 = 0 := by
    apply Subtype.ext
    show ((v - u).1).1 = 0
    exact norm_eq_zero.mp hnorm0
  have hw : v - u = 0 := by
    apply Subtype.ext
    show (v - u).1 = 0
    exact hw1
  exact (sub_eq_zero.mp hw).symm

/-- **The converse-resolvent identity**: if
`Ĥu + λ•u = g` then `R_λ g = u` — the resolvent
inverts the resolvent equation, by uniqueness against
the canonical preimage of `g`. -/
theorem sliceYosida_resolvent_eq_of_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) (g : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos))
    (hg : sliceHamOperator μG ρ hN2 hρcont hN β hpos u
        + (lam : ℂ) • u.1 = g) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam g
      = u.1 := by
  have hu' : (⟨sliceResolventLin μG ρ hN2 hρcont hN
        β hpos lam hlam g,
      sliceResolvent_range_le μG ρ hN2 hρcont hN β
        hpos lam hlam (LinearMap.mem_range_self
          (sliceResolventLin μG ρ hN2 hρcont hN β hpos
            lam hlam) g)⟩ :
      ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos)) = u :=
    sliceYosida_add_lam_injective μG ρ hN2 hρcont hN β
      hpos lam hlam _ u g
      (sliceHamOperator_add_lam_smul μG ρ hN2 hρcont
        hN β hpos lam hlam _ g rfl) hg
  rw [sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos lam
    hlam g]
  exact congrArg Subtype.val hu'

/-- **The core identity**: `R_λ(Ĥu + λ•u) = u` on the
domain. -/
theorem sliceYosida_resolvent_core (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam
        (sliceHamOperator μG ρ hN2 hρcont hN β hpos u
          + (lam : ℂ) • u.1) = u.1 :=
  sliceYosida_resolvent_eq_of_add μG ρ hN2 hρcont hN β
    hpos lam hlam u _ rfl

/-- **The defect of `Pₙ` on the domain is a resolvent
value of `Ĥu`**: `Pₙ u − u = −R_{λₙ}(Ĥu)`. -/
theorem sliceYosidaP_sub_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    sliceYosidaP μG ρ hN2 hρcont hN β hpos n u.1 - u.1
      = - sliceYosidaR μG ρ hN2 hρcont hN β hpos
          (sliceYosidaWeight n) (sliceYosidaWeight_pos n)
          (sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u) := by
  have hcore := sliceYosida_resolvent_core μG ρ hN2
    hρcont hN β hpos (sliceYosidaWeight n)
    (sliceYosidaWeight_pos n) u
  rw [map_add, map_smul] at hcore
  have h2 : ((sliceYosidaWeight n : ℂ))
        • (sliceYosidaR μG ρ hN2 hρcont hN β hpos
            (sliceYosidaWeight n)
            (sliceYosidaWeight_pos n) u.1)
      = u.1 - sliceYosidaR μG ρ hN2 hρcont hN β hpos
          (sliceYosidaWeight n)
          (sliceYosidaWeight_pos n)
          (sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u) := by
    rw [add_comm] at hcore
    exact eq_sub_of_add_eq hcore
  rw [sliceYosidaP_apply μG ρ hN2 hρcont hN β hpos n
    u.1, h2]
  abel

/-- The defect bound on the domain:
`‖Pₙ u − u‖ ≤ ‖Ĥu‖ / λₙ`. -/
theorem sliceYosidaP_sub_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    ‖sliceYosidaP μG ρ hN2 hρcont hN β hpos n u.1
        - u.1‖
      ≤ ‖sliceHamOperator μG ρ hN2 hρcont hN β
          hpos u‖ / sliceYosidaWeight n := by
  rw [sliceYosidaP_sub_apply μG ρ hN2 hρcont hN β
    hpos n u, norm_neg]
  refine le_trans (ContinuousLinearMap.le_opNorm _ _)
    ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right
    (sliceYosidaR_opNorm_le μG ρ hN2 hρcont hN β hpos
      (sliceYosidaWeight n) (sliceYosidaWeight_pos n))
    (norm_nonneg _)

/-- **The approximant on the domain is `Pₙ` of the
Hamiltonian**: `Ĥₙ u = Pₙ(Ĥu)`. -/
theorem sliceYosidaApprox_apply_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n u.1
      = sliceYosidaP μG ρ hN2 hρcont hN β hpos n
          (sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u) := by
  have h := sliceYosidaP_sub_apply μG ρ hN2 hρcont hN
    β hpos n u
  have h2 : u.1 - sliceYosidaP μG ρ hN2 hρcont hN β
        hpos n u.1
      = sliceYosidaR μG ρ hN2 hρcont hN β hpos
          (sliceYosidaWeight n)
          (sliceYosidaWeight_pos n)
          (sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u) := by
    have h3 := congrArg Neg.neg h
    rwa [neg_sub, neg_neg] at h3
  rw [sliceYosidaApprox_apply μG ρ hN2 hρcont hN β
    hpos n u.1, sliceYosidaP_apply μG ρ hN2 hρcont hN
    β hpos n (sliceHamOperator μG ρ hN2 hρcont hN β
      hpos u), h2]

/-- **The domain is dense** — its orthogonal complement
in `H'` is zero: a vector orthogonal to the domain is
orthogonal to the range of `R₁`, hence (by symmetry)
annihilated against `R₁` of itself, hence killed by
`R₁`, hence zero by uniqueness for the resolvent
equation at `λ = 1`. -/
theorem sliceHam_domain_orth_eq_bot (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos)ᗮ = ⊥ := by
  have hone : (0 : ℝ) < 1 := by norm_num
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hsymm : ∀ f : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos),
      inner ℂ (sliceYosidaR μG ρ hN2 hρcont hN β
          hpos 1 hone f) y
        = inner ℂ f (sliceYosidaR μG ρ hN2 hρcont hN
            β hpos 1 hone y) := by
    intro f
    rw [sliceFormClosure_inner μG ρ hN2 hρcont hN β
        hpos, sliceFormClosure_inner μG ρ hN2 hρcont
        hN β hpos, sliceYosidaR_apply μG ρ hN2
        hρcont hN β hpos 1 hone f,
      sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos 1
        hone y, sliceResolventLin_apply μG ρ hN2
        hρcont hN β hpos 1 hone f,
      sliceResolventLin_apply μG ρ hN2 hρcont hN β
        hpos 1 hone y]
    exact sliceResolvent_symmetric μG ρ hN2 hρcont
      hN β hpos 1 hone f y
  have hR1 : ∀ f : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos),
      inner ℂ f (sliceYosidaR μG ρ hN2 hρcont hN β
        hpos 1 hone y) = 0 := by
    intro f
    rw [← hsymm f]
    apply (Submodule.mem_orthogonal _ y).mp hy
    rw [sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos
      1 hone f]
    exact sliceResolvent_range_eq μG ρ hN2 hρcont hN
      β hpos 1 hone ▸ LinearMap.mem_range_self
        (sliceResolventLin μG ρ hN2 hρcont hN β hpos
          1 hone) f
  have hR1y : sliceYosidaR μG ρ hN2 hρcont hN β hpos
      1 hone y = 0 :=
    inner_self_eq_zero.mp
      (hR1 (sliceYosidaR μG ρ hN2 hρcont hN β hpos 1
        hone y))
  obtain ⟨u', hu'⟩ :=
    sliceHamOperator_add_lam_surjective μG ρ hN2
      hρcont hN β hpos 1 hone y
  have hu'1 : u'.1 = 0 := by
    rw [← sliceYosida_resolvent_eq_of_add μG ρ hN2
      hρcont hN β hpos 1 hone u' y hu']
    exact hR1y
  have hu'0 : u' = 0 :=
    Subtype.ext (by rw [hu'1]; rfl)
  rw [← hu', hu'0]
  simp

/-- The domain's closure is everything. -/
theorem sliceHam_domain_closure_eq_top (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos).topologicalClosure = ⊤ := by
  have h1 : (sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos).topologicalClosureᗮ = ⊥ := by
    rw [Submodule.orthogonal_closure]
    exact sliceHam_domain_orth_eq_bot μG ρ hN2
      hρcont hN β hpos
  haveI : CompleteSpace ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  haveI : CompleteSpace
      ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos).topologicalClosure :=
    (Submodule.isClosed_topologicalClosure
      _).completeSpace_coe
  exact Submodule.orthogonal_eq_bot_iff.mp h1

/-- Density in ε-form: every vector of `H'` is
approximated by domain vectors. -/
theorem sliceHam_exists_dom_near (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
        hN β hpos), ‖u - v.1‖ < ε := by
  have hu : u ∈ (sliceHamOperatorDomain μG ρ hN2
        hρcont hN β hpos).topologicalClosure := by
    rw [sliceHam_domain_closure_eq_top μG ρ hN2
      hρcont hN β hpos]
    exact Submodule.mem_top
  have hu2 : u ∈ closure
      ((sliceHamOperatorDomain μG ρ hN2 hρcont hN β
        hpos : Submodule ℂ ↥(sliceFormClosure μG ρ
          hN2 hρcont hN β hpos)) : Set
        ↥(sliceFormClosure μG ρ hN2 hρcont hN β
          hpos)) := by
    have h3 : u ∈ ((sliceHamOperatorDomain μG ρ hN2
          hρcont hN β hpos).topologicalClosure : Set
        ↥(sliceFormClosure μG ρ hN2 hρcont hN β
          hpos)) :=
      SetLike.mem_coe.mpr hu
    rwa [Submodule.topologicalClosure_coe] at h3
  rw [Metric.mem_closure_iff] at hu2
  obtain ⟨y, hy, hdist⟩ := hu2 ε hε
  exact ⟨⟨y, SetLike.mem_coe.mp hy⟩,
    by rwa [dist_eq_norm] at hdist⟩

set_option maxHeartbeats 1600000 in
/-- **Convergence on the domain**: `Pₙ u → u` for
`u ∈ dom Ĥ`, by the defect bound and the squeeze. -/
theorem sliceYosidaP_tendsto_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    Tendsto (fun n : ℕ => sliceYosidaP μG ρ hN2
        hρcont hN β hpos n u.1) atTop (𝓝 u.1) := by
  have hlim : Tendsto (fun n : ℕ =>
        ‖sliceHamOperator μG ρ hN2 hρcont hN β hpos
            u‖ / sliceYosidaWeight n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ =>
        (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds (x :=
      ‖sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u‖)).mul h1
    rw [mul_zero] at h2
    refine h2.congr (fun n => ?_)
    simp only [sliceYosidaWeight, mul_one_div]
  have h0 : Tendsto (fun n : ℕ => sliceYosidaP μG ρ
        hN2 hρcont hN β hpos n u.1 - u.1) atTop
      (𝓝 0) :=
    squeeze_zero_norm
      (fun n => sliceYosidaP_sub_norm_le μG ρ hN2
        hρcont hN β hpos n u) hlim
  have h3 := h0.add
    (tendsto_const_nhds (x := u.1))
  simpa [sub_add_cancel] using h3

set_option maxHeartbeats 1600000 in
/-- **Strong resolvent convergence on all of `H'`**:
`Pₙ u → u` for every `u`, by the ε/3 pass through
the dense domain, using that every `Pₙ` is a
contraction. -/
theorem sliceYosidaP_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    Tendsto (fun n : ℕ => sliceYosidaP μG ρ hN2
        hρcont hN β hpos n u) atTop (𝓝 u) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, hv⟩ := sliceHam_exists_dom_near μG ρ
    hN2 hρcont hN β hpos u (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp
    (sliceYosidaP_tendsto_dom μG ρ hN2 hρcont hN β
      hpos v)) (ε / 3) (by positivity)
  refine ⟨N₀, fun n hn => ?_⟩
  have hdist := hN₀ n hn
  rw [dist_eq_norm] at hdist ⊢
  have hcontr : ‖sliceYosidaP μG ρ hN2 hρcont hN β
        hpos n u - sliceYosidaP μG ρ hN2 hρcont hN
        β hpos n v.1‖ ≤ ‖u - v.1‖ := by
    rw [← map_sub]
    refine le_trans (ContinuousLinearMap.le_opNorm
      _ _) ?_
    exact mul_le_of_le_one_left (norm_nonneg _)
      (sliceYosidaP_opNorm_le μG ρ hN2 hρcont hN β
        hpos n)
  have htri : ‖sliceYosidaP μG ρ hN2 hρcont hN β
        hpos n u - u‖
      ≤ ‖sliceYosidaP μG ρ hN2 hρcont hN β hpos n u
          - sliceYosidaP μG ρ hN2 hρcont hN β hpos
            n v.1‖
        + ‖sliceYosidaP μG ρ hN2 hρcont hN β hpos
            n v.1 - v.1‖ + ‖v.1 - u‖ := by
    have heq : sliceYosidaP μG ρ hN2 hρcont hN β
          hpos n u - u
        = (sliceYosidaP μG ρ hN2 hρcont hN β hpos
            n u - sliceYosidaP μG ρ hN2 hρcont hN β
            hpos n v.1)
          + (sliceYosidaP μG ρ hN2 hρcont hN β hpos
              n v.1 - v.1) + (v.1 - u) := by
      abel
    rw [heq]
    exact le_trans (norm_add_le _ _)
      (add_le_add (norm_add_le _ _) (le_refl _))
  have hrev : ‖v.1 - u‖ = ‖u - v.1‖ := norm_sub_rev _ _
  linarith

/-- **The approximants converge on the domain**:
`Ĥₙ u → Ĥ u` for `u ∈ dom Ĥ`, since `Ĥₙ u = Pₙ(Ĥu)`
and `Pₙ → id` strongly. -/
theorem sliceYosidaApprox_tendsto_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    Tendsto (fun n : ℕ => sliceYosidaApprox μG ρ hN2
        hρcont hN β hpos n u.1) atTop
      (𝓝 (sliceHamOperator μG ρ hN2 hρcont hN β
        hpos u)) := by
  have h := sliceYosidaP_tendsto μG ρ hN2 hρcont hN
    β hpos (sliceHamOperator μG ρ hN2 hρcont hN β
      hpos u)
  rwa [show (fun n : ℕ => sliceYosidaP μG ρ hN2
          hρcont hN β hpos n
          (sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u))
        = (fun n : ℕ => sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n u.1) from
      funext fun n => (sliceYosidaApprox_apply_dom
        μG ρ hN2 hρcont hN β hpos n u).symm] at h

/-! ## §4. Brick 2 — the approximant semigroups and the
strong limit

The resolvent identity (from the §3 uniqueness),
commutation of the resolvents and of the approximants,
the approximant semigroups `E(t, n) = exp(−t Ĥₙ)`, their
contraction bound, the Duhamel difference estimate on
`dom Ĥ`, and the strong limit `S(t)` on all of `H'`.
This brick does NOT identify `S(t)` with `T̂_c` or with
any functional calculus of `Ĥ` — that is FG-2c-4. -/

/-- **The canonical domain preimage** of `g` under
`R_λ`: the domain element whose value is `R_λ g`. -/
noncomputable def sliceYosidaPreimage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN β
      hpos) :=
  ⟨sliceResolventLin μG ρ hN2 hρcont hN β hpos lam
      hlam g,
    sliceResolvent_range_le μG ρ hN2 hρcont hN β hpos
      lam hlam (LinearMap.mem_range_self
        (sliceResolventLin μG ρ hN2 hρcont hN β hpos
          lam hlam) g)⟩

theorem sliceYosidaPreimage_val (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    (sliceYosidaPreimage μG ρ hN2 hρcont hN β hpos
        lam hlam g).1
      = sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
          hlam g :=
  (sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos lam
    hlam g).symm

theorem sliceYosidaPreimage_spec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceHamOperator μG ρ hN2 hρcont hN β hpos
        (sliceYosidaPreimage μG ρ hN2 hρcont hN β hpos
          lam hlam g)
      + (lam : ℂ) • (sliceYosidaPreimage μG ρ hN2
          hρcont hN β hpos lam hlam g).1 = g :=
  sliceHamOperator_add_lam_smul μG ρ hN2 hρcont hN β
    hpos lam hlam _ g rfl

set_option maxHeartbeats 1600000 in
/-- **The resolvent identity**:
`R_λ g − R_μ g = (μ − λ) • R_μ (R_λ g)`, from the §3
uniqueness applied to the combination
`preimage_λ g − preimage_μ g − (μ−λ) • preimage_μ (R_λ g)`,
which solves the homogeneous `μ`-resolvent equation. -/
theorem sliceYosida_resolvent_identity (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam mu : ℝ)
    (hlam : 0 < lam) (hmu : 0 < mu)
    (g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam g
        - sliceYosidaR μG ρ hN2 hρcont hN β hpos mu
            hmu g
      = ((mu - lam : ℝ) : ℂ) • sliceYosidaR μG ρ hN2
          hρcont hN β hpos mu hmu
          (sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
            hlam g) := by
  set xb := sliceYosidaPreimage μG ρ hN2 hρcont hN β
    hpos lam hlam g with hxb_def
  set yb := sliceYosidaPreimage μG ρ hN2 hρcont hN β
    hpos mu hmu g with hyb_def
  set zb := sliceYosidaPreimage μG ρ hN2 hρcont hN β
    hpos mu hmu xb.1 with hzb_def
  set c : ℂ := (mu : ℂ) - (lam : ℂ) with hc_def
  have hspec_xb : sliceHamOperator μG ρ hN2 hρcont hN
        β hpos xb + (lam : ℂ) • xb.1 = g :=
    sliceYosidaPreimage_spec μG ρ hN2 hρcont hN β hpos
      lam hlam g
  have hspec_yb : sliceHamOperator μG ρ hN2 hρcont hN
        β hpos yb + (mu : ℂ) • yb.1 = g :=
    sliceYosidaPreimage_spec μG ρ hN2 hρcont hN β hpos
      mu hmu g
  have hspec_zb : sliceHamOperator μG ρ hN2 hρcont hN
        β hpos zb + (mu : ℂ) • zb.1 = xb.1 :=
    sliceYosidaPreimage_spec μG ρ hN2 hρcont hN β hpos
      mu hmu xb.1
  have hxb : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos xb = g - (lam : ℂ) • xb.1 :=
    eq_sub_of_add_eq hspec_xb
  have hyb : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos yb = g - (mu : ℂ) • yb.1 :=
    eq_sub_of_add_eq hspec_yb
  have hzb : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos zb = xb.1 - (mu : ℂ) • zb.1 :=
    eq_sub_of_add_eq hspec_zb
  set u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos) := xb - yb - c • zb with hu_def
  have huval : u.1 = xb.1 - yb.1 - c • zb.1 := rfl
  have hHu : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos u
      = sliceHamOperator μG ρ hN2 hρcont hN β hpos xb
        - sliceHamOperator μG ρ hN2 hρcont hN β hpos
            yb
        - c • sliceHamOperator μG ρ hN2 hρcont hN β
            hpos zb := by
    rw [hu_def]
    simp only [map_sub, map_smul]
  have hcomp : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos u + (mu : ℂ) • u.1 = 0 := by
    rw [hHu, huval, hxb, hyb, hzb, hc_def]
    simp only [smul_sub, smul_smul, sub_smul, sub_mul,
      mul_sub]
    rw [mul_comm (lam : ℂ) (mu : ℂ)]
    abel
  have hv0 : sliceHamOperator μG ρ hN2 hρcont hN β
        hpos (0 : ↥(sliceHamOperatorDomain μG ρ hN2
          hρcont hN β hpos))
      + (mu : ℂ) • (0 : ↥(sliceHamOperatorDomain μG
          ρ hN2 hρcont hN β hpos)).1 = 0 := by
    simp
  have hu0 : u = 0 :=
    sliceYosida_add_lam_injective μG ρ hN2 hρcont hN
      β hpos mu hmu u 0 0 hcomp hv0
  have hval0 : xb.1 - yb.1 - c • zb.1 = 0 := by
    have h := congrArg Subtype.val hu0
    rwa [huval] at h
  have hfin : xb.1 - yb.1 = c • zb.1 :=
    sub_eq_zero.mp hval0
  have hzbv : zb.1 = sliceYosidaR μG ρ hN2 hρcont hN
        β hpos mu hmu
        (sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
          hlam g) := by
    rw [sliceYosidaPreimage_val μG ρ hN2 hρcont hN β
        hpos mu hmu xb.1,
      sliceYosidaPreimage_val μG ρ hN2 hρcont hN β
        hpos lam hlam g]
  have hcast : ((mu - lam : ℝ) : ℂ) = c := by
    rw [hc_def]
    push_cast
    ring
  rw [hcast, ← hzbv,
    ← sliceYosidaPreimage_val μG ρ hN2 hρcont hN β
      hpos lam hlam g,
    ← sliceYosidaPreimage_val μG ρ hN2 hρcont hN β
      hpos mu hmu g]
  exact hfin

set_option maxHeartbeats 1600000 in
/-- **The resolvents commute** (pointwise form):
`R_λ (R_μ g) = R_μ (R_λ g)` — the resolvent identity
read in both directions, cancelling the nonzero
scalar `μ − λ`. -/
theorem sliceYosidaR_apply_commute (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam mu : ℝ)
    (hlam : 0 < lam) (hmu : 0 < mu)
    (g : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam
        (sliceYosidaR μG ρ hN2 hρcont hN β hpos mu
          hmu g)
      = sliceYosidaR μG ρ hN2 hρcont hN β hpos mu hmu
          (sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
            hlam g) := by
  by_cases hlm : lam = mu
  · subst hlm
    rfl
  · set p := sliceYosidaR μG ρ hN2 hρcont hN β hpos
      lam hlam g with hp
    set q := sliceYosidaR μG ρ hN2 hρcont hN β hpos
      mu hmu g with hq
    set A := sliceYosidaR μG ρ hN2 hρcont hN β hpos
      lam hlam q with hA
    set B := sliceYosidaR μG ρ hN2 hρcont hN β hpos
      mu hmu p with hB
    have hc0 : ((mu - lam : ℝ) : ℂ) ≠ 0 :=
      fun h => (sub_ne_zero.mpr (Ne.symm hlm))
        (Complex.ofReal_eq_zero.mp h)
    have h1 : p - q = ((mu - lam : ℝ) : ℂ) • B :=
      sliceYosida_resolvent_identity μG ρ hN2 hρcont
        hN β hpos lam mu hlam hmu g
    have h2 : q - p = ((lam - mu : ℝ) : ℂ) • A :=
      sliceYosida_resolvent_identity μG ρ hN2 hρcont
        hN β hpos mu lam hmu hlam g
    have hneg : -((lam - mu : ℝ) : ℂ)
        = ((mu - lam : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, neg_sub]
    have h2' : ((mu - lam : ℝ) : ℂ) • A = p - q := by
      have e1 : -(((lam - mu : ℝ) : ℂ) • A)
          = ((mu - lam : ℝ) : ℂ) • A := by
        rw [← neg_smul, hneg]
      have e2 : -(((lam - mu : ℝ) : ℂ) • A)
          = p - q := by
        rw [← h2]
        exact neg_sub _ _
      exact e1.symm.trans e2
    have h3 : ((mu - lam : ℝ) : ℂ) • B
        = ((mu - lam : ℝ) : ℂ) • A := by
      rw [h2']
      exact h1.symm
    have h5 : B = A := by
      have h4 := congrArg
        (fun z => (((mu - lam : ℝ) : ℂ))⁻¹ • z) h3
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc0,
        one_smul, one_smul] at h4
    exact h5.symm

/-- **The scaled resolvents commute**:
`Pₙ Pₘ = Pₘ Pₙ`, from the resolvent commutation. -/
theorem sliceYosidaP_mul_commute (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n m : ℕ) :
    Commute (sliceYosidaP μG ρ hN2 hρcont hN β hpos n)
      (sliceYosidaP μG ρ hN2 hρcont hN β hpos m) := by
  show sliceYosidaP μG ρ hN2 hρcont hN β hpos n
      * sliceYosidaP μG ρ hN2 hρcont hN β hpos m
    = sliceYosidaP μG ρ hN2 hρcont hN β hpos m
      * sliceYosidaP μG ρ hN2 hρcont hN β hpos n
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.mul_apply,
    sliceYosidaP_apply, map_smul, smul_smul]
  rw [mul_comm ((sliceYosidaWeight n : ℂ))
      ((sliceYosidaWeight m : ℂ)),
    sliceYosidaR_apply_commute μG ρ hN2 hρcont hN β
      hpos (sliceYosidaWeight m)
      (sliceYosidaWeight n)
      (sliceYosidaWeight_pos m)
      (sliceYosidaWeight_pos n) x]

/-- **The approximants commute**: `Ĥₙ Ĥₘ = Ĥₘ Ĥₙ` —
both are polynomials in the commuting pair
`Pₙ, Pₘ`. -/
theorem sliceYosidaApprox_commute (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n m : ℕ) :
    Commute (sliceYosidaApprox μG ρ hN2 hρcont hN β
        hpos n)
      (sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
        m) := by
  have hP := sliceYosidaP_mul_commute μG ρ hN2
    hρcont hN β hpos n m
  have h1 : Commute
      (1 - sliceYosidaP μG ρ hN2 hρcont hN β hpos n)
      (1 - sliceYosidaP μG ρ hN2 hρcont hN β hpos
        m) :=
    Commute.sub_right
      (Commute.sub_left (Commute.one_left _)
        (Commute.one_right _))
      (Commute.sub_left (Commute.one_left _) hP)
  unfold sliceYosidaApprox
  exact clm_commute_smul_left
    (clm_commute_smul_right h1 _) _

/-- **The approximant semigroup**
`E(t, n) := exp(−t • Ĥₙ)` — the contraction
semigroup of the bounded generator `−Ĥₙ`, via the
normed-algebra exponential of continuous linear
maps, routed through `yosidaExpOf` (the instance
diamond at this seat is documented there). The
carrier completeness is supplied locally from
FG-2b's theorem. -/
noncomputable def sliceYosidaExp (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (n : ℕ) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN
        β hpos) :=
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  yosidaExpOf (((-t : ℝ) : ℂ) •
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n)

/-- The defining equation of the approximant
semigroup, in `yosidaExpOf` form. -/
theorem sliceYosidaExp_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (n : ℕ) :
    sliceYosidaExp μG ρ hN2 hρcont hN β hpos t n
      = yosidaExpOf (((-t : ℝ) : ℂ) •
          sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  rfl

set_option maxHeartbeats 1600000 in
theorem sliceYosidaExp_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    sliceYosidaExp μG ρ hN2 hρcont hN β hpos 0 n
      = 1 := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  rw [sliceYosidaExp_eq,
    show (↑(-(0 : ℝ)) : ℂ) •
          sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n
        = 0 from by
      rw [show (↑(-(0 : ℝ)) : ℂ) = (0 : ℂ) by
        simp only [Complex.ofReal_zero, neg_zero]]
      exact zero_smul ℂ
        (sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n)]
  exact yosidaExpOf_zero (𝔸 :=
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN
        β hpos))

set_option maxHeartbeats 1600000 in
/-- **The approximants commute with each other's
semigroups** — the input to the Duhamel identity. -/
theorem sliceYosidaApprox_commute_exp (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n m : ℕ)
    (t : ℝ) :
    Commute (sliceYosidaApprox μG ρ hN2 hρcont hN β
        hpos n)
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
        m) := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  rw [sliceYosidaExp_eq]
  exact commute_yosidaExpOf_right
    (clm_commute_smul_right
      (sliceYosidaApprox_commute μG ρ hN2 hρcont hN β
        hpos n m) _)

set_option maxHeartbeats 1600000 in
/-- **Decomposition of the exponent**:
`(−t) • Ĥₙ = (−tλₙ) • 1 + (tλₙ²) • R_{λₙ}` as
continuous linear maps — the approximant exponent
splits into a scalar part and a resolvent part. -/
theorem sliceYosidaExp_smul_decomp (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (n : ℕ) :
    ((-t : ℝ) : ℂ) • sliceYosidaApprox μG ρ hN2
        hρcont hN β hpos n
      = ((-t * sliceYosidaWeight n : ℝ) : ℂ) • (1 :
          ↥(sliceFormClosure μG ρ hN2 hρcont hN β
            hpos) →L[ℂ] ↥(sliceFormClosure μG ρ
              hN2 hρcont hN β hpos))
        + ((t * (sliceYosidaWeight n) ^ 2 : ℝ) : ℂ) •
            sliceYosidaR μG ρ hN2 hρcont hN β hpos
              (sliceYosidaWeight n)
              (sliceYosidaWeight_pos n) := by
  have e1 : ((-t : ℝ) : ℂ)
        * ((sliceYosidaWeight n : ℝ) : ℂ)
      = ((-t * sliceYosidaWeight n : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : ((-t : ℝ) : ℂ)
        * ((sliceYosidaWeight n : ℝ) : ℂ)
        * ((sliceYosidaWeight n : ℝ) : ℂ)
      = -((t * (sliceYosidaWeight n) ^ 2 : ℝ) :
          ℂ) := by
    push_cast
    ring
  unfold sliceYosidaApprox sliceYosidaP
  rw [smul_smul, smul_sub, smul_smul, e2, e1]
  have hneg : (-((t * (sliceYosidaWeight n) ^ 2 :
        ℝ) : ℂ)) • sliceYosidaR μG ρ hN2 hρcont hN
        β hpos (sliceYosidaWeight n)
        (sliceYosidaWeight_pos n)
      = -(((t * (sliceYosidaWeight n) ^ 2 : ℝ) :
          ℂ) • sliceYosidaR μG ρ hN2 hρcont hN β
            hpos (sliceYosidaWeight n)
            (sliceYosidaWeight_pos n)) := by
    ext v
    simp
  rw [hneg, sub_neg_eq_add]

set_option maxHeartbeats 1600000 in
/-- **Contraction of the approximant semigroups**:
`‖E(t, n)‖ ≤ 1` for `t ≥ 0`. The exponent splits as
`(−tλₙ) • 1 + (tλₙ²) • R_{λₙ}` (commuting parts);
the scalar part contributes `e^{−tλₙ}`, the resolvent
part at most `e^{tλₙ}` by the crude series bound with
`‖R_{λₙ}‖ ≤ λₙ⁻¹`, and the factors cancel. -/
theorem sliceYosidaExp_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) :
    ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos t n‖
      ≤ 1 := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  have hposw : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hcomm : Commute
      (((-t * sliceYosidaWeight n : ℝ) : ℂ) • (1 :
          ↥(sliceFormClosure μG ρ hN2 hρcont hN β
            hpos) →L[ℂ] ↥(sliceFormClosure μG ρ
              hN2 hρcont hN β hpos)))
      (((t * (sliceYosidaWeight n) ^ 2 : ℝ) : ℂ) •
        sliceYosidaR μG ρ hN2 hρcont hN β hpos
          (sliceYosidaWeight n)
          (sliceYosidaWeight_pos n)) :=
    clm_commute_smul_left
      (clm_commute_smul_right (Commute.one_left _) _)
      _
  have hexp : sliceYosidaExp μG ρ hN2 hρcont hN β
        hpos t n
      = yosidaExpOf (((-t * sliceYosidaWeight n : ℝ) :
            ℂ) • (1 : ↥(sliceFormClosure μG ρ hN2
              hρcont hN β hpos) →L[ℂ]
              ↥(sliceFormClosure μG ρ hN2 hρcont hN
                β hpos)))
        * yosidaExpOf
            (((t * (sliceYosidaWeight n) ^ 2 : ℝ) :
              ℂ) • sliceYosidaR μG ρ hN2 hρcont hN β
                hpos (sliceYosidaWeight n)
                (sliceYosidaWeight_pos n)) := by
    rw [sliceYosidaExp_eq,
      sliceYosidaExp_smul_decomp μG ρ hN2 hρcont hN
        β hpos t n]
    exact yosidaExpOf_add_of_commute hcomm
  rw [hexp]
  have hnormR : ‖sliceYosidaR μG ρ hN2 hρcont hN β
        hpos (sliceYosidaWeight n)
        (sliceYosidaWeight_pos n)‖
      ≤ (sliceYosidaWeight n)⁻¹ :=
    sliceYosidaR_opNorm_le μG ρ hN2 hρcont hN β hpos
      (sliceYosidaWeight n) (sliceYosidaWeight_pos n)
  have hT : ‖((t * (sliceYosidaWeight n) ^ 2 : ℝ) :
        ℂ) • sliceYosidaR μG ρ hN2 hρcont hN β hpos
          (sliceYosidaWeight n)
          (sliceYosidaWeight_pos n)‖
      ≤ t * sliceYosidaWeight n := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg ht hposw.le) (fun v => ?_)
    rw [ContinuousLinearMap.smul_apply,
      sliceYosidaR_apply μG ρ hN2 hρcont hN β hpos
        (sliceYosidaWeight n)
        (sliceYosidaWeight_pos n) v, norm_smul,
      Complex.norm_real,
      Real.norm_of_nonneg
        (mul_nonneg ht (pow_nonneg hposw.le 2))]
    calc (t * (sliceYosidaWeight n) ^ 2) *
          ‖sliceResolventLin μG ρ hN2 hρcont hN β
              hpos (sliceYosidaWeight n)
              (sliceYosidaWeight_pos n) v‖
        ≤ (t * (sliceYosidaWeight n) ^ 2) *
            ((sliceYosidaWeight n)⁻¹ * ‖v‖) :=
          mul_le_mul_of_nonneg_left
            (sliceResolvent_norm_le μG ρ hN2 hρcont
              hN β hpos (sliceYosidaWeight n)
              (sliceYosidaWeight_pos n) v)
            (mul_nonneg ht (pow_nonneg hposw.le 2))
      _ = (t * sliceYosidaWeight n) * ‖v‖ := by
          rw [pow_two]
          field_simp [hposw.ne']
  have hS : ‖yosidaExpOf
        (((-t * sliceYosidaWeight n : ℝ) : ℂ) •
          (1 : ↥(sliceFormClosure μG ρ hN2 hρcont
              hN β hpos) →L[ℂ]
            ↥(sliceFormClosure μG ρ hN2 hρcont hN
              β hpos)))‖
      ≤ Real.exp (-t * sliceYosidaWeight n) := by
    have e : yosidaExpOf
          (((-t * sliceYosidaWeight n : ℝ) : ℂ) •
            (1 : ↥(sliceFormClosure μG ρ hN2 hρcont
                hN β hpos) →L[ℂ]
              ↥(sliceFormClosure μG ρ hN2 hρcont hN
                β hpos)))
        = (Complex.exp
            (((-t * sliceYosidaWeight n : ℝ) : ℂ))) •
            (1 : ↥(sliceFormClosure μG ρ hN2 hρcont
                hN β hpos) →L[ℂ]
              ↥(sliceFormClosure μG ρ hN2 hρcont hN
                β hpos)) := by
      have hbridge : ∀ c : ℂ,
          (c • (1 : ↥(sliceFormClosure μG ρ hN2
                hρcont hN β hpos) →L[ℂ]
              ↥(sliceFormClosure μG ρ hN2 hρcont hN
                β hpos)))
            = algebraMap ℂ
                (↥(sliceFormClosure μG ρ hN2 hρcont
                    hN β hpos) →L[ℂ]
                  ↥(sliceFormClosure μG ρ hN2 hρcont
                    hN β hpos)) c := by
        intro c
        ext v
        rw [smul_apply, one_apply_eq_self,
          ContinuousLinearMap.algebraMap_apply]
      rw [hbridge, hbridge, Complex.exp_eq_exp_ℂ]
      exact yosidaExpOf_algebraMap_exp
        (𝔸 := ↥(sliceFormClosure μG ρ hN2 hρcont hN
            β hpos) →L[ℂ] ↥(sliceFormClosure μG ρ
              hN2 hρcont hN β hpos)) _
    rw [e]
    refine ContinuousLinearMap.opNorm_le_bound _
      (Real.exp_nonneg _) (fun v => ?_)
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, norm_smul,
      Complex.norm_exp_ofReal]
  have hT2 : ‖yosidaExpOf
        (((t * (sliceYosidaWeight n) ^ 2 : ℝ) : ℂ) •
          sliceYosidaR μG ρ hN2 hρcont hN β hpos
            (sliceYosidaWeight n)
            (sliceYosidaWeight_pos n))‖
      ≤ Real.exp (t * sliceYosidaWeight n) :=
    le_trans
      (norm_exp_le_exp_norm clm_one_opNorm_le _)
      (Real.exp_le_exp.mpr hT)
  refine le_trans ?_
    (le_trans (mul_le_mul hS hT2 (by positivity)
      (Real.exp_nonneg _)) ?_)
  · rw [ContinuousLinearMap.mul_def]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  · exact le_of_eq (by
      rw [← Real.exp_add,
        show -t * sliceYosidaWeight n
            + t * sliceYosidaWeight n = 0 by ring,
        Real.exp_zero])

set_option maxHeartbeats 1600000 in
/-- **Bridge, forward affine path**: the §0
complex affine exponential at `a = 0`, `b = −1`,
evaluated at a real point, is the approximant
semigroup `E(r, n)`. The identification crosses
between the algebra scalar action (carried by the
§0 definition) and the module scalar action (in
`sliceYosidaExp`); after unfolding both exponential
definitions the operator identity is checked on
vectors, where the two actions agree. -/
theorem sliceYosidaAffineExp_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (r : ℝ) :
    yosidaAffineExp
        (sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
          n) 0 (-1) ((r : ℂ))
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          r n := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  rw [sliceYosidaExp_eq]
  simp only [yosidaAffineExp, yosidaExpOf]
  congr 1
  ext v
  simp only [smul_apply, Algebra.smul_def,
    ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.algebraMap_apply]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- **Bridge, reversed affine path**: the §0
complex affine exponential at `a = −t`, `b = 1`,
evaluated at a real point, is the reversed
approximant semigroup `E(t − r, n)`. -/
theorem sliceYosidaAffineExp_sub_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (n : ℕ) (r : ℝ) :
    yosidaAffineExp
        (sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
          n) (-(t : ℂ)) 1 ((r : ℂ))
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - r) n := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  rw [sliceYosidaExp_eq]
  simp only [yosidaAffineExp, yosidaExpOf]
  congr 1
  ext v
  simp only [smul_apply, Algebra.smul_def,
    ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.algebraMap_apply]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- **The Duhamel derivative, for a general
vector**: for `w ∈ H'`, the path
`s ↦ E(t − s, n)(E(s, m) w)` is differentiable
everywhere with derivative
`E(t − s, n)(E(s, m)(Ĥₙ − Ĥₘ) w)`. The computation
runs over `ℂ` (where the operator paths are
differentiable by the §0 affine lemma and the
same-field application rule applies) and is then
restricted to the real path; the two bridges above
identify the result with the real approximant
semigroups. No domain hypothesis is needed: both
approximants are bounded. -/
theorem sliceYosidaDuhamel_hasDerivAt (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (n m : ℕ)
    (w : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) (s : ℝ) :
    HasDerivAt
      (fun r => sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos (t - r) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos r
          m w))
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - s) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m ((sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos n
            - sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos m) w))) s := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  have hIn : HasDerivAt
      (fun z : ℂ => (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) 0 (-1) z) w)
      (-((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) 0 (-1) ((s : ℂ)))
        (sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
          m w))) ((s : ℂ)) := by
    have h := HasDerivAt.clm_apply
      (hasDerivAt_exp_affine_complex
        (sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
          m) 0 (-1) ((s : ℂ)))
      (hasDerivAt_const ((s : ℂ)) w)
    simpa only [smul_apply,
      ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.neg_apply, map_zero,
      add_zero, neg_smul, one_smul] using h
  have hOut : HasDerivAt
      (fun z : ℂ => (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 z)
        ((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) 0 (-1) z) w))
      ((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 ((s : ℂ)))
        (sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n
          ((yosidaAffineExp
            (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m) 0 (-1) ((s : ℂ))) w))
      + (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 ((s : ℂ)))
          (-((yosidaAffineExp
            (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m) 0 (-1) ((s : ℂ)))
            (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m w)))) ((s : ℂ)) :=
    by
      have h := HasDerivAt.clm_apply
        (hasDerivAt_exp_affine_complex
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 ((s : ℂ))) hIn
      simpa only [smul_apply, one_smul,
        ContinuousLinearMap.mul_apply] using h
  have hFR : HasFDerivAt
      (fun z : ℂ => (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 z)
        ((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) 0 (-1) z) w))
      ((ContinuousLinearMap.toSpanSingleton ℂ
        ((yosidaAffineExp
            (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n) (-(t : ℂ)) 1 ((s : ℂ)))
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n
            ((yosidaAffineExp
              (sliceYosidaApprox μG ρ hN2 hρcont hN
                β hpos m) 0 (-1) ((s : ℂ))) w))
        + (yosidaAffineExp
            (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n) (-(t : ℂ)) 1 ((s : ℂ)))
          (-((yosidaAffineExp
              (sliceYosidaApprox μG ρ hN2 hρcont hN
                β hpos m) 0 (-1) ((s : ℂ)))
            (sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos m w))))).restrictScalars ℝ)
      ((s : ℂ)) :=
    hOut.hasFDerivAt.restrictScalars ℝ
  have hC := hFR.comp s
    Complex.ofRealCLM.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at hC
  have hswap : sliceYosidaApprox μG ρ hN2 hρcont hN
        β hpos n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m w)
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n w) := by
    have hcomm := (sliceYosidaApprox_commute_exp
      μG ρ hN2 hρcont hN β hpos n m s).eq
    calc sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n (sliceYosidaExp μG ρ hN2 hρcont
            hN β hpos s m w)
        = (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n * sliceYosidaExp μG ρ hN2
                hρcont hN β hpos s m) w :=
          (ContinuousLinearMap.mul_apply _ _ _).symm
      _ = (sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos s m * sliceYosidaApprox μG ρ hN2
                hρcont hN β hpos n) w := by
          rw [hcomm]
      _ = sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos s m (sliceYosidaApprox μG ρ hN2
              hρcont hN β hpos n w) :=
          ContinuousLinearMap.mul_apply _ _ _
  convert hC using 1
  · funext r
    show sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - r) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos r
          m w)
      = (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) (-(t : ℂ)) 1 ((r : ℂ)))
        ((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) 0 (-1) ((r : ℂ))) w)
    rw [sliceYosidaAffineExp_sub_eq μG ρ hN2 hρcont
      hN β hpos t n r,
      sliceYosidaAffineExp_eq μG ρ hN2 hρcont hN β
        hpos m r]
  · show sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - s) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m ((sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos n
            - sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos m) w))
      = (ContinuousLinearMap.toSpanSingleton ℂ
          ((yosidaAffineExp
              (sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n) (-(t : ℂ)) 1
                ((s : ℂ)))
            (sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos n
              ((yosidaAffineExp
                (sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos m) 0 (-1) ((s : ℂ)))
                w))
          + (yosidaAffineExp
              (sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n) (-(t : ℂ)) 1
                ((s : ℂ)))
            (-((yosidaAffineExp
                (sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos m) 0 (-1) ((s : ℂ)))
              (sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos m w)))))
        (Complex.ofRealCLM 1)
    rw [ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_smul,
      sliceYosidaAffineExp_sub_eq μG ρ hN2 hρcont
      hN β hpos t n s,
      sliceYosidaAffineExp_eq μG ρ hN2 hρcont hN β
        hpos m s, hswap, map_neg,
      ContinuousLinearMap.sub_apply, map_sub,
      map_sub, sub_eq_add_neg]

set_option maxHeartbeats 1600000 in
/-- **Duhamel bound on the domain** (joint
consistency): for `u ∈ D(Ĥ)` and `t ≥ 0`,
`‖E(t, n) u − E(t, m) u‖` is at most `t` times the
sum of the two approximant defects
`‖Ĥₙ u − Ĥ u‖ + ‖Ĥₘ u − Ĥ u‖`. Proved by the
fundamental theorem of calculus along the Duhamel
path `s ↦ E(t − s, n)(E(s, m) u)`, whose derivative
is `E(t − s, n)(E(s, m)(Ĥₙ − Ĥₘ) u)`, bounded by the
defect sum through the two contraction bounds. -/
theorem sliceYosidaExp_sub_norm_le_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) (n m : ℕ)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
      β hpos)) :
    ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos t n u.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β hpos t m
          u.1‖
      ≤ t * (‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖
          + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖) := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont hN
      β hpos
  have hcontr : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (k : ℕ)
      (w : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos)),
      ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos τ k
        w‖ ≤ ‖w‖ := by
    intro τ hτ k w
    calc ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos
            τ k w‖
        ≤ ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos
              τ k‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right
            (sliceYosidaExp_opNorm_le μG ρ hN2 hρcont
              hN β hpos τ hτ k) (norm_nonneg _)
      _ = ‖w‖ := one_mul _
  have hw : ‖(sliceYosidaApprox μG ρ hN2 hρcont hN β
        hpos n - sliceYosidaApprox μG ρ hN2 hρcont
        hN β hpos m) u.1‖
      ≤ ‖sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
            n u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖
        + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖ := by
    rw [ContinuousLinearMap.sub_apply]
    have hrewrite : sliceYosidaApprox μG ρ hN2
          hρcont hN β hpos n u.1
        - sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos m u.1
        = (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u)
          - (sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u) := by abel
    rw [hrewrite]
    exact norm_sub_le _ _
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r => sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos (t - r) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos r
          m u.1))
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - s) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m ((sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n
            - sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m) u.1))) s := by
    intro s
    exact sliceYosidaDuhamel_hasDerivAt μG ρ hN2
      hρcont hN β hpos t n m u.1 s
  have hcont : Continuous
      (fun s => sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos (t - s) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m ((sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n
            - sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m) u.1))) :=
    continuous_iff_continuousAt.mpr
      (fun s => (sliceYosidaDuhamel_hasDerivAt μG ρ
        hN2 hρcont hN β hpos t n m
        ((sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n
          - sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m) u.1) s).continuousAt)
  have hbound : ∀ s ∈ Set.uIoc 0 t,
      ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          (t - s) n
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos s
          m ((sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n
            - sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m) u.1))‖
      ≤ ‖sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
            n u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖
        + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖ := by
    intro s hs
    have hs01 : 0 ≤ s ∧ s ≤ t := by
      rw [Set.uIoc_of_le ht] at hs
      exact ⟨(Set.mem_Ioc.mp hs).1.le,
        (Set.mem_Ioc.mp hs).2⟩
    exact le_trans
      (le_trans
        (hcontr (t - s) (sub_nonneg.mpr hs01.2) n _)
        (hcontr s hs01.1 m _)) hw
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s)
    (hcont.intervalIntegrable 0 t)
  have hends :
      (∫ s in (0 : ℝ)..t,
        sliceYosidaExp μG ρ hN2 hρcont hN β hpos
            (t - s) n
          (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
            s m ((sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n
              - sliceYosidaApprox μG ρ hN2 hρcont hN
                β hpos m) u.1)))
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos t m
          u.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
          n u.1 := by
    rw [hFTC, sub_self,
      sliceYosidaExp_zero μG ρ hN2 hρcont hN β hpos
        n, one_apply_eq_self, sub_zero,
      sliceYosidaExp_zero μG ρ hN2 hρcont hN β hpos
        m, one_apply_eq_self]
  calc ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
          n u.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
          m u.1‖
      = ‖∫ s in (0 : ℝ)..t,
          sliceYosidaExp μG ρ hN2 hρcont hN β hpos
              (t - s) n
            (sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos s m ((sliceYosidaApprox μG ρ hN2
                  hρcont hN β hpos n
                - sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos m) u.1))‖ := by
        rw [hends, norm_sub_rev]
    _ ≤ (‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖
          + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖) * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          hbound
    _ = t * (‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos n u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖
          + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
              hpos m u.1
            - sliceHamOperator μG ρ hN2 hρcont hN β
              hpos u‖) := by
        rw [sub_zero, abs_of_nonneg ht, mul_comm]

/-! ## §4d. The strong limit `S(t)`

The Duhamel bound makes `n ↦ E(t, n) u` Cauchy —
first on the domain (against `Ĥₙ u → Ĥ u`), then
everywhere by an `ε/3` pass through the density
of the domain and the uniform contraction bound.
`S(t)` is the resulting strong limit, packaged
as a continuous linear map. -/

set_option maxHeartbeats 1600000 in
/-- **Cauchy on the domain**: for `u ∈ D(Ĥ)` and
`t ≥ 0`, the approximant values `E(t, n) u` form
a Cauchy sequence — the Duhamel bound against
the defect convergence `Ĥₙ u → Ĥ u`. -/
theorem sliceYosidaExp_cauchy_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    CauchySeq (fun n : ℕ => sliceYosidaExp μG ρ
      hN2 hρcont hN β hpos t n u.1) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have ht1' : t + 1 ≠ 0 := ne_of_gt ht1
  have hδ : 0 < ε / (2 * (t + 1)) :=
    div_pos hε (mul_pos (by norm_num) ht1)
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.tendsto_atTop.mp
      (sliceYosidaApprox_tendsto_dom μG ρ hN2
        hρcont hN β hpos u)) _ hδ
  refine ⟨N₀, fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  have hbound := sliceYosidaExp_sub_norm_le_dom
    μG ρ hN2 hρcont hN β hpos t ht n m u
  have hn' : ‖sliceYosidaApprox μG ρ hN2 hρcont hN
        β hpos n u.1
      - sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u‖ < ε / (2 * (t + 1)) := by
    have h2 := hN₀ n hn
    rwa [dist_eq_norm] at h2
  have hN₀' : ‖sliceYosidaApprox μG ρ hN2 hρcont
        hN β hpos m u.1
      - sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u‖ < ε / (2 * (t + 1)) := by
    have h2 := hN₀ m hm
    rwa [dist_eq_norm] at h2
  have hsum : ‖sliceYosidaApprox μG ρ hN2 hρcont
        hN β hpos n u.1
      - sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u‖
    + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
        m u.1
      - sliceHamOperator μG ρ hN2 hρcont hN β hpos
        u‖ < ε / (t + 1) := by
    have h2 := add_lt_add hn' hN₀'
    have h3 : ε / (2 * (t + 1))
        + ε / (2 * (t + 1)) = ε / (t + 1) := by
      field_simp [ht1']
      ring
    linarith [h2, h3]
  have hfin : t * (ε / (t + 1)) < ε := by
    have hlt : t / (t + 1) < 1 := by
      rw [div_lt_one ht1]
      linarith
    have h4 : ε * (t / (t + 1)) < ε * 1 :=
      mul_lt_mul_of_pos_left hlt hε
    rw [mul_one] at h4
    have h5 : t * (ε / (t + 1))
        = ε * (t / (t + 1)) := by
      field_simp [ht1']
    rwa [h5]
  exact lt_of_le_of_lt hbound
    (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hsum.le ht) hfin)

set_option maxHeartbeats 1600000 in
/-- **Cauchy everywhere**: for every `u ∈ H'`
and `t ≥ 0`, `E(t, n) u` is Cauchy — the domain
case plus an `ε/3` pass through the density of
`D(Ĥ)`, using the uniform contraction bound. -/
theorem sliceYosidaExp_cauchy (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    CauchySeq (fun n : ℕ => sliceYosidaExp μG ρ
      hN2 hρcont hN β hpos t n u) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨v, hv⟩ := sliceHam_exists_dom_near μG ρ
    hN2 hρcont hN β hpos u (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := (Metric.cauchySeq_iff.mp
    (sliceYosidaExp_cauchy_dom μG ρ hN2 hρcont hN
      β hpos t ht v)) (ε / 3) (by positivity)
  refine ⟨N₀, fun n hn m hm => ?_⟩
  have hctr : ∀ k : ℕ,
      dist (sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t k u)
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          t k v.1) ≤ ε / 3 := by
    intro k
    have hle := sliceYosidaExp_opNorm_le μG ρ hN2
      hρcont hN β hpos t ht k
    rw [dist_eq_norm, ← map_sub]
    refine le_trans
      (ContinuousLinearMap.le_opNorm _ _) ?_
    refine le_trans
      (mul_le_mul_of_nonneg_right hle
        (norm_nonneg _)) ?_
    rw [one_mul]
    exact le_of_lt hv
  have h2 := hN₀ n hn m hm
  have htri : dist (sliceYosidaExp μG ρ hN2 hρcont
        hN β hpos t n u)
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
        m u)
    ≤ dist (sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t n u)
        (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          t n v.1)
      + (dist (sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t n v.1)
          (sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t m v.1)
        + dist (sliceYosidaExp μG ρ hN2 hρcont hN
            β hpos t m v.1)
          (sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t m u)) :=
    le_trans (dist_triangle _ _ _)
      (add_le_add le_rfl (dist_triangle _ _ _))
  have h3 : dist (sliceYosidaExp μG ρ hN2 hρcont
        hN β hpos t m v.1)
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos t
        m u) ≤ ε / 3 := by
    rw [dist_comm]
    exact hctr m
  linarith [htri, hctr n, h2, h3]

/-- **The strong limit**, as a bare function:
`Slim(t) u = limₙ E(t, n) u` for `t ≥ 0` (and
`u` itself for `t < 0`, where nothing is
claimed). -/
noncomputable def sliceYosidaSlim (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) : ↥(sliceFormClosure μG ρ hN2 hρcont
      hN β hpos) :=
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont
      hN β hpos
  if h : 0 ≤ t then
    Classical.choose
      (cauchySeq_tendsto_of_complete
        (sliceYosidaExp_cauchy μG ρ hN2 hρcont hN
          β hpos t h u))
  else u

set_option maxHeartbeats 1600000 in
/-- **Characterization of the limit**: for
`t ≥ 0`, `E(t, n) u → Slim(t) u` strongly. -/
theorem sliceYosidaSlim_spec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    Tendsto (fun n : ℕ => sliceYosidaExp μG ρ hN2
        hρcont hN β hpos t n u) atTop
      (𝓝 (sliceYosidaSlim μG ρ hN2 hρcont hN β
        hpos t u)) := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont
      hN β hpos
  have h := Classical.choose_spec
    (cauchySeq_tendsto_of_complete
      (sliceYosidaExp_cauchy μG ρ hN2 hρcont hN β
        hpos t ht u))
  rwa [sliceYosidaSlim, dif_pos ht]

set_option maxHeartbeats 1600000 in
/-- **The limit is a contraction on vectors**:
`‖Slim(t) u‖ ≤ ‖u‖` for `t ≥ 0`. -/
theorem sliceYosidaSlim_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ‖sliceYosidaSlim μG ρ hN2 hρcont hN β hpos t
        u‖ ≤ ‖u‖ := by
  refine le_of_tendsto_of_tendsto'
    (Tendsto.norm (sliceYosidaSlim_spec μG ρ hN2
      hρcont hN β hpos t ht u)) tendsto_const_nhds
    ?_
  intro n
  refine le_trans
    (ContinuousLinearMap.le_opNorm _ _) ?_
  refine le_trans
    (mul_le_mul_of_nonneg_right
      (sliceYosidaExp_opNorm_le μG ρ hN2 hρcont
        hN β hpos t ht n) (norm_nonneg _)) ?_
  rw [one_mul]

set_option maxHeartbeats 1600000 in
/-- **Additivity of the limit** in the vector,
for `t ≥ 0` (by uniqueness of strong limits). -/
theorem sliceYosidaSlim_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u w : ↥(sliceFormClosure μG ρ hN2 hρcont hN
      β hpos)) :
    sliceYosidaSlim μG ρ hN2 hρcont hN β hpos t
        (u + w)
      = sliceYosidaSlim μG ρ hN2 hρcont hN β hpos
          t u
        + sliceYosidaSlim μG ρ hN2 hρcont hN β
          hpos t w := by
  refine tendsto_nhds_unique
    (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
      hpos t ht (u + w)) ?_
  simp only [map_add]
  exact Filter.Tendsto.add
    (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
      hpos t ht u)
    (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
      hpos t ht w)

set_option maxHeartbeats 1600000 in
/-- **Homogeneity of the limit** in the vector,
for `t ≥ 0` (by uniqueness of strong limits). -/
theorem sliceYosidaSlim_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) (c : ℂ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceYosidaSlim μG ρ hN2 hρcont hN β hpos t
        (c • u)
      = c • sliceYosidaSlim μG ρ hN2 hρcont hN β
          hpos t u := by
  refine tendsto_nhds_unique
    (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
      hpos t ht (c • u)) ?_
  simp only [map_smul]
  exact Filter.Tendsto.smul tendsto_const_nhds
    (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
      hpos t ht u)

/-- **The Yosida limit operator** `S(t)`, as a
continuous linear map on `H'` for `t ≥ 0` (and
`0` for `t < 0`, where nothing is claimed). Its
values are the strong limits of the approximant
semigroups; no identification of `S(t)` with
`exp(−Ĥ)` or with `T̂_c` is made or claimed
here — that is the separate FG-2c-4 brick. -/
noncomputable def sliceYosidaS (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos)
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont
        hN β hpos) :=
  if h : 0 ≤ t then
    LinearMap.mkContinuous
      { toFun := sliceYosidaSlim μG ρ hN2 hρcont
          hN β hpos t,
        map_add' := fun u w =>
          sliceYosidaSlim_add μG ρ hN2 hρcont hN β
            hpos t h u w,
        map_smul' := fun c u =>
          sliceYosidaSlim_smul μG ρ hN2 hρcont hN
            β hpos t h c u }
      1
      (fun u => by
        simpa using sliceYosidaSlim_norm_le μG ρ
          hN2 hρcont hN β hpos t h u)
  else 0

set_option maxHeartbeats 1600000 in
/-- **Values of `S(t)`**: for `t ≥ 0`,
`S(t) u = Slim(t) u` — the strong limit. -/
theorem sliceYosidaS_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceYosidaS μG ρ hN2 hρcont hN β hpos t u
      = sliceYosidaSlim μG ρ hN2 hρcont hN β hpos
          t u := by
  rw [sliceYosidaS, dif_pos ht]
  rfl

set_option maxHeartbeats 1600000 in
/-- **`S(t)` is the strong limit**: for `t ≥ 0`,
`E(t, n) u → S(t) u` for every `u ∈ H'`. -/
theorem sliceYosidaS_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    Tendsto (fun n : ℕ => sliceYosidaExp μG ρ hN2
        hρcont hN β hpos t n u) atTop
      (𝓝 (sliceYosidaS μG ρ hN2 hρcont hN β hpos
        t u)) := by
  rw [sliceYosidaS_apply μG ρ hN2 hρcont hN β
    hpos t ht u]
  exact sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
    hpos t ht u


/-! ## §5. Brick 3 — family properties of `S(t)`

`S(0) = 1`, the operator-norm contraction
`‖S(t)‖ ≤ 1`, the vacuum fixed point
`S(t) Ω = Ω`, the on-domain rate, strong
continuity in `t`, and the semigroup law
`S(s + t) = S(s) ∘ S(t)` — all for `s, t ≥ 0`,
all from the approximant family properties and
the strong-limit characterization. -/

/-- **The vacuum vector** of the carrier `H'`
(the completed constant function), for the
fixed-point statement `S(t) Ω = Ω`. -/
noncomputable def sliceYosidaVacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (hd : 0 < d) :
    ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :=
  ⟨sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
      hd,
    sliceFormDomain_le_closure μG ρ hN2 hρcont hN
      β hpos
      (sliceHamC_vacuum_mem_domain μG ρ hN2 hρcont
        hN β hpos hd)⟩

set_option maxHeartbeats 1600000 in
/-- **The resolvent fixes the vacuum direction**:
`R_λ Ω = λ⁻¹ • Ω` (FG-2c-1's vacuum identity,
restated at the named vacuum vector). -/
theorem sliceYosidaR_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (lam : ℝ) (hlam : 0 < lam) (hd : 0 < d) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
        hlam (sliceYosidaVacuum μG ρ hN2 hρcont hN
          β hpos hd)
      = ((lam : ℂ))⁻¹ • sliceYosidaVacuum μG ρ hN2
          hρcont hN β hpos hd := by
  rw [sliceYosidaR_apply]
  exact sliceResolvent_vacuum μG ρ hN2 hρcont hN
    β hpos lam hlam hd

set_option maxHeartbeats 1600000 in
/-- **`Pₙ` fixes the vacuum**: `Pₙ Ω = Ω`. -/
theorem sliceYosidaP_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (hd : 0 < d) :
    sliceYosidaP μG ρ hN2 hρcont hN β hpos n
        (sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd)
      = sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd := by
  have hw : ((sliceYosidaWeight n : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (sliceYosidaWeight_pos n).ne'
  rw [sliceYosidaP_apply μG ρ hN2 hρcont hN β
      hpos n _,
    sliceYosidaR_vacuum μG ρ hN2 hρcont hN β hpos
      _ (sliceYosidaWeight_pos n) hd,
    smul_smul, mul_inv_cancel₀ hw, one_smul]

set_option maxHeartbeats 1600000 in
/-- **The approximants annihilate the vacuum**:
`Ĥₙ Ω = 0`. -/
theorem sliceYosidaApprox_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (hd : 0 < d) :
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n
        (sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd)
      = 0 := by
  rw [sliceYosidaApprox_apply μG ρ hN2 hρcont hN
      β hpos n _,
    sliceYosidaP_vacuum μG ρ hN2 hρcont hN β hpos
      n hd, sub_self, smul_zero]

set_option maxHeartbeats 1600000 in
/-- **Derivative of the approximant path at a
vector**: for each `n` and `u`, the path
`t ↦ E(t, n) u` has derivative
`−E(t, n)(Ĥₙ u)` at every `t` — the
bounded-generator derivative, computed over
`ℂ` (the inner step of the Duhamel
computation) and restricted to the real
axis. -/
theorem sliceYosidaExp_hasDerivAt_apply
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) (r : ℝ) :
    HasDerivAt (fun t' : ℝ => sliceYosidaExp μG
        ρ hN2 hρcont hN β hpos t' n u)
      (-(sliceYosidaExp μG ρ hN2 hρcont hN β hpos
        r n (sliceYosidaApprox μG ρ hN2 hρcont hN
          β hpos n u))) r := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont
      hN β hpos
  have hIn : HasDerivAt
      (fun z : ℂ => (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) 0 (-1) z) u)
      (-((yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) 0 (-1) ((r : ℂ)))
        (sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n u))) ((r : ℂ)) := by
    have h := HasDerivAt.clm_apply
      (hasDerivAt_exp_affine_complex
        (sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n) 0 (-1) ((r : ℂ)))
      (hasDerivAt_const ((r : ℂ)) u)
    simpa only [smul_apply,
      ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.neg_apply, map_zero,
      add_zero, neg_smul, one_smul] using h
  have hC0 := hIn.hasFDerivAt.restrictScalars ℝ
  have hC := hC0.comp r
    Complex.ofRealCLM.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at hC
  convert hC using 1
  · funext t'
    show sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          t' n u
      = (yosidaAffineExp
          (sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) 0 (-1) ((t' : ℂ))) u
    rw [sliceYosidaAffineExp_eq μG ρ hN2 hρcont
      hN β hpos n t']
  · show (-(sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos r n (sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n u)))
      = (ContinuousLinearMap.toSpanSingleton ℂ
          (-((yosidaAffineExp
              (sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n) 0 (-1) ((r : ℂ)))
            (sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos n u))))
        (Complex.ofRealCLM 1)
    rw [ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_smul,
      sliceYosidaAffineExp_eq μG ρ hN2 hρcont hN
        β hpos n r]

set_option maxHeartbeats 1600000 in
/-- **The approximant semigroups fix the
vacuum**: `E(t, n) Ω = Ω` for every `t` and `n`
— the exponential series applied to `Ω`, where
every positive power of the generator
annihilates `Ω`. -/
theorem sliceYosidaExp_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (t : ℝ) (n : ℕ) (hd : 0 < d) :
    sliceYosidaExp μG ρ hN2 hρcont hN β hpos t n
        (sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd)
      = sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd := by
  have hderiv : ∀ r : ℝ, HasDerivAt
      (fun t' : ℝ => sliceYosidaExp μG ρ hN2
        hρcont hN β hpos t' n
        (sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd)) 0 r := by
    intro r
    have h := sliceYosidaExp_hasDerivAt_apply μG
      ρ hN2 hρcont hN β hpos n
      (sliceYosidaVacuum μG ρ hN2 hρcont hN β
        hpos hd) r
    rwa [sliceYosidaApprox_vacuum μG ρ hN2 hρcont
      hN β hpos n hd, map_zero, neg_zero] at h
  have hconst := is_const_of_deriv_eq_zero
    (fun r => (hderiv r).differentiableAt)
    (fun r => (hderiv r).deriv) t 0
  rw [hconst, sliceYosidaExp_zero μG ρ hN2
    hρcont hN β hpos n,
    ContinuousLinearMap.one_apply]

set_option maxHeartbeats 1600000 in
/-- **`S(0) = 1`**: the limit at time zero is
the identity. -/
theorem sliceYosidaS_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceYosidaS μG ρ hN2 hρcont hN β hpos 0
      = 1 := by
  ext u
  have hlim : sliceYosidaSlim μG ρ hN2 hρcont hN
        β hpos 0 u = u :=
    tendsto_nhds_unique
      (sliceYosidaSlim_spec μG ρ hN2 hρcont hN β
        hpos 0 (le_refl 0) u)
      (by
        have hfun : (fun n : ℕ => sliceYosidaExp
              μG ρ hN2 hρcont hN β hpos 0 n u)
            = fun _ => u := by
          funext n
          rw [sliceYosidaExp_zero μG ρ hN2 hρcont
            hN β hpos n,
            ContinuousLinearMap.one_apply]
        rw [hfun]
        exact tendsto_const_nhds)
  rw [sliceYosidaS_apply μG ρ hN2 hρcont hN β
    hpos 0 (le_refl 0) u, hlim,
    ContinuousLinearMap.one_apply]

set_option maxHeartbeats 1600000 in
/-- **Operator-norm contraction**: `‖S(t)‖ ≤ 1`
for `t ≥ 0`. -/
theorem sliceYosidaS_opNorm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) :
    ‖sliceYosidaS μG ρ hN2 hρcont hN β hpos t‖
      ≤ 1 := by
  rw [sliceYosidaS, dif_pos ht]
  exact LinearMap.mkContinuous_norm_le _
    (by norm_num) _

set_option maxHeartbeats 1600000 in
/-- **The limit fixes the vacuum**:
`S(t) Ω = Ω` for `t ≥ 0`. -/
theorem sliceYosidaS_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) (hd : 0 < d) :
    sliceYosidaS μG ρ hN2 hρcont hN β hpos t
        (sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd)
      = sliceYosidaVacuum μG ρ hN2 hρcont hN β
          hpos hd :=
  tendsto_nhds_unique
    (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
      hpos t ht _)
    (by
      have hfun : (fun n : ℕ => sliceYosidaExp
            μG ρ hN2 hρcont hN β hpos t n
            (sliceYosidaVacuum μG ρ hN2 hρcont hN
              β hpos hd))
          = fun _ => sliceYosidaVacuum μG ρ hN2
              hρcont hN β hpos hd := by
        funext n
        exact sliceYosidaExp_vacuum μG ρ hN2
          hρcont hN β hpos t n hd
      rw [hfun]
      exact tendsto_const_nhds)

set_option maxHeartbeats 1600000 in
/-- **The on-domain rate**: for `u ∈ D(Ĥ)` and
`t ≥ 0`,
`‖E(t, n) u − S(t) u‖ ≤ t · ‖Ĥₙ u − Ĥ u‖` — the
Duhamel bound with the second approximant
index sent to infinity. -/
theorem sliceYosidaExp_sub_S_le_dom (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont
      hN β hpos)) :
    ‖sliceYosidaExp μG ρ hN2 hρcont hN β hpos t n
        u.1
      - sliceYosidaS μG ρ hN2 hρcont hN β hpos t
        u.1‖
    ≤ t * ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n u.1
        - sliceHamOperator μG ρ hN2 hρcont hN β
          hpos u‖ := by
  have hdef0 : Tendsto
      (fun m : ℕ => ‖sliceYosidaApprox μG ρ hN2
          hρcont hN β hpos m u.1
        - sliceHamOperator μG ρ hN2 hρcont hN β
          hpos u‖) atTop (𝓝 0) := by
    have h4 : Tendsto
        (fun m : ℕ => sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos m u.1
          - sliceHamOperator μG ρ hN2 hρcont hN
            β hpos u) atTop
        (𝓝 (sliceHamOperator μG ρ hN2 hρcont hN
            β hpos u
          - sliceHamOperator μG ρ hN2 hρcont hN
            β hpos u)) :=
      (sliceYosidaApprox_tendsto_dom μG ρ hN2
        hρcont hN β hpos u).sub
          tendsto_const_nhds
    rw [sub_self] at h4
    have h5 := Tendsto.norm h4
    rwa [norm_zero] at h5
  have hlim1 : Tendsto
      (fun m : ℕ => sliceYosidaExp μG ρ hN2
          hρcont hN β hpos t n u.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t m u.1) atTop
      (𝓝 (sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t n u.1
        - sliceYosidaS μG ρ hN2 hρcont hN β hpos
          t u.1)) :=
    tendsto_const_nhds.sub
      (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
        hpos t ht u.1)
  have hlim2 : Tendsto
      (fun m : ℕ => t * (‖sliceYosidaApprox μG ρ
            hN2 hρcont hN β hpos n u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖
        + ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos m u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖)) atTop
      (𝓝 (t * (‖sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n u.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos u‖ + 0))) :=
    Tendsto.const_mul t
      (tendsto_const_nhds.add hdef0)
  have hle := le_of_tendsto_of_tendsto'
    (Tendsto.norm hlim1) hlim2
    (fun m => sliceYosidaExp_sub_norm_le_dom μG
      ρ hN2 hρcont hN β hpos t ht n m u)
  rwa [add_zero] at hle

set_option maxHeartbeats 1600000 in
/-- **Fixed-`n` paths are continuous**: for each
approximant index `n` and vector `u`, the path
`t ↦ E(t, n) u` is continuous on all of `ℝ`. -/
theorem sliceYosidaExp_continuous (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    Continuous (fun t : ℝ => sliceYosidaExp μG ρ
      hN2 hρcont hN β hpos t n u) :=
  continuous_iff_continuousAt.mpr (fun r =>
    (sliceYosidaExp_hasDerivAt_apply μG ρ hN2
      hρcont hN β hpos n u r).continuousAt)

set_option maxHeartbeats 3200000 in
/-- **Strong continuity of `S`**: for every
`u ∈ H'`, the path `t ↦ S(t) u` is continuous
on `[0, ∞)` — an `ε/7` argument: domain
approximation, the on-domain rate (uniform for
`t` in a bounded window), and the fixed-`n`
path continuity. -/
theorem sliceYosidaS_continuousOn (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ContinuousOn (fun t : ℝ => sliceYosidaS μG ρ
      hN2 hρcont hN β hpos t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  have ht₀' : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  obtain ⟨v, hv⟩ := sliceHam_exists_dom_near μG ρ
    hN2 hρcont hN β hpos u (ε / 7) (by positivity)
  have hdef0 : Tendsto
      (fun m : ℕ => ‖sliceYosidaApprox μG ρ hN2
          hρcont hN β hpos m v.1
        - sliceHamOperator μG ρ hN2 hρcont hN β
          hpos v‖) atTop (𝓝 0) := by
    have h4 : Tendsto
        (fun m : ℕ => sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos m v.1
          - sliceHamOperator μG ρ hN2 hρcont hN
            β hpos v) atTop
        (𝓝 (sliceHamOperator μG ρ hN2 hρcont hN
            β hpos v
          - sliceHamOperator μG ρ hN2 hρcont hN
            β hpos v)) :=
      (sliceYosidaApprox_tendsto_dom μG ρ hN2
        hρcont hN β hpos v).sub
          tendsto_const_nhds
    rw [sub_self] at h4
    have h5 := Tendsto.norm h4
    rwa [norm_zero] at h5
  have hdef1 : Tendsto
      (fun m : ℕ => (t₀ + 1) *
        ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos m v.1
        - sliceHamOperator μG ρ hN2 hρcont hN β
          hpos v‖) atTop (𝓝 0) := by
    have h6 := hdef0.const_mul (t₀ + 1)
    rwa [mul_zero] at h6
  obtain ⟨N, hNb⟩ := (Metric.tendsto_atTop.mp
    hdef1) (ε / 7) (by positivity)
  have hNv : (t₀ + 1) * ‖sliceYosidaApprox μG ρ
        hN2 hρcont hN β hpos N v.1
      - sliceHamOperator μG ρ hN2 hρcont hN β
        hpos v‖ < ε / 7 := by
    have h2 := hNb N le_rfl
    rwa [dist_eq_norm, sub_zero,
      Real.norm_of_nonneg (mul_nonneg (by linarith)
        (norm_nonneg _))] at h2
  have hAE : ∀ τ : ℝ, 0 ≤ τ → τ ≤ t₀ + 1 →
      ‖sliceYosidaS μG ρ hN2 hρcont hN β hpos τ u
        - sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          τ N u‖
      ≤ 2 * ‖u - v.1‖ + (t₀ + 1) *
          ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos N v.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos v‖ := by
    intro τ hτ hτ1
    have e : sliceYosidaS μG ρ hN2 hρcont hN β
          hpos τ u
        - sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos τ N u
      = (sliceYosidaS μG ρ hN2 hρcont hN β hpos
            τ u
          - sliceYosidaS μG ρ hN2 hρcont hN β
            hpos τ v.1)
        + ((sliceYosidaS μG ρ hN2 hρcont hN β
              hpos τ v.1
            - sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos τ N v.1)
          + (sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos τ N v.1
            - sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos τ N u)) := by abel
    have p1 : ‖sliceYosidaS μG ρ hN2 hρcont hN β
          hpos τ u
        - sliceYosidaS μG ρ hN2 hρcont hN β hpos
          τ v.1‖ ≤ ‖u - v.1‖ := by
      rw [← map_sub, sliceYosidaS_apply μG ρ hN2
        hρcont hN β hpos τ hτ]
      exact sliceYosidaSlim_norm_le μG ρ hN2
        hρcont hN β hpos τ hτ _
    have p2 : ‖sliceYosidaS μG ρ hN2 hρcont hN β
          hpos τ v.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos τ N v.1‖
      ≤ (t₀ + 1) * ‖sliceYosidaApprox μG ρ hN2
          hρcont hN β hpos N v.1
        - sliceHamOperator μG ρ hN2 hρcont hN β
          hpos v‖ := by
      rw [norm_sub_rev]
      refine le_trans
        (sliceYosidaExp_sub_S_le_dom μG ρ hN2
          hρcont hN β hpos τ hτ N v) ?_
      exact mul_le_mul_of_nonneg_right hτ1
        (norm_nonneg _)
    have p3 : ‖sliceYosidaExp μG ρ hN2 hρcont hN
          β hpos τ N v.1
        - sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos τ N u‖ ≤ ‖u - v.1‖ := by
      rw [← map_sub]
      refine le_trans
        (ContinuousLinearMap.le_opNorm _ _) ?_
      refine le_trans
        (mul_le_mul_of_nonneg_right
          (sliceYosidaExp_opNorm_le μG ρ hN2
            hρcont hN β hpos τ hτ N)
          (norm_nonneg _)) ?_
      rw [one_mul, norm_sub_rev]
    rw [e]
    refine le_trans (norm_add_le _ _)
      (add_le_add le_rfl (norm_add_le _ _)) |>.trans
      (by linarith [p1, p2, p3])
  obtain ⟨δ, hδ0, hδ⟩ :=
    (Metric.continuousAt_iff.mp
      (sliceYosidaExp_continuous μG ρ hN2 hρcont
        hN β hpos N u).continuousAt) (ε / 7)
      (by positivity)
  refine ⟨min δ 1, lt_min hδ0 one_pos,
    fun t htI htδ => ?_⟩
  have ht' : 0 ≤ t := Set.mem_Ici.mp htI
  have hδt : dist t t₀ < δ :=
    lt_of_lt_of_le htδ (min_le_left _ _)
  have hδ1 : dist t t₀ < 1 :=
    lt_of_lt_of_le htδ (min_le_right _ _)
  have ht1 : t ≤ t₀ + 1 := by
    rw [dist_eq_norm] at hδ1
    have h9 := (abs_lt.mp hδ1).2
    linarith
  have hB : dist (sliceYosidaExp μG ρ hN2 hρcont
        hN β hpos t N u)
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
        t₀ N u) < ε / 7 := hδ hδt
  rw [dist_eq_norm] at hB ⊢
  have hA1 := hAE t ht' ht1
  have hA2 := hAE t₀ ht₀' (by linarith)
  have hC : ‖sliceYosidaExp μG ρ hN2 hρcont hN β
        hpos t₀ N u
      - sliceYosidaS μG ρ hN2 hρcont hN β hpos t₀
        u‖
      ≤ 2 * ‖u - v.1‖ + (t₀ + 1) *
          ‖sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos N v.1
          - sliceHamOperator μG ρ hN2 hρcont hN β
            hpos v‖ := by
    have hC0 := hA2
    rwa [norm_sub_rev (sliceYosidaS μG ρ hN2
      hρcont hN β hpos t₀ u)
      (sliceYosidaExp μG ρ hN2 hρcont hN β hpos
        t₀ N u)] at hC0
  have htri : ‖sliceYosidaS μG ρ hN2 hρcont hN β
        hpos t u
      - sliceYosidaS μG ρ hN2 hρcont hN β hpos t₀
        u‖
    ≤ ‖sliceYosidaS μG ρ hN2 hρcont hN β hpos t u
        - sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t N u‖
      + (‖sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t N u
          - sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t₀ N u‖
        + ‖sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t₀ N u
          - sliceYosidaS μG ρ hN2 hρcont hN β
            hpos t₀ u‖) := by
    have e : sliceYosidaS μG ρ hN2 hρcont hN β
          hpos t u
        - sliceYosidaS μG ρ hN2 hρcont hN β hpos
          t₀ u
      = (sliceYosidaS μG ρ hN2 hρcont hN β hpos
            t u
          - sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t N u)
        + ((sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos t N u
            - sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos t₀ N u)
          + (sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos t₀ N u
            - sliceYosidaS μG ρ hN2 hρcont hN β
              hpos t₀ u)) := by abel
    rw [e]
    exact le_trans (norm_add_le _ _)
      (add_le_add le_rfl (norm_add_le _ _))
  linarith [htri, hA1, hC, hB, hv, hNv]

set_option maxHeartbeats 1600000 in
/-- **The approximant semigroup law**:
`E(s + t, n) = E(s, n) ∘ E(t, n)` — the
exponential of a sum of two scalar multiples
of the same bounded generator. -/
theorem sliceYosidaExp_add_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (s t : ℝ) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    sliceYosidaExp μG ρ hN2 hρcont hN β hpos
        (s + t) n u
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          s n (sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos t n u) := by
  letI : CompleteSpace
      ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont
      hN β hpos
  have hcomm : Commute (((-s : ℝ) : ℂ) •
        sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n)
      (((-t : ℝ) : ℂ) • sliceYosidaApprox μG ρ
        hN2 hρcont hN β hpos n) :=
    clm_commute_smul_right
      (clm_commute_smul_left (Commute.refl _) _)
      _
  have harg : (((-(s + t) : ℝ) : ℂ) •
        sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n)
      = (((-s : ℝ) : ℂ) • sliceYosidaApprox μG ρ
            hN2 hρcont hN β hpos n)
        + (((-t : ℝ) : ℂ) • sliceYosidaApprox μG
            ρ hN2 hρcont hN β hpos n) := by
    have h1 : (((-(s + t) : ℝ) : ℂ))
        = (((-s : ℝ) : ℂ)) + (((-t : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [h1]
    ext v
    rw [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, add_smul]
  rw [sliceYosidaExp_eq μG ρ hN2 hρcont hN β
      hpos (s + t) n,
    sliceYosidaExp_eq μG ρ hN2 hρcont hN β hpos
      s n,
    sliceYosidaExp_eq μG ρ hN2 hρcont hN β hpos
      t n, harg,
    yosidaExpOf_add_of_commute hcomm,
    ContinuousLinearMap.mul_apply]

set_option maxHeartbeats 3200000 in
/-- **The semigroup law**: for `s, t ≥ 0`,
`S(s + t) = S(s) ∘ S(t)` — the approximant law,
passed to the strong limit: for fixed `u`, the
error `E(s, n)(E(t, n) u) − S(s)(S(t) u)` is
controlled by the contraction in the first
factor and the strong convergence in the
second. -/
theorem sliceYosidaS_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sliceYosidaS μG ρ hN2 hρcont hN β hpos (s + t)
      = sliceYosidaS μG ρ hN2 hρcont hN β hpos s
        ∘L sliceYosidaS μG ρ hN2 hρcont hN β hpos
          t := by
  ext u : 1
  rw [ContinuousLinearMap.comp_apply]
  refine tendsto_nhds_unique
    (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
      hpos (s + t) (add_nonneg hs ht) u) ?_
  have hfun : (fun n : ℕ => sliceYosidaExp μG ρ
        hN2 hρcont hN β hpos (s + t) n u)
      = (fun n : ℕ => sliceYosidaExp μG ρ hN2
          hρcont hN β hpos s n (sliceYosidaExp μG
            ρ hN2 hρcont hN β hpos t n u)) :=
    funext fun n => sliceYosidaExp_add_apply μG
      ρ hN2 hρcont hN β hpos s t n u
  rw [hfun]
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine squeeze_zero_norm
    (a := fun n : ℕ =>
      dist (sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos t n u)
        (sliceYosidaS μG ρ hN2 hρcont hN β hpos
          t u)
      + dist (sliceYosidaExp μG ρ hN2 hρcont hN
            β hpos s n (sliceYosidaS μG ρ hN2
              hρcont hN β hpos t u))
          (sliceYosidaS μG ρ hN2 hρcont hN β
            hpos s (sliceYosidaS μG ρ hN2 hρcont
              hN β hpos t u)))
    (fun n => ?_) ?_
  · have hnorm : ‖dist (sliceYosidaExp μG ρ hN2
          hρcont hN β hpos s n (sliceYosidaExp μG
            ρ hN2 hρcont hN β hpos t n u))
        (sliceYosidaS μG ρ hN2 hρcont hN β hpos s
          (sliceYosidaS μG ρ hN2 hρcont hN β hpos
            t u))‖
      = ‖sliceYosidaExp μG ρ hN2 hρcont hN β
          hpos s n (sliceYosidaExp μG ρ hN2
            hρcont hN β hpos t n u)
        - sliceYosidaS μG ρ hN2 hρcont hN β hpos
          s (sliceYosidaS μG ρ hN2 hρcont hN β
            hpos t u)‖ := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg dist_nonneg, dist_eq_norm]
    rw [hnorm, dist_eq_norm, dist_eq_norm]
    have e1 : sliceYosidaExp μG ρ hN2 hρcont hN
          β hpos s n (sliceYosidaExp μG ρ hN2
            hρcont hN β hpos t n u)
        - sliceYosidaS μG ρ hN2 hρcont hN β hpos
          s (sliceYosidaS μG ρ hN2 hρcont hN β
            hpos t u)
      = sliceYosidaExp μG ρ hN2 hρcont hN β hpos
          s n (sliceYosidaExp μG ρ hN2 hρcont hN
            β hpos t n u
          - sliceYosidaS μG ρ hN2 hρcont hN β
            hpos t u)
        + (sliceYosidaExp μG ρ hN2 hρcont hN β
            hpos s n (sliceYosidaS μG ρ hN2
              hρcont hN β hpos t u)
          - sliceYosidaS μG ρ hN2 hρcont hN β
            hpos s (sliceYosidaS μG ρ hN2 hρcont
              hN β hpos t u)) := by
      have h10 : sliceYosidaExp μG ρ hN2 hρcont
            hN β hpos s n (sliceYosidaExp μG ρ
              hN2 hρcont hN β hpos t n u)
          = sliceYosidaExp μG ρ hN2 hρcont hN β
              hpos s n (sliceYosidaExp μG ρ hN2
                hρcont hN β hpos t n u
              - sliceYosidaS μG ρ hN2 hρcont hN β
                hpos t u)
            + sliceYosidaExp μG ρ hN2 hρcont hN β
                hpos s n (sliceYosidaS μG ρ hN2
                  hρcont hN β hpos t u) := by
        rw [← map_add, sub_add_cancel]
      rw [h10]
      abel
    rw [e1]
    refine le_trans (norm_add_le _ _)
      (add_le_add ?_ le_rfl)
    refine le_trans
      (ContinuousLinearMap.le_opNorm _ _) ?_
    refine le_trans
      (mul_le_mul_of_nonneg_right
        (sliceYosidaExp_opNorm_le μG ρ hN2 hρcont
          hN β hpos s hs n) (norm_nonneg _)) ?_
    rw [one_mul]
  · have g1 := tendsto_iff_dist_tendsto_zero.mp
      (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
        hpos t ht u)
    have g2 := tendsto_iff_dist_tendsto_zero.mp
      (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
        hpos s hs (sliceYosidaS μG ρ hN2 hρcont
          hN β hpos t u))
    have h11 := g1.add g2
    rwa [add_zero] at h11


end SliceYosida

end ThetLogos
