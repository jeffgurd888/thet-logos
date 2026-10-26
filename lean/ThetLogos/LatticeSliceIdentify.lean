/-
# FG-2c-4 — IDENTIFY: THE YOSIDA SEMIGROUP IS THE TRANSFER
# OPERATOR'S OWN

Brick FG-2c-4 of the FG-2c gate paper
(`whitepaper/stage2-fg2c-gate-2026-10-25.md`, §2 Sense C):
the IDENTIFY half of Route B, and the final brick of the
FG-2 line. PLACEMENT LABEL (consumed from the gate, not
re-decided here): **Stage 2 completeness** work at fixed
volume. It is NOT frontier progress: Items 3 (uniform
estimates) and 4 (continuum) are untouched, and nothing
here moves any dial. Dials 0/4. NO CLAIM.

## What this brick consumes

* FG-2b (`LatticeSliceFriedrichs`): the carrier
  `H' := sliceFormClosure` (= `(ker T̂_c)ᗮ` by FG-2c-0),
  the Hamiltonian `Ĥ = sliceHamOperator`, the Riesz
  resolvent `R₁`.
* FG-2c-1 (`LatticeSliceResolvent`): the resolvent family
  `R_λ` at every `λ > 0`, domain independence
  (`range R_λ = D(Ĥ)`), the `J_λ` Riesz specification and
  its uniqueness.
* FG-2c-0 (`LatticeSliceCfc`): the continuous functional
  calculus of the completed transfer operator `T̂_c` on
  the ambient space — `spectrum ℝ T̂_c ⊆ [0, 1]`, `cfc`
  pairings and their monotonicity, the defect orbit
  `Â_c^n x → 0` on `(ker T̂_c)ᗮ`, and
  `sliceFormClosure = (ker T̂_c)ᗮ`.
* FG-2c-3 (`LatticeSliceYosida`): the candidate semigroup
  `S(t) = sliceYosidaS t`, the strong limit of the Yosida
  approximant exponentials `exp(−t Ĥₙ)`, a contraction
  semigroup on all of `H'`. FG-2c-3 expressly did NOT
  identify its limit.
* FG-2a (`LatticeSliceFormClosed`): the form is the
  `−log T̂_c` series — the polarized approximants are
  `sliceApproxB K x y = Σ_{j=1}^K (1/j)·⟪x, Â^j y⟫` with
  `Â = Â_c` the completed defect. This is the bridge:
  the Friedrichs Hamiltonian of that form is, in the
  classical reading, `−log T̂_c`, whose semigroup at
  `t = 1` is `T̂_c` itself.

## What this brick proves

The identification, by resolvents, in three steps.

* **Step A (§3).** For every `λ > 0`, the FG-2c-1
  resolvent is the `cfc` resolvent of `T̂_c`, restricted
  to `H'`:
  `R_λ = (cfc g_λ T̂_c)|_{H'}` with
  `g_λ(μ) = (λ − log μ)⁻¹` on `(0, 1]`, `g_λ(0) = 0`.
  Proved through the `J_λ` Riesz specification: the
  candidate lies in the form domain (its approximant
  pairings are uniformly bounded by `(4λ)⁻¹‖x‖²`, since
  `g_λ² · T_K ≤ (4λ)⁻¹` pointwise), and it satisfies the
  resolvent pairing identity, since the defect
  `ψ_{λ,K} = 1 − g_λ·(T_K + λ) = g_λ · (−log − T_K)`
  obeys `0 ≤ ψ_{λ,K} ≤ (1−μ)^K` on `[0, 1]`, whose
  pairings die on `H'` by the defect-orbit theorem.
* **Step B (§4).** The Yosida approximants are `cfc`
  operators: `Ĥₙ = (cfc aₙ T̂_c)|_{H'}` with
  `aₙ = λₙ(1 − λₙ g_{λₙ})`, `λₙ = n + 1`; hence
  `exp(−Ĥₙ)` and `cfc (exp(−aₙ·)) T̂_c` agree on `H'`,
  both being limits of the same partial sums.
* **Step C (§5).** `exp(−aₙ(μ)) → μ` uniformly on
  `[0, 1]`, so `cfc (exp(−aₙ·)) T̂_c → T̂_c` in operator
  norm, while `exp(−Ĥₙ) → S(1)` strongly by FG-2c-3.
  The limits agree: **`S(1) = T̂_c|_{H'}`**, as continuous
  linear maps on `H'`.

## The battery corollary (§6)

`SliceBattery`'s T4 hypothesis
`SliceSpectralCorrespondence` has two clauses.
The **Jensen clause** `exp(−E x) ≤ ⟪x, T̂_c x⟫.re` is
DISCHARGED here, elementarily, at every seat: the
energy is the form value, the form value dominates
every partial sum `Σ_{j≤K} a_j/j` of the defect
pairings `a_j = ⟪x, Â^j x⟫.re`, the association
inequality `a_{j+1} ≥ a_j · a_1` (positivity of
`((1−μ)^j − c^j)((1−μ) − c)` in the `cfc` pairing,
at `c^j = a_j`) gives `a_j ≥ a_1^j`, and the log
series sums the bound to `−log(1 − a_1)`.
The **gap clause** `⟪x, T̂_c x⟫.re ≤ 1 − δ` is NOT
discharged and is NOT a consequence of the
identification: `GapBoundU1` bounds the `ℂ`-spectrum
of the pre-completion `transferOp` on `osSpace`, and
transporting a spectral bound on that space to a
pairing bound for the completed `T̂_c` is a separate
step that is not in the landed record. It remains the
correspondence's one named open clause.
-/

import ThetLogos.LatticeSliceYosida
import ThetLogos.LatticeSliceCfc
import ThetLogos.SliceBattery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries

namespace ThetLogos

open MeasureTheory Finset Filter
open scoped Matrix ENNReal NNReal InnerProduct Nat
  Topology

section SliceIdentify

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §0. The resolvent spectral function

`g_λ(μ) = (λ − log μ)⁻¹` for `μ > 0`, extended by
`g_λ(0) = 0` — the spectral function of `(Ĥ + λ)⁻¹`
under the identification `Ĥ = −log T̂_c`. The extension
value at `0` is forced by continuity:
`(λ − log μ)⁻¹ → 0` as `μ → 0⁺`. -/

/-- **The resolvent spectral function** `g_λ`: the
function of `T̂_c` that Step A identifies with the
resolvent `R_λ`. -/
noncomputable def sliceIdFun (lam μ : ℝ) : ℝ :=
  if μ = 0 then 0 else (lam - Real.log μ)⁻¹

/-- The extension value at `0`. -/
theorem sliceIdFun_zero (lam : ℝ) :
    sliceIdFun lam 0 = 0 := if_pos rfl

/-- On `(0, ∞)` the function is the plain formula. -/
theorem sliceIdFun_of_ne_zero (lam : ℝ) {μ : ℝ}
    (hμ : μ ≠ 0) :
    sliceIdFun lam μ = (lam - Real.log μ)⁻¹ :=
  if_neg hμ

/-- `0 ≤ g_λ` on `[0, 1]` for `λ > 0`. -/
theorem sliceIdFun_nonneg {lam : ℝ} (hlam : 0 < lam)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sliceIdFun lam μ := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [sliceIdFun_zero]
  · rw [sliceIdFun_of_ne_zero lam hμ0]
    refine inv_nonneg.mpr ?_
    have hlog : Real.log μ ≤ 0 :=
      Real.log_nonpos hμ.1 hμ.2
    linarith

/-- `g_λ ≤ λ⁻¹` on `[0, 1]` for `λ > 0`. -/
theorem sliceIdFun_le {lam : ℝ} (hlam : 0 < lam)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    sliceIdFun lam μ ≤ lam⁻¹ := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [sliceIdFun_zero]
    exact inv_nonneg.mpr hlam.le
  · rw [sliceIdFun_of_ne_zero lam hμ0]
    have hlog : Real.log μ ≤ 0 :=
      Real.log_nonpos hμ.1 hμ.2
    have hle : lam ≤ lam - Real.log μ := by linarith
    exact inv_anti₀ hlam hle

/-- `g_λ` is continuous on `[0, 1]` for `λ > 0`
(the point `0` is the only work: the formula's limit
there is the extension value). -/
theorem sliceIdFun_continuousOn {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (sliceIdFun lam) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases hx0 : x = 0
  · -- Continuity at the left endpoint `0`, by an
    -- explicit `ε`-`δ` argument with
    -- `δ = exp (λ − ε⁻¹)`.
    subst hx0
    rw [ContinuousWithinAt, sliceIdFun_zero,
      Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨Real.exp (lam - ε⁻¹), Real.exp_pos _,
      fun y hyIcc hydist => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg hyIcc.1] at hydist
    rw [Real.dist_eq, sub_zero]
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [sliceIdFun_zero, abs_zero]; exact hε
    · have hypos : 0 < y := lt_of_le_of_ne hyIcc.1
        (Ne.symm hy0)
      have hloglt : Real.log y < lam - ε⁻¹ := by
        have h := Real.log_lt_log hypos hydist
        rwa [Real.log_exp] at h
      have hpos : 0 < lam - Real.log y := by
        have hlog : Real.log y ≤ 0 :=
          Real.log_nonpos hyIcc.1 hyIcc.2
        linarith
      rw [sliceIdFun_of_ne_zero lam hy0,
        abs_of_pos (inv_pos.mpr hpos), inv_eq_one_div,
        div_lt_iff₀ hpos]
      have h1 : ε⁻¹ < lam - Real.log y := by linarith
      have h2 := mul_lt_mul_of_pos_left h1 hε
      rwa [mul_inv_cancel₀ (ne_of_gt hε)] at h2
  · -- At `x ∈ (0, 1]` the plain formula is continuous,
    -- and it agrees with `g_λ` near `x` inside the
    -- interval.
    have hxpos : 0 < x := lt_of_le_of_ne hx.1
      (Ne.symm hx0)
    have hcontAt : ContinuousAt
        (fun μ : ℝ => (lam - Real.log μ)⁻¹) x := by
      refine ContinuousAt.inv₀
        (continuousAt_const.sub
          (Real.continuousAt_log hx0)) ?_
      have hlog : Real.log x ≤ 0 :=
        Real.log_nonpos hx.1 hx.2
      exact ne_of_gt (by linarith)
    have hval : sliceIdFun lam x
        = (lam - Real.log x)⁻¹ :=
      sliceIdFun_of_ne_zero lam hx0
    refine Filter.Tendsto.congr'
      (f₁ := fun μ : ℝ => (lam - Real.log μ)⁻¹) ?_ ?_
    · exact mem_nhdsWithin.mpr ⟨Set.Ioi (0 : ℝ),
        isOpen_Ioi, hxpos, fun y hy =>
          (sliceIdFun_of_ne_zero lam (ne_of_gt hy.1)).symm⟩
    · rw [hval]; exact hcontAt.continuousWithinAt

/-! ## §1. The truncated logarithm series

`T_K(μ) = Σ_{j=1}^K (1/j)(1−μ)^j`, the `K`-th partial
sum of `−log μ = Σ_{j≥1} (1/j)(1−μ)^j` on `(0, 1]`.
Two facts drive everything below: the partial sums
increase to `−log μ`, and the tail is geometrically
small against the defect: `−log μ − T_K(μ) ≤
(1−μ)^K · (−log μ)`. -/

/-- **The truncated logarithm** `T_K`, as a bare
real function (the same function whose `cfc` pairing
is `sliceHamFormApproxC`, by FG-2c-0's
`sliceApproxC_eq`). -/
noncomputable def sliceLogApproxFun (K : ℕ) (μ : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * (1 - μ) ^ j

/-- `T_K ≥ 0` on `[0, 1]`. -/
theorem sliceLogApproxFun_nonneg (K : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sliceLogApproxFun K μ := by
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))
    (pow_nonneg (sub_nonneg.mpr hμ.2) j)

/-- `T_K` as a sum over `range K` of the log-series
terms `(1−μ)^{n+1}/(n+1)`. -/
theorem sliceLogApproxFun_eq_sum_range (K : ℕ) (μ : ℝ) :
    sliceLogApproxFun K μ
      = ∑ n ∈ Finset.range K,
          (1 - μ) ^ (n + 1) / ((n : ℝ) + 1) := by
  induction K with
  | zero =>
    unfold sliceLogApproxFun
    rw [show (Finset.Icc 1 0 : Finset ℕ) = ∅ by decide,
      Finset.sum_empty, Finset.sum_range_zero]
  | succ k ih =>
    have hstep : (∑ j ∈ Finset.Icc 1 k,
          (j : ℝ)⁻¹ * (1 - μ) ^ j)
        = ∑ n ∈ Finset.range k,
            (1 - μ) ^ (n + 1) / ((n : ℝ) + 1) := ih
    show (∑ j ∈ Finset.Icc 1 (k + 1),
        (j : ℝ)⁻¹ * (1 - μ) ^ j) = _
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ)
      ≤ k + 1) _, hstep, Finset.sum_range_succ]
    congr 1
    rw [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    ring

/-- The log-series sum at `1 − μ`. -/
theorem sliceId_hasSum {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    HasSum (fun n : ℕ => (1 - μ) ^ (n + 1)
        / ((n : ℝ) + 1)) (- Real.log μ) := by
  have hlt : |(1 : ℝ) - μ| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hμ.2)]
    have hpos : (0 : ℝ) < μ :=
      lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
    linarith
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hlt
  rwa [show (1 : ℝ) - (1 - μ) = μ by ring] at h

/-- **Partial sums are below the limit**: `T_K(μ) ≤
−log μ` on `(0, 1]`. -/
theorem sliceLogApproxFun_le (K : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    sliceLogApproxFun K μ ≤ - Real.log μ := by
  have hsum := sliceId_hasSum hμ hμ0
  rw [sliceLogApproxFun_eq_sum_range]
  refine le_trans (Summable.sum_le_tsum (Finset.range K)
    (fun n _ => div_nonneg
      (pow_nonneg (sub_nonneg.mpr hμ.2) _)
      (by positivity)) hsum.summable)
    (le_of_eq hsum.tsum_eq)

/-- **The tail bound**: `−log μ − T_K(μ) ≤
(1−μ)^K · (−log μ)` on `(0, 1]`. -/
theorem sliceLogApproxFun_tail_le (K : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    - Real.log μ - sliceLogApproxFun K μ
      ≤ (1 - μ) ^ K * (- Real.log μ) := by
  have hsum := sliceId_hasSum hμ hμ0
  have hsumm := hsum.summable
  have htsum : ∑' n : ℕ, (1 - μ) ^ (n + 1)
        / ((n : ℝ) + 1) = - Real.log μ := hsum.tsum_eq
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun m : ℕ => (1 - μ) ^ (m + 1)
      / ((m : ℝ) + 1)) K hsumm
  rw [htsum] at hsplit
  have htail : - Real.log μ - sliceLogApproxFun K μ
      = ∑' n : ℕ, (1 - μ) ^ (n + K + 1)
          / (((n + K : ℕ) : ℝ) + 1) := by
    rw [sliceLogApproxFun_eq_sum_range]
    linarith [hsplit]
  have h1m : (0 : ℝ) ≤ 1 - μ := sub_nonneg.mpr hμ.2
  have hsummA : Summable (fun n : ℕ =>
      (1 - μ) ^ (n + K + 1) / (((n + K : ℕ) : ℝ) + 1)) :=
    (summable_nat_add_iff K).mpr hsumm
  rw [htail]
  refine le_trans (Summable.tsum_le_tsum
    (f := fun n : ℕ => (1 - μ) ^ (n + K + 1)
      / (((n + K : ℕ) : ℝ) + 1))
    (g := fun n : ℕ => (1 - μ) ^ K
      * ((1 - μ) ^ (n + 1) / ((n : ℝ) + 1)))
    ?_ hsummA (hsumm.mul_left ((1 - μ) ^ K))) ?_
  · intro n
    show (1 - μ) ^ (n + K + 1) / (((n + K : ℕ) : ℝ) + 1)
        ≤ (1 - μ) ^ K * ((1 - μ) ^ (n + 1)
          / ((n : ℝ) + 1))
    rw [Nat.cast_add]
    have hfact : (1 - μ) ^ (n + K + 1)
        = (1 - μ) ^ K * (1 - μ) ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hfact, div_eq_mul_inv, div_eq_mul_inv,
      ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (pow_nonneg h1m K) (pow_nonneg h1m _))
    refine inv_anti₀ (by positivity :
      (0 : ℝ) < (n : ℝ) + 1) ?_
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  · rw [tsum_mul_left, htsum]

/-- `T_K` is (the restriction of) a polynomial, hence
continuous on the whole line. -/
theorem sliceLogApproxFun_continuous (K : ℕ) :
    Continuous (sliceLogApproxFun K) := by
  unfold sliceLogApproxFun
  refine continuous_finsetSum _ fun j _ => ?_
  fun_prop

/-! ## §2. Restriction to `H'` and the pairing identity

Every `cfc` operator of `T̂_c` preserves the kernel of
`T̂_c` (it commutes with `T̂_c = cfc id`) and therefore
preserves `H' = (ker T̂_c)ᗮ` (it is self-adjoint).
So every `cfc` operator restricts to a continuous
linear map on the carrier `H'`, with no continuity
hypothesis on the function: the calculus only ever
sees the spectrum. -/

/-- **Restriction**: an ambient operator preserving
`H'` restricts to a continuous linear map on `H'`. -/
noncomputable def sliceRestrictOf (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (F : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hF : ∀ z ∈ sliceFormClosure μG ρ hN2 hρcont hN β
        hpos,
      F z ∈ sliceFormClosure μG ρ hN2 hρcont hN β hpos) :
    (↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
  (F.comp (sliceFormClosure μG ρ hN2 hρcont hN β
    hpos).subtypeL).codRestrict _ fun x => hF x.1 x.2

/-- The restriction's ambient value is the original
operator's value. -/
theorem sliceRestrictOf_apply_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (F : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hF : ∀ z ∈ sliceFormClosure μG ρ hN2 hρcont hN β
        hpos,
      F z ∈ sliceFormClosure μG ρ hN2 hρcont hN β hpos)
    (x : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceRestrictOf μG ρ hN2 hρcont hN β hpos F hF)
      x).1 = F x.1 := rfl

/-- **`cfc` preserves the kernel**: `cfc f T̂_c` maps
`ker T̂_c` into itself, since it commutes with
`T̂_c = cfc id`. -/
theorem sliceCfc_preserves_ker (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ℝ → ℝ) {z : sliceHilbertSpace μG ρ hN2 hρcont
      hN β hpos}
    (hz : z ∈ sliceKerTc μG ρ hN2 hρcont hN β hpos) :
    (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)) z
      ∈ sliceKerTc μG ρ hN2 hρcont hN β hpos := by
  rw [sliceKerTc_mem_iff μG ρ hN2 hρcont hN β hpos] at *
  have hcomm := (cfc_commute_cfc (fun μ : ℝ => μ)
    f (sliceTc μG ρ hN2 hρcont hN β hpos)).eq
  rw [sliceCfc_id μG ρ hN2 hρcont hN β hpos] at hcomm
  have happ := DFunLike.congr_fun hcomm z
  rw [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply] at happ
  rw [happ, hz, map_zero]

/-- **`cfc` preserves `H'`**: `cfc f T̂_c` maps
`H' = (ker T̂_c)ᗮ` into itself, since it is
self-adjoint and preserves the kernel. -/
theorem sliceCfc_preserves_closure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ℝ → ℝ) {z : sliceHilbertSpace μG ρ hN2 hρcont
      hN β hpos}
    (hz : z ∈ sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :
    (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)) z
      ∈ sliceFormClosure μG ρ hN2 hρcont hN β hpos := by
  rw [sliceFormClosure_eq_ker_orthogonal μG ρ hN2
    hρcont hN β hpos] at hz ⊢
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro u hu
  rw [← sliceSelfAdjoint_inner_move μG ρ hN2 hρcont
    hN β hpos (sliceCfc_isSelfAdjoint μG ρ hN2 hρcont
      hN β hpos f) u z]
  exact hz _ (sliceCfc_preserves_ker μG ρ hN2 hρcont
    hN β hpos f hu)

/-- **The restricted `cfc` operator** on `H'`. -/
noncomputable def sliceCfcRestrict (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ℝ → ℝ) :
    (↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
  sliceRestrictOf μG ρ hN2 hρcont hN β hpos
    (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
    (fun z hz => sliceCfc_preserves_closure μG ρ hN2
      hρcont hN β hpos f hz)

/-- The restricted `cfc` operator's ambient value. -/
theorem sliceCfcRestrict_apply_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : ℝ → ℝ)
    (x : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceCfcRestrict μG ρ hN2 hρcont hN β hpos f)
      x).1
      = (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos))
          x.1 :=
  sliceRestrictOf_apply_coe μG ρ hN2 hρcont hN β hpos
    _ _ x

/-- `T̂_c` itself preserves `H'`. -/
theorem sliceTc_preserves_closure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hz : z ∈ sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :
    (sliceTc μG ρ hN2 hρcont hN β hpos) z
      ∈ sliceFormClosure μG ρ hN2 hρcont hN β hpos := by
  have h := sliceCfc_preserves_closure μG ρ hN2 hρcont
    hN β hpos (fun μ : ℝ => μ) hz
  rwa [sliceCfc_id μG ρ hN2 hρcont hN β hpos] at h

/-- **The restricted transfer operator** `T̂_c|_{H'}`:
the right-hand side of the identification. -/
noncomputable def sliceTcRestrict (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (↥(sliceFormClosure μG ρ hN2 hρcont hN β hpos))
      →L[ℂ] ↥(sliceFormClosure μG ρ hN2 hρcont hN β
        hpos) :=
  sliceRestrictOf μG ρ hN2 hρcont hN β hpos
    (sliceTc μG ρ hN2 hρcont hN β hpos)
    (fun z hz => sliceTc_preserves_closure μG ρ hN2
      hρcont hN β hpos hz)

/-- The restricted transfer operator's ambient value. -/
theorem sliceTcRestrict_apply_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceTcRestrict μG ρ hN2 hρcont hN β hpos) x).1
      = (sliceTc μG ρ hN2 hρcont hN β hpos) x.1 :=
  sliceRestrictOf_apply_coe μG ρ hN2 hρcont hN β hpos
    _ _ x

/-- **The polarized identity**: the polarized
approximant is the `cfc` pairing of the truncated
logarithm,
`sliceApproxB K x y = ⟪x, cfc (T_K) T̂_c y⟫`.
The complex (un-real-parted) form of FG-2c-0's
`sliceApproxC_eq`. -/
theorem sliceApproxB_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K x y
      = inner ℂ x (cfc (sliceLogApproxFun K)
          (sliceTc μG ρ hN2 hρcont hN β hpos) y) := by
  have hfun : sliceLogApproxFun K
      = (fun μ : ℝ => ∑ j ∈ Finset.Icc 1 K,
          (j : ℝ)⁻¹ * (1 - μ) ^ j) := rfl
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      inner ℂ x (cfc (fun μ : ℝ => (j : ℝ)⁻¹
          * (1 - μ) ^ j)
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)
        = (↑((j : ℝ)⁻¹) : ℂ) * inner ℂ x
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
            hN β hpos))^[j] y) := by
    intro j _
    rw [cfc_const_mul _ _ _ (by fun_prop),
      sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos j,
      Algebra.smul_def, ContinuousLinearMap.mul_apply,
      sliceAlgebraMap_apply μG ρ hN2 hρcont hN β hpos,
      inner_smul_right, sliceAc_pow_apply μG ρ hN2
        hρcont hN β hpos j]
  show (∑ j ∈ Finset.Icc 1 K, (↑((j : ℝ)⁻¹) : ℂ)
      * inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos))^[j] y)) = _
  rw [hfun, sliceCfc_sum μG ρ hN2 hρcont hN β hpos
      (Finset.Icc 1 K)
      (fun j μ => (j : ℝ)⁻¹ * (1 - μ) ^ j)
      (fun j _ => by fun_prop),
    sliceSum_apply μG ρ hN2 hρcont hN β hpos
      (Finset.Icc 1 K) _ y, inner_sum]
  exact Finset.sum_congr rfl fun j hj => (hterm j hj).symm

/-! ## §2b. The resolvent defect function

`ψ_{λ,K} = 1 − g_λ·(T_K + λ)`. On `(0, 1]` it factors
as `g_λ · (−log − T_K)` (since `g_λ·(λ − log) = 1`
there), and the tail bound of §1 gives
`0 ≤ ψ_{λ,K} ≤ (1−μ)^K` on all of `[0, 1]` — at
`μ = 0` both sides are `1`. It is continuous on
`[0, 1]`, being built from `g_λ` and a polynomial. -/

/-- **The resolvent defect function** `ψ_{λ,K}`. -/
noncomputable def sliceIdDefectFun (lam : ℝ) (K : ℕ)
    (μ : ℝ) : ℝ :=
  1 - sliceIdFun lam μ * (sliceLogApproxFun K μ + lam)

/-- At `μ = 0` the defect is `1`, matching the bound
`(1−μ)^K`. -/
theorem sliceIdDefectFun_zero (lam : ℝ) (K : ℕ) :
    sliceIdDefectFun lam K 0 = 1 := by
  unfold sliceIdDefectFun
  rw [sliceIdFun_zero]
  ring

/-- **The factorization** on `(0, 1]`:
`ψ_{λ,K} = g_λ · (−log − T_K)`. -/
theorem sliceIdDefectFun_factor {lam : ℝ} (K : ℕ)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hμ0 : μ ≠ 0) (hlam : 0 < lam) :
    sliceIdDefectFun lam K μ
      = sliceIdFun lam μ
        * (- Real.log μ - sliceLogApproxFun K μ) := by
  unfold sliceIdDefectFun
  have hg : sliceIdFun lam μ * (lam - Real.log μ)
      = 1 := by
    rw [sliceIdFun_of_ne_zero lam hμ0]
    refine inv_mul_cancel₀ (ne_of_gt ?_)
    have hlog : Real.log μ ≤ 0 :=
      Real.log_nonpos hμ.1 hμ.2
    linarith
  calc 1 - sliceIdFun lam μ
        * (sliceLogApproxFun K μ + lam)
      = sliceIdFun lam μ * (lam - Real.log μ)
        - sliceIdFun lam μ
          * (sliceLogApproxFun K μ + lam) := by
          rw [hg]
    _ = sliceIdFun lam μ
          * (- Real.log μ
            - sliceLogApproxFun K μ) := by ring

/-- `0 ≤ ψ_{λ,K}` on `[0, 1]`. -/
theorem sliceIdDefectFun_nonneg {lam : ℝ}
    (hlam : 0 < lam) (K : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sliceIdDefectFun lam K μ := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [sliceIdDefectFun_zero]; exact zero_le_one
  · rw [sliceIdDefectFun_factor K hμ hμ0 hlam]
    exact mul_nonneg (sliceIdFun_nonneg hlam hμ)
      (sub_nonneg.mpr (sliceLogApproxFun_le K hμ hμ0))

/-- `ψ_{λ,K} ≤ (1−μ)^K` on `[0, 1]`. -/
theorem sliceIdDefectFun_le {lam : ℝ} (hlam : 0 < lam)
    (K : ℕ) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    sliceIdDefectFun lam K μ ≤ (1 - μ) ^ K := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [sliceIdDefectFun_zero]
    simp
  · rcases eq_or_ne μ 1 with rfl | hμ1
    · -- At `μ = 1`: `T_K 1 = 0` and `g_λ(1)·λ = 1`, so
      -- the defect vanishes.
      have hTK : sliceLogApproxFun K 1 = 0 := by
        unfold sliceLogApproxFun
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        rw [show (1 : ℝ) - 1 = 0 by ring,
          zero_pow (by omega : j ≠ 0), mul_zero]
      have hg1 : sliceIdFun lam 1 = lam⁻¹ := by
        rw [sliceIdFun_of_ne_zero lam (by norm_num),
          Real.log_one, sub_zero]
      unfold sliceIdDefectFun
      rw [hg1, hTK]
      have : lam⁻¹ * (0 + lam) = 1 := by
        rw [zero_add]
        exact inv_mul_cancel₀ (ne_of_gt hlam)
      rw [this]
      have h5 : (0 : ℝ) ≤ (1 - 1) ^ K :=
        pow_nonneg (by norm_num) K
      linarith
    · have hμpos : 0 < μ :=
        lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
      have hlogneg : Real.log μ < 0 :=
        Real.log_neg hμpos (lt_of_le_of_ne hμ.2 hμ1)
      rw [sliceIdDefectFun_factor K hμ hμ0 hlam]
      have hgR : sliceIdFun lam μ * (- Real.log μ)
          ≤ 1 := by
        rw [sliceIdFun_of_ne_zero lam hμ0]
        have h1 : (lam - Real.log μ)⁻¹
            ≤ (- Real.log μ)⁻¹ :=
          inv_anti₀ (by linarith) (by linarith)
        have h2 := mul_le_mul_of_nonneg_right h1
          (le_of_lt (by linarith : (0:ℝ) < - Real.log μ))
        rwa [inv_mul_cancel₀
          (ne_of_gt (by linarith : (0:ℝ)
            < - Real.log μ))] at h2
      calc sliceIdFun lam μ
            * (- Real.log μ - sliceLogApproxFun K μ)
          ≤ sliceIdFun lam μ * ((1 - μ) ^ K
              * (- Real.log μ)) :=
            mul_le_mul_of_nonneg_left
              (sliceLogApproxFun_tail_le K hμ hμ0)
              (sliceIdFun_nonneg hlam hμ)
        _ = (1 - μ) ^ K * (sliceIdFun lam μ
              * (- Real.log μ)) := by ring
        _ ≤ (1 - μ) ^ K * 1 :=
            mul_le_mul_of_nonneg_left hgR
              (pow_nonneg (sub_nonneg.mpr hμ.2) K)
        _ = (1 - μ) ^ K := mul_one _

/-- `ψ_{λ,K}` is continuous on `[0, 1]`. -/
theorem sliceIdDefectFun_continuousOn {lam : ℝ}
    (hlam : 0 < lam) (K : ℕ) :
    ContinuousOn (sliceIdDefectFun lam K)
      (Set.Icc (0 : ℝ) 1) := by
  show ContinuousOn (fun μ : ℝ => 1
    - sliceIdFun lam μ * (sliceLogApproxFun K μ + lam))
    (Set.Icc (0 : ℝ) 1)
  exact continuousOn_const.sub
    ((sliceIdFun_continuousOn hlam).mul
      ((sliceLogApproxFun_continuous K).continuousOn.add
        continuousOn_const))

/-- **The `g_λ²·T_K` bound**: `g_λ(μ)²·T_K(μ) ≤
(4λ)⁻¹` on `[0, 1]` — from `T_K ≤ −log μ` and
`t/(λ+t)² ≤ 1/(4λ)` (i.e. `(λ−t)² ≥ 0`). -/
theorem sliceIdFun_sq_mul_le {lam : ℝ} (hlam : 0 < lam)
    (K : ℕ) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    sliceIdFun lam μ ^ 2 * sliceLogApproxFun K μ
      ≤ (4 * lam)⁻¹ := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [sliceIdFun_zero]
    have h1 : (0 : ℝ) ^ 2 * sliceLogApproxFun K 0
        = 0 := by simp
    rw [h1]
    exact inv_nonneg.mpr (by linarith)
  · have hlog : Real.log μ ≤ 0 :=
      Real.log_nonpos hμ.1 hμ.2
    have hstep : sliceIdFun lam μ ^ 2
          * sliceLogApproxFun K μ
        ≤ sliceIdFun lam μ ^ 2 * (- Real.log μ) :=
      mul_le_mul_of_nonneg_left
        (sliceLogApproxFun_le K hμ hμ0) (sq_nonneg _)
    refine le_trans hstep ?_
    rw [sliceIdFun_of_ne_zero lam hμ0, inv_pow,
      show ((lam - Real.log μ) ^ 2)⁻¹ * (- Real.log μ)
        = (- Real.log μ) / (lam - Real.log μ) ^ 2 from
        by rw [div_eq_mul_inv, mul_comm]]
    rw [div_le_iff₀ (sq_pos_of_pos
        (show (0:ℝ) < lam - Real.log μ by linarith)),
      le_inv_mul_iff₀' (by positivity :
        (0:ℝ) < 4 * lam)]
    nlinarith [sq_nonneg (lam + Real.log μ)]

/-! ## §2c. Pairing monotonicity and the
Cauchy–Schwarz bound for the defect pairings -/

/-- **Pairing monotonicity from a pointwise bound on
`[0, 1]`** (the landed `sliceCfc_pairing_mono` asks
for global continuity; here both functions are only
needed on the spectrum's housing interval). -/
theorem sliceCfc_pairing_mono_of_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (fa fb : ℝ → ℝ)
    (hfa : ContinuousOn fa (Set.Icc (0 : ℝ) 1))
    (hfb : ContinuousOn fb (Set.Icc (0 : ℝ) 1))
    (hle : ∀ μ ∈ Set.Icc (0 : ℝ) 1, fa μ ≤ fb μ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :
    (inner ℂ x (cfc fa (sliceTc μG ρ hN2 hρcont hN β
        hpos) x)).re
      ≤ (inner ℂ x (cfc fb (sliceTc μG ρ hN2 hρcont hN
          β hpos) x)).re := by
  have hsub : spectrum ℝ (sliceTc μG ρ hN2 hρcont hN
      β hpos) ⊆ Set.Icc (0 : ℝ) 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hnn := sliceCfc_pairing_nonneg μG ρ hN2 hρcont
    hN β hpos (fun μ => fb μ - fa μ)
    (fun μ hμ => sub_nonneg.mpr (hle μ hμ)) x
  rw [cfc_sub fb fa _ (hfb.mono hsub) (hfa.mono hsub),
    ContinuousLinearMap.sub_apply, inner_sub_right,
    Complex.sub_re] at hnn
  linarith

/-- **The `√`-Cauchy–Schwarz bound** for a positive
`cfc` pairing:
`‖⟪x, cfc ψ y⟫‖ ≤ √(⟪x, cfc ψ x⟫.re) ·
√(⟪y, cfc ψ y⟫.re)`. -/
theorem sliceCfc_pairing_abs_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (ψ : ℝ → ℝ)
    (hψcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hψ : ∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ μ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :
    ‖inner ℂ x (cfc ψ (sliceTc μG ρ hN2 hρcont hN β
        hpos) y)‖
      ≤ Real.sqrt ((inner ℂ x (cfc ψ
            (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re)
        * Real.sqrt ((inner ℂ y (cfc ψ
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            y)).re) := by
  have hsub : spectrum ℝ (sliceTc μG ρ hN2 hρcont hN
      β hpos) ⊆ Set.Icc (0 : ℝ) 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  set A := cfc (fun μ => Real.sqrt (ψ μ))
    (sliceTc μG ρ hN2 hρcont hN β hpos) with hA
  have hcont : ContinuousOn (fun μ => Real.sqrt (ψ μ))
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (Real.continuous_sqrt.comp_continuousOn
      hψcont).mono hsub
  have hsq : cfc ψ (sliceTc μG ρ hN2 hρcont hN β hpos)
      = A * A := by
    rw [hA, ← cfc_mul _ _ _ hcont hcont]
    refine cfc_congr fun μ hμ => ?_
    exact (Real.mul_self_sqrt
      (hψ μ (hsub hμ))).symm
  have hmove : ∀ u v, inner ℂ u (cfc ψ
        (sliceTc μG ρ hN2 hρcont hN β hpos) v)
      = inner ℂ (A u) (A v) := by
    intro u v
    rw [hsq, ContinuousLinearMap.mul_apply]
    exact (sliceSelfAdjoint_inner_move μG ρ hN2
      hρcont hN β hpos (sliceCfc_isSelfAdjoint μG ρ
        hN2 hρcont hN β hpos _) u (A v)).symm
  have hnorm : ∀ z, ‖A z‖ = Real.sqrt
      ((inner ℂ z (cfc ψ (sliceTc μG ρ hN2 hρcont hN
        β hpos) z)).re) := by
    intro z
    have hsq2 : ‖A z‖ ^ 2 = (inner ℂ z (cfc ψ
          (sliceTc μG ρ hN2 hρcont hN β hpos) z)).re := by
      have e1 : (inner ℂ (A z) (A z)).re
          = (inner ℂ z (cfc ψ (sliceTc μG ρ hN2 hρcont
              hN β hpos) z)).re :=
        congrArg Complex.re (hmove z z).symm
      have h2 : (inner ℂ (A z) (A z))
          = ((‖A z‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        exact (Complex.ofReal_pow ‖A z‖ 2).symm
      rw [h2, Complex.ofReal_re] at e1
      exact e1
    calc ‖A z‖ = Real.sqrt (‖A z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by rw [hsq2]
  rw [hmove x y]
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [hnorm x, hnorm y]

/-- **The defect pairings vanish on `H'`**: for
`y ∈ H'`,
`⟪x, cfc (ψ_{λ,K}) T̂_c y⟫ → 0` as `K → ∞`, by the
`√`-Cauchy–Schwarz bound, `ψ_{λ,K} ≤ (1−μ)^K`, and
the defect-orbit theorem. This is the analytic heart
of Step A. -/
theorem sliceIdDefect_pairing_tendsto_zero
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {lam : ℝ} (hlam : 0 < lam)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    {y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hy : y ∈ sliceFormClosure μG ρ hN2 hρcont hN β
      hpos) :
    Filter.Tendsto (fun K => inner ℂ x
        (cfc (sliceIdDefectFun lam K)
          (sliceTc μG ρ hN2 hρcont hN β hpos) y))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun K => ‖x‖
    * Real.sqrt (‖y‖ * ‖((sliceAc μG ρ hN2 hρcont
        hN β hpos) ^ K) y‖)) (fun K => norm_nonneg _)
    ?_ ?_
  · intro K
    refine le_trans (sliceCfc_pairing_abs_le μG ρ hN2
      hρcont hN β hpos (sliceIdDefectFun lam K)
      (sliceIdDefectFun_continuousOn hlam K)
      (fun μ hμ => sliceIdDefectFun_nonneg hlam K hμ)
      x y) ?_
    have hfx : Real.sqrt ((inner ℂ x
          (cfc (sliceIdDefectFun lam K)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            x)).re) ≤ ‖x‖ := by
      have hmono := sliceCfc_pairing_mono_of_le μG ρ
        hN2 hρcont hN β hpos (sliceIdDefectFun lam K)
        (fun _ : ℝ => 1)
        (sliceIdDefectFun_continuousOn hlam K)
        continuousOn_const
        (fun μ hμ => le_trans
          (sliceIdDefectFun_le hlam K hμ)
          (pow_le_one₀ (sub_nonneg.mpr hμ.2)
            (by linarith [hμ.1]))) x
      rw [sliceCfc_pairing_const μG ρ hN2 hρcont hN β
        hpos 1 x, one_mul] at hmono
      refine le_trans (Real.sqrt_le_sqrt hmono) ?_
      rw [Real.sqrt_sq (norm_nonneg x)]
    have hfy : Real.sqrt ((inner ℂ y
          (cfc (sliceIdDefectFun lam K)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            y)).re)
        ≤ Real.sqrt (‖y‖
          * ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K)
              y‖) := by
      refine Real.sqrt_le_sqrt ?_
      have hmono := sliceCfc_pairing_mono_of_le μG ρ
        hN2 hρcont hN β hpos (sliceIdDefectFun lam K)
        (fun μ : ℝ => (1 - μ) ^ K)
        (sliceIdDefectFun_continuousOn hlam K)
        (by fun_prop) (fun μ hμ =>
          sliceIdDefectFun_le hlam K hμ) y
      rw [sliceCfc_defect_pow μG ρ hN2 hρcont hN β
        hpos K] at hmono
      refine le_trans hmono ?_
      refine le_trans (Complex.re_le_norm _) ?_
      exact norm_inner_le_norm _ _
    refine mul_le_mul hfx hfy (Real.sqrt_nonneg _)
      (norm_nonneg x)
  · have horbit : Filter.Tendsto (fun K =>
        ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K) y)
        Filter.atTop (nhds 0) :=
      sliceAc_pow_tendsto_zero μG ρ hN2 hρcont hN β
        hpos y (by
          rwa [sliceFormClosure_eq_ker_orthogonal μG ρ
            hN2 hρcont hN β hpos] at hy)
    have h2 : Filter.Tendsto (fun K => ‖y‖
          * ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K)
              y‖) Filter.atTop (nhds (‖y‖ * 0)) := by
      have h : Filter.Tendsto (fun K => ‖y‖
            * ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K)
                y‖) Filter.atTop
          (nhds (‖y‖ * ‖(0 :
            sliceHilbertSpace μG ρ hN2 hρcont hN β
            hpos)‖)) :=
        tendsto_const_nhds.mul horbit.norm
      simpa using h
    have h3 : Filter.Tendsto (fun K => Real.sqrt (‖y‖
          * ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K)
              y‖)) Filter.atTop
        (nhds (Real.sqrt (‖y‖ * 0))) :=
      (Real.continuous_sqrt.tendsto _).comp h2
    have h4 : Filter.Tendsto (fun K => ‖x‖
          * Real.sqrt (‖y‖
            * ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ K)
                y‖)) Filter.atTop
        (nhds (‖x‖ * Real.sqrt (‖y‖ * 0))) :=
      tendsto_const_nhds.mul h3
    simpa using h4

/-! ## §3. Step A — the resolvent is the cfc of `g_λ`

The Yosida resolvent `R_λ` of FG-2c-1/FG-2c-3 is the
Riesz representative of the `J_λ` pairing. The
candidate `G_λ x := cfc (g_λ) T̂_c x` (ambient) lies in
the form domain (§3.1, by the uniform bound
`q_K(G_λ x) ≤ (4λ)⁻¹‖x‖²`) and satisfies the `J_λ`
identity exactly in the limit `K → ∞` (§3.2–3.3), the
defect pairing vanishing by §2c. Uniqueness of the
Riesz representative then gives `R_λ = G_λ|_{H'}`. -/

/-- **§3.1 — the candidate lands in the form domain**:
`cfc (g_λ) T̂_c x` has `sliceHamFormC` bounded by
`(4λ)⁻¹‖x‖²`, by self-adjointness of the cfc and
`g_λ² · T_K ≤ (4λ)⁻¹` on `[0,1]`. -/
theorem sliceIdFun_cfc_mem_formDomain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    (cfc (sliceIdFun lam)
        (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1
      ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β
        hpos := by
  rw [sliceHamC_mem_domain_iff μG ρ hN2 hρcont hN β
      hpos, sliceHamFormC_ne_top_iff μG ρ hN2 hρcont
      hN β hpos]
  refine ⟨(4 * lam)⁻¹ * ‖x.1‖ ^ 2, ?_⟩
  rintro _ ⟨K, rfl⟩
  show sliceHamFormApproxC μG ρ hN2 hρcont hN β
      hpos K ((cfc (sliceIdFun lam)
        (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
    ≤ (4 * lam)⁻¹ * ‖x.1‖ ^ 2
  have hfun : sliceLogApproxFun K
      = (fun μ => ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
          * (1 - μ) ^ j) := rfl
  have hq : sliceHamFormApproxC μG ρ hN2 hρcont hN β
        hpos K
        ((cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
      = (inner ℂ
          ((cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
          (cfc (sliceLogApproxFun K)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              x.1))).re := by
    have h := sliceApproxC_eq μG ρ hN2 hρcont hN β
      hpos K ((cfc (sliceIdFun lam)
        (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
    rwa [← hfun] at h
  rw [hq]
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hg : ContinuousOn (sliceIdFun lam)
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceIdFun_continuousOn hlam).mono hsub
  have hTK : ContinuousOn (sliceLogApproxFun K)
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceLogApproxFun_continuous K).continuousOn
      |>.mono hsub
  have hop : (cfc (sliceIdFun lam)
        (sliceTc μG ρ hN2 hρcont hN β hpos))
        ((cfc (sliceLogApproxFun K)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          ((cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1))
      = cfc (fun μ => sliceIdFun lam μ ^ 2
          * sliceLogApproxFun K μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) x.1 := by
    have e1 : (cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          * (cfc (sliceLogApproxFun K)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
        = cfc (fun μ => sliceIdFun lam μ
            * sliceLogApproxFun K μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) :=
      (cfc_mul _ _ _ hg hTK).symm
    have e2 : cfc (fun μ => sliceIdFun lam μ
            * sliceLogApproxFun K μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
          * (cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
        = cfc (fun μ => sliceIdFun lam μ ^ 2
            * sliceLogApproxFun K μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) := by
      have hF : (fun μ => sliceIdFun lam μ
            * sliceLogApproxFun K μ)
          = (sliceIdFun lam * sliceLogApproxFun K) := by
        funext μ
        exact (Pi.mul_apply _ _ μ).symm
      rw [hF, ← cfc_mul _ _ _ (hg.mul hTK) hg]
      congr 1
      funext μ
      rw [Pi.mul_apply]
      ring
    calc (cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          ((cfc (sliceLogApproxFun K)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              x.1))
        = (((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
            * (cfc (sliceLogApproxFun K)
              (sliceTc μG ρ hN2 hρcont hN β hpos)))
          * (cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)))
          x.1 := by
          rw [ContinuousLinearMap.mul_apply,
            ContinuousLinearMap.mul_apply]
      _ = cfc (fun μ => sliceIdFun lam μ ^ 2
            * sliceLogApproxFun K μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
          x.1 := by rw [e1, e2]
  rw [sliceSelfAdjoint_inner_move μG ρ hN2 hρcont hN
      β hpos
      (sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β
        hpos (sliceIdFun lam)) _ _, hop]
  refine le_trans (sliceCfc_pairing_mono_of_le μG ρ
      hN2 hρcont hN β hpos
      (fun μ => sliceIdFun lam μ ^ 2
        * sliceLogApproxFun K μ)
      (fun _ => (4 * lam)⁻¹)
      (((sliceIdFun_continuousOn hlam).pow
        2).mul (sliceLogApproxFun_continuous
        K).continuousOn) continuousOn_const
      (fun μ hμ => sliceIdFun_sq_mul_le hlam K hμ)
      x.1) ?_
  rw [sliceCfc_pairing_const μG ρ hN2 hρcont hN β
    hpos]

/-- **§3.2a — the polarized approximant of the
candidate**: `B_K(G_λ a, b)` is the pairing with
`cfc (g_λ · T_K)`. -/
theorem sliceApproxB_cfc_id (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (K : ℕ)
    (a b : sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :
    sliceApproxB μG ρ hN2 hρcont hN β hpos K
        ((cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos)) a) b
      = inner ℂ a (cfc (fun μ => sliceIdFun lam μ
          * sliceLogApproxFun K μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) b) := by
  rw [sliceApproxB_eq μG ρ hN2 hρcont hN β hpos,
    sliceSelfAdjoint_inner_move μG ρ hN2 hρcont hN β
      hpos
      (sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β
        hpos (sliceIdFun lam)) a]
  congr 1
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  rw [← ContinuousLinearMap.mul_apply,
    ← cfc_mul _ _ _
      ((sliceIdFun_continuousOn hlam).mono hsub)
      ((sliceLogApproxFun_continuous
        K).continuousOn.mono hsub)]

/-- **§3.2b — the exact per-`K` pairing identity**:
`⟪a, b⟫` splits into the polarized approximant at the
candidate, the `λ`-term, and the defect pairing. -/
theorem sliceId_pairing_identity (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) (K : ℕ)
    (a b : sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :
    inner ℂ a b
      = sliceApproxB μG ρ hN2 hρcont hN β hpos K
          ((cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) a) b
        + (lam : ℂ) * inner ℂ
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos)) a) b
        + inner ℂ a (cfc (sliceIdDefectFun lam K)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            b) := by
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hg : ContinuousOn (sliceIdFun lam)
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceIdFun_continuousOn hlam).mono hsub
  have h1 := sliceApproxB_cfc_id μG ρ hN2 hρcont hN
    β hpos lam hlam K a b
  have h2 : (lam : ℂ) * inner ℂ
        ((cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos)) a) b
      = inner ℂ a (cfc (fun μ => lam
          * sliceIdFun lam μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) b) := by
    rw [sliceSelfAdjoint_inner_move μG ρ hN2 hρcont
      hN β hpos
      (sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β
        hpos (sliceIdFun lam)) a b]
    have hcfc : cfc (fun μ => lam * sliceIdFun lam μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
        = (lam : ℝ) • (cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos)) :=
      cfc_const_mul lam (sliceIdFun lam)
        (sliceTc μG ρ hN2 hρcont hN β hpos) hg
    rw [hcfc, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_right]
    rfl
  have h3 : inner ℂ a (cfc (fun μ => sliceIdFun lam
            μ * sliceLogApproxFun K μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) b)
        + inner ℂ a (cfc (fun μ => lam
            * sliceIdFun lam μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) b)
        + inner ℂ a (cfc (sliceIdDefectFun lam K)
          (sliceTc μG ρ hN2 hρcont hN β hpos) b)
      = inner ℂ a b := by
    have hF1 : ContinuousOn (fun μ => sliceIdFun lam
          μ * sliceLogApproxFun K μ)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      hg.mul ((sliceLogApproxFun_continuous
        K).continuousOn.mono hsub)
    have hF2 : ContinuousOn (fun μ => lam
          * sliceIdFun lam μ)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      continuousOn_const.mul hg
    have hF3 : ContinuousOn (sliceIdDefectFun lam K)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      (sliceIdDefectFun_continuousOn hlam K).mono
        hsub
    have hF12 : ContinuousOn (fun μ => sliceIdFun
          lam μ * sliceLogApproxFun K μ
          + lam * sliceIdFun lam μ)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      hF1.add hF2
    rw [← inner_add_right, ← inner_add_right,
      ← ContinuousLinearMap.add_apply,
      ← ContinuousLinearMap.add_apply,
      ← cfc_add _ _ _ hF1 hF2, ← cfc_add _ _ _
        hF12 hF3]
    have hEqOn : Set.EqOn
        (fun μ => sliceIdFun lam μ
            * sliceLogApproxFun K μ
          + lam * sliceIdFun lam μ
          + sliceIdDefectFun lam K μ)
        (fun _ => (1 : ℝ))
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) := by
      intro μ _
      show sliceIdFun lam μ * sliceLogApproxFun
          K μ + lam * sliceIdFun lam μ
          + sliceIdDefectFun lam K μ = 1
      unfold sliceIdDefectFun
      ring
    rw [cfc_congr hEqOn, sliceCfc_const μG ρ hN2
      hρcont hN β hpos (1 : ℝ), map_one,
      ContinuousLinearMap.one_apply]
  rw [h1, h2]
  exact h3.symm

/-- **§3.3 — the candidate satisfies the `J_λ`
identity**: the per-`K` identity of §3.2b passes to
the limit by `sliceFormB_tendsto` and the vanishing
of the defect pairing (§2c). -/
theorem sliceResolvent_cfc_spec (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam)
    (x : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos))
    (v : sliceFormDomainLam μG ρ hN2 hρcont hN β
      hpos lam hlam) :
    sliceFormInnerLam μG ρ hN2 hρcont hN β hpos lam
        hlam
        (sliceFormDomainLam.ofSub μG ρ hN2 hρcont hN
          β hpos lam hlam
          ⟨(cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1,
            sliceIdFun_cfc_mem_formDomain μG ρ hN2
              hρcont hN β hpos lam hlam x⟩) v
      = inner ℂ x.1 v.val := by
  have hB := sliceFormB_tendsto μG ρ hN2 hρcont hN β
    hpos ⟨(cfc (sliceIdFun lam)
      (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1,
      sliceIdFun_cfc_mem_formDomain μG ρ hN2 hρcont
        hN β hpos lam hlam x⟩ v.toSub
  have hvan : Filter.Tendsto
      (fun K => inner ℂ x.1
        (cfc (sliceIdDefectFun lam K)
          (sliceTc μG ρ hN2 hρcont hN β hpos) v.val))
      Filter.atTop (nhds 0) :=
    sliceIdDefect_pairing_tendsto_zero μG ρ hN2
      hρcont hN β hpos hlam x.1
      (sliceFormDomain_le_closure μG ρ hN2 hρcont hN
        β hpos v.toSub.2)
  have hlim1 : Filter.Tendsto
      (fun K => sliceApproxB μG ρ hN2 hρcont hN β
          hpos K ((cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
          v.val
        + (lam : ℂ) * inner ℂ
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              x.1) v.val)
      Filter.atTop
      (nhds (sliceFormB μG ρ hN2 hρcont hN β hpos
          ⟨(cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1,
            sliceIdFun_cfc_mem_formDomain μG ρ hN2
              hρcont hN β hpos lam hlam x⟩ v.toSub
        + (lam : ℂ) * inner ℂ
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              x.1) v.val)) :=
    hB.add_const _
  have hlim2 : Filter.Tendsto
      (fun K => inner ℂ x.1 v.val
        - inner ℂ x.1
            (cfc (sliceIdDefectFun lam K)
              (sliceTc μG ρ hN2 hρcont hN β hpos)
              v.val))
      Filter.atTop
      (nhds (inner ℂ x.1 v.val - 0)) :=
    tendsto_const_nhds.sub hvan
  have heq : ∀ K, sliceApproxB μG ρ hN2 hρcont hN β
          hpos K ((cfc (sliceIdFun lam)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) x.1)
          v.val
        + (lam : ℂ) * inner ℂ
            ((cfc (sliceIdFun lam)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              x.1) v.val
      = inner ℂ x.1 v.val
        - inner ℂ x.1
            (cfc (sliceIdDefectFun lam K)
              (sliceTc μG ρ hN2 hρcont hN β hpos)
              v.val) := by
    intro K
    have hid := sliceId_pairing_identity μG ρ hN2
      hρcont hN β hpos lam hlam K x.1 v.val
    rw [hid]
    ring
  have hfin := tendsto_nhds_unique
    (Filter.Tendsto.congr heq hlim1) hlim2
  rw [sub_zero] at hfin
  exact hfin

/-- **Step A (headline)**: the Yosida resolvent at
every weight `λ > 0` is the restriction to `H'` of the
continuous functional calculus of `g_λ` at `T̂_c`:
`R_λ = (cfc g_λ T̂_c)|_{H'}`. Proved by Riesz
uniqueness — §3.3 says the cfc candidate solves the
same `J_λ` identity as FG-2c-1's representative. -/
theorem sliceResolvent_eq_cfcRestrict (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (lam : ℝ)
    (hlam : 0 < lam) :
    sliceYosidaR μG ρ hN2 hρcont hN β hpos lam hlam
      = sliceCfcRestrict μG ρ hN2 hρcont hN β hpos
          (sliceIdFun lam) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  calc ((sliceYosidaR μG ρ hN2 hρcont hN β hpos lam
          hlam) x).1
      = (sliceResolventRep μG ρ hN2 hρcont hN β
          hpos lam hlam x).val := by
        rw [sliceYosidaR_apply μG ρ hN2 hρcont hN β
            hpos lam hlam x,
          sliceResolventLin_apply μG ρ hN2 hρcont hN
            β hpos lam hlam x]
        exact sliceResolvent_coe μG ρ hN2 hρcont hN β
          hpos lam hlam x
    _ = (cfc (sliceIdFun lam)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          x.1 := by
        have hun := sliceResolventRep_unique μG ρ
          hN2 hρcont hN β hpos lam hlam
          (fun v => (sliceResolventRep_spec μG ρ hN2
            hρcont hN β hpos lam hlam x v).trans
            (sliceResolvent_cfc_spec μG ρ hN2 hρcont
              hN β hpos lam hlam x v).symm)
        exact congrArg
          (sliceFormDomainLam.val μG ρ hN2 hρcont hN
            β hpos lam hlam) hun
    _ = ((sliceCfcRestrict μG ρ hN2 hρcont hN β
          hpos (sliceIdFun lam)) x).1 :=
        (sliceCfcRestrict_apply_coe μG ρ hN2 hρcont
          hN β hpos (sliceIdFun lam) x).symm

/-! ## §4. Step B — the Yosida approximant is a cfc,
    and its exponential is the cfc of the exponential

`Ĥₙ = λₙ(1 − λₙ • R_{λₙ})` with `λₙ = n + 1`. By Step A,
`R_{λₙ}` is the restricted cfc of `g_{λₙ}`, so `Ĥₙ` is
the restricted cfc of the real symbol
`aₙ(μ) = λₙ(1 − λₙ g_{λₙ}(μ))`. For the finite cfc
algebra we also use a globally continuous
representative `ãₙ`, obtained by clamping the argument
to `[0, 1]`; it agrees with `aₙ` on `[0, 1]`, hence on
the spectrum. -/

/-- **The `n`-th Yosida symbol**:
`aₙ(μ) = λₙ(1 − λₙ g_{λₙ}(μ))`, `λₙ = n + 1`. -/
noncomputable def sliceYosidaSymbol (n : ℕ) : ℝ → ℝ :=
  fun μ => sliceYosidaWeight n
    * (1 - sliceYosidaWeight n
        * sliceIdFun (sliceYosidaWeight n) μ)

/-- **The clamped Yosida symbol** — globally
continuous, equal to `aₙ` on `[0, 1]`. -/
noncomputable def sliceYosidaSymbolClamp (n : ℕ) :
    ℝ → ℝ :=
  fun μ => sliceYosidaSymbol n (min (max μ 0) 1)

/-- The Yosida symbol is continuous on `[0, 1]`. -/
theorem sliceYosidaSymbol_continuousOn (n : ℕ) :
    ContinuousOn (sliceYosidaSymbol n)
      (Set.Icc (0 : ℝ) 1) :=
  continuousOn_const.mul
    (continuousOn_const.sub
      (continuousOn_const.mul
        (sliceIdFun_continuousOn
          (sliceYosidaWeight_pos n))))

/-- The clamped symbol is globally continuous. -/
theorem sliceYosidaSymbolClamp_continuous (n : ℕ) :
    Continuous (sliceYosidaSymbolClamp n) := by
  have hcomp : Continuous (sliceYosidaSymbol n
      ∘ fun μ => min (max μ 0) 1) :=
    (sliceYosidaSymbol_continuousOn n).comp_continuous
      ((continuous_id.max continuous_const).min
        continuous_const)
      (fun μ => ⟨le_min (le_max_right μ 0)
        zero_le_one, min_le_right _ _⟩)
  exact hcomp

/-- The clamped symbol agrees with the symbol on
`[0, 1]`. -/
theorem sliceYosidaSymbolClamp_eqOn (n : ℕ) :
    Set.EqOn (sliceYosidaSymbolClamp n)
      (sliceYosidaSymbol n) (Set.Icc (0 : ℝ) 1) := by
  intro μ hμ
  show sliceYosidaSymbol n (min (max μ 0) 1)
    = sliceYosidaSymbol n μ
  rw [max_eq_left hμ.1, min_eq_left hμ.2]

/-- The Yosida symbol is nonnegative on `[0, 1]`:
`λₙ g_{λₙ}(μ) ≤ 1` there. -/
theorem sliceYosidaSymbol_nonneg (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sliceYosidaSymbol n μ := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hg1 : sliceYosidaWeight n
      * sliceIdFun (sliceYosidaWeight n) μ ≤ 1 := by
    by_cases hμ0 : μ = 0
    · rw [hμ0, sliceIdFun_zero]
      simp [hW.ne']
    · have hlog : Real.log μ ≤ 0 :=
        Real.log_nonpos hμ.1 hμ.2
      have hge : sliceYosidaWeight n
          ≤ sliceYosidaWeight n - Real.log μ := by
        linarith
      have hpos' : 0 < sliceYosidaWeight n
          - Real.log μ := by linarith
      rw [sliceIdFun_of_ne_zero _ hμ0]
      have h := inv_anti₀ hW hge
      calc sliceYosidaWeight n
            * (sliceYosidaWeight n
              - Real.log μ)⁻¹
          ≤ sliceYosidaWeight n
            * (sliceYosidaWeight n)⁻¹ :=
          mul_le_mul_of_nonneg_left h hW.le
        _ = 1 := mul_inv_cancel₀ hW.ne'
  unfold sliceYosidaSymbol
  exact mul_nonneg hW.le (by linarith)

/-- The Yosida symbol is at most `λₙ` on `[0, 1]`. -/
theorem sliceYosidaSymbol_le (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    sliceYosidaSymbol n μ ≤ sliceYosidaWeight n := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hg : 0 ≤ sliceYosidaWeight n
      * sliceIdFun (sliceYosidaWeight n) μ :=
    mul_nonneg hW.le
      (sliceIdFun_nonneg hW hμ)
  unfold sliceYosidaSymbol
  have h := mul_le_mul_of_nonneg_left
    (show (1 : ℝ) - sliceYosidaWeight n
        * sliceIdFun (sliceYosidaWeight n) μ
      ≤ 1 by linarith) hW.le
  rwa [mul_one] at h

/-- The restriction of a cfc depends only on the
function's values on `[0, 1]`. -/
theorem sliceCfcRestrict_congr (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (fa fb : ℝ → ℝ)
    (h : Set.EqOn fa fb (Set.Icc (0 : ℝ) 1)) :
    sliceCfcRestrict μG ρ hN2 hρcont hN β hpos fa
      = sliceCfcRestrict μG ρ hN2 hρcont hN β hpos
        fb := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [sliceCfcRestrict_apply_coe μG ρ hN2 hρcont hN
      β hpos fa x,
    sliceCfcRestrict_apply_coe μG ρ hN2 hρcont hN β
      hpos fb x]
  exact DFunLike.congr_fun (cfc_congr (fun μ hμ => h
    (sliceTc_spectrum_subset μG ρ hN2 hρcont hN β
      hpos hμ))) x.1

/-- Product of cfcs, in pointwise-lambda form (the
Pi-form conversion of `cfc_mul`). -/
theorem sliceCfc_mul_lambda (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (fa fb : ℝ → ℝ)
    (hfa : ContinuousOn fa
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)))
    (hfb : ContinuousOn fb
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos))) :
    (cfc fa (sliceTc μG ρ hN2 hρcont hN β hpos))
        * (cfc fb (sliceTc μG ρ hN2 hρcont hN β
          hpos))
      = cfc (fun μ => fa μ * fb μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos) := by
  rw [← cfc_mul fa fb _ hfa hfb]

set_option maxHeartbeats 1600000 in
/-- **Step B, first half**: the Yosida approximant is
the restricted cfc of its symbol,
`Ĥₙ = (cfc aₙ T̂_c)|_{H'}` — Step A applied to
`R_{λₙ}`, plus the CLM algebra of
`λₙ • (1 − λₙ • ·)`. -/
theorem sliceYosidaApprox_eq_cfcRestrict (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n
      = sliceCfcRestrict μG ρ hN2 hρcont hN β hpos
          (sliceYosidaSymbol n) := by
  set W := sliceYosidaWeight n with hWdef
  have hW : 0 < W := sliceYosidaWeight_pos n
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hg : ContinuousOn (sliceIdFun W)
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceIdFun_continuousOn hW).mono hsub
  have hop : cfc (sliceYosidaSymbol n)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = (W : ℝ) • (1 - (W : ℝ)
          • cfc (sliceIdFun W)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) := by
    have e1 : sliceYosidaSymbol n
        = (fun μ => W * (1 - W
            * sliceIdFun W μ)) := rfl
    rw [e1, cfc_const_mul W
      (fun μ => 1 - W * sliceIdFun W μ)
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      (continuousOn_const.sub
        (continuousOn_const.mul hg)),
      cfc_sub (fun _ => (1 : ℝ))
        (fun μ => W * sliceIdFun W μ) _
        continuousOn_const
        (continuousOn_const.mul hg),
      sliceCfc_const μG ρ hN2 hρcont hN β hpos
        (1 : ℝ), map_one,
      cfc_const_mul W (sliceIdFun W)
        (sliceTc μG ρ hN2 hρcont hN β hpos) hg]
  have hR : ∀ u : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos),
      ((sliceYosidaR μG ρ hN2 hρcont hN β hpos W
        hW) u).1
        = (cfc (sliceIdFun W)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1 := by
    intro u
    rw [sliceResolvent_eq_cfcRestrict μG ρ hN2
      hρcont hN β hpos W hW]
    exact sliceCfcRestrict_apply_coe μG ρ hN2
      hρcont hN β hpos (sliceIdFun W) u
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  calc ((sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n) u).1
      = (W : ℂ) • (u.1 - (W : ℂ)
          • ((sliceYosidaR μG ρ hN2 hρcont hN β
              hpos W hW) u).1) := by
        rw [sliceYosidaApprox_apply μG ρ hN2 hρcont
            hN β hpos n u, Submodule.coe_smul,
          Submodule.coe_sub,
          sliceYosidaP_apply μG ρ hN2 hρcont hN β
            hpos n u, Submodule.coe_smul]
    _ = (W : ℂ) • (u.1 - (W : ℂ)
          • ((cfc (sliceIdFun W)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1)) := by
        rw [hR u]
    _ = ((sliceCfcRestrict μG ρ hN2 hρcont hN β
          hpos (sliceYosidaSymbol n)) u).1 := by
        rw [sliceCfcRestrict_apply_coe μG ρ hN2
            hρcont hN β hpos (sliceYosidaSymbol n) u,
          hop, smul_apply, sub_apply,
          ContinuousLinearMap.one_apply, smul_apply,
          RCLike.real_smul_eq_coe_smul (K := ℂ),
          RCLike.real_smul_eq_coe_smul (K := ℂ)]
        rfl

/-- The approximant is also the restricted cfc of
the clamped symbol. -/
theorem sliceYosidaApprox_eq_cfcRestrict_clamp
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    sliceYosidaApprox μG ρ hN2 hρcont hN β hpos n
      = sliceCfcRestrict μG ρ hN2 hρcont hN β hpos
          (sliceYosidaSymbolClamp n) :=
  (sliceYosidaApprox_eq_cfcRestrict μG ρ hN2 hρcont
    hN β hpos n).trans
    (sliceCfcRestrict_congr μG ρ hN2 hρcont hN β
      hpos (sliceYosidaSymbolClamp n)
      (sliceYosidaSymbol n)
      (sliceYosidaSymbolClamp_eqOn n)).symm

/-- **Powers of the approximant, coerced**: the
`k`-th power acts on ambient vectors as the cfc of
the `k`-th power of the clamped symbol. -/
theorem sliceYosidaApprox_pow_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (k : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
        n ^ k) u).1
      = (cfc (fun μ => (sliceYosidaSymbolClamp n
            μ) ^ k)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1 := by
  have hstep : ∀ z : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos),
      ((sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
        n) z).1
        = (cfc (sliceYosidaSymbolClamp n)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            z.1 := by
    intro z
    rw [sliceYosidaApprox_eq_cfcRestrict_clamp μG ρ
      hN2 hρcont hN β hpos n]
    exact sliceCfcRestrict_apply_coe μG ρ hN2
      hρcont hN β hpos (sliceYosidaSymbolClamp n) z
  induction k generalizing u with
  | zero =>
    rw [pow_zero, ContinuousLinearMap.one_apply,
      show (fun μ => (sliceYosidaSymbolClamp n μ)
          ^ 0) = (fun _ => (1 : ℝ)) from
        funext fun μ => pow_zero _,
      sliceCfc_const μG ρ hN2 hρcont hN β hpos
        (1 : ℝ), map_one,
      ContinuousLinearMap.one_apply]
  | succ k ih =>
    have hsub : spectrum ℝ
        (sliceTc μG ρ hN2 hρcont hN β hpos)
        ⊆ Set.Icc 0 1 :=
      sliceTc_spectrum_subset μG ρ hN2 hρcont hN β
        hpos
    have hã : ContinuousOn (sliceYosidaSymbolClamp n)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      (sliceYosidaSymbolClamp_continuous
        n).continuousOn.mono hsub
    have hãk : ContinuousOn
        (fun μ => (sliceYosidaSymbolClamp n μ) ^ k)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      ((sliceYosidaSymbolClamp_continuous n).pow
        k).continuousOn.mono hsub
    calc ((sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n ^ (k + 1)) u).1
        = ((sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) ((sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n ^ k) u)).1 := by
          rw [pow_succ',
            ContinuousLinearMap.mul_apply]
      _ = (cfc (fun μ => (sliceYosidaSymbolClamp n
              μ) ^ (k + 1))
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1 := by
          rw [hstep ((sliceYosidaApprox μG ρ hN2
              hρcont hN β hpos n ^ k) u), ih u,
            ← ContinuousLinearMap.mul_apply,
            sliceCfc_mul_lambda μG ρ hN2 hρcont hN
              β hpos (sliceYosidaSymbolClamp n)
              (fun μ => (sliceYosidaSymbolClamp n
                μ) ^ k) hã hãk]
          congr 1
          congr 1
          funext μ
          exact (pow_succ' _ _).symm

/-- The real exponential series, in the `•`-normal
form of `NormedSpace.exp_series_hasSum_exp'`
transported across `Real.exp_eq_exp_ℝ`. -/
theorem sliceReal_hasSum_exp (s : ℝ) :
    HasSum (fun k => ((k ! : ℝ)⁻¹) • (s ^ k))
      (Real.exp s) := by
  have h : HasSum (fun n => ((n ! : ℝ)⁻¹) • (s ^ n))
      (NormedSpace.exp s) :=
    NormedSpace.exp_series_hasSum_exp' s
  rwa [← Real.exp_eq_exp_ℝ] at h

/-- Partial sums of the real exponential series
converge. -/
theorem sliceReal_exp_partial_tendsto (s : ℝ) :
    Filter.Tendsto (fun K => ∑ k ∈ Finset.range K,
        ((k ! : ℝ)⁻¹) • (s ^ k)) Filter.atTop
      (nhds (Real.exp s)) :=
  (sliceReal_hasSum_exp s).tendsto_sum_nat

/-- **Step B, ambient half**: the cfc partial sums of
`exp(−ãₙ)` converge in operator norm to
`cfc (exp(−ãₙ)) T̂_c`, by the Weierstrass tail bound
`exp(λₙ) − ∑_{k<K} λₙ^k/k!` (the symbol lies in
`[0, λₙ]` on the spectrum). -/
theorem sliceCfc_exp_partial_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    Filter.Tendsto (fun K => ∑ k ∈ Finset.range K,
        cfc (fun μ => ((k ! : ℝ)⁻¹)
          * (-(sliceYosidaSymbolClamp n μ)) ^ k)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
      Filter.atTop
      (nhds (cfc (fun μ => Real.exp
          (-(sliceYosidaSymbolClamp n μ)))
        (sliceTc μG ρ hN2 hρcont hN β hpos))) := by
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hsummW : Summable (fun k => ((k ! : ℝ)⁻¹)
      • (sliceYosidaWeight n ^ k)) :=
    (sliceReal_hasSum_exp _).summable
  have htsumW : ∑' k, ((k ! : ℝ)⁻¹)
      • (sliceYosidaWeight n ^ k)
      = Real.exp (sliceYosidaWeight n) :=
    (sliceReal_hasSum_exp _).tsum_eq
  have hãspec : ContinuousOn (sliceYosidaSymbolClamp
      n) (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceYosidaSymbolClamp_continuous
      n).continuousOn.mono hsub
  have hexpOn : ContinuousOn (fun μ => Real.exp
        (-(sliceYosidaSymbolClamp n μ)))
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    Real.continuous_exp.comp_continuousOn
      hãspec.neg
  have hbound : ∀ K, ‖cfc ((fun μ => Real.exp
          (-(sliceYosidaSymbolClamp n μ)))
        - (fun μ => ∑ k ∈ Finset.range K,
            ((k ! : ℝ)⁻¹)
            * (-(sliceYosidaSymbolClamp n μ)) ^ k))
        (sliceTc μG ρ hN2 hρcont hN β hpos)‖
      ≤ Real.exp (sliceYosidaWeight n)
        - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
            • (sliceYosidaWeight n ^ k) := by
    intro K
    have htail0 : 0 ≤ Real.exp (sliceYosidaWeight n)
        - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
            • (sliceYosidaWeight n ^ k) := by
      have hle := Summable.sum_le_tsum
        (Finset.range K)
        (fun i _ => smul_nonneg
          (inv_nonneg.mpr (Nat.cast_nonneg _))
          (pow_nonneg hW.le _)) hsummW
      rw [htsumW] at hle
      linarith
    refine norm_cfc_le htail0 (fun μ hμ => ?_)
    have hμI : μ ∈ Set.Icc (0 : ℝ) 1 := hsub hμ
    have hã : sliceYosidaSymbolClamp n μ
        = sliceYosidaSymbol n μ :=
      sliceYosidaSymbolClamp_eqOn n hμI
    have hã0 : 0 ≤ sliceYosidaSymbolClamp n μ :=
      hã ▸ sliceYosidaSymbol_nonneg n hμI
    have hãW : sliceYosidaSymbolClamp n μ
        ≤ sliceYosidaWeight n :=
      hã ▸ sliceYosidaSymbol_le n hμI
    have hsumm : Summable (fun k => ((k ! : ℝ)⁻¹)
        • ((-(sliceYosidaSymbolClamp n μ)) ^ k)) :=
      (sliceReal_hasSum_exp _).summable
    have key : (∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ)) ^ k))
        + ∑' i, ((↑(i + K) ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ))
            ^ (i + K))
        = Real.exp (-(sliceYosidaSymbolClamp n
            μ)) :=
      (Summable.sum_add_tsum_nat_add K
        hsumm).trans (sliceReal_hasSum_exp _).tsum_eq
    have keyW : (∑ k ∈ Finset.range K,
          ((k ! : ℝ)⁻¹)
          • (sliceYosidaWeight n ^ k))
        + ∑' i, ((↑(i + K) ! : ℝ)⁻¹)
          • (sliceYosidaWeight n ^ (i + K))
        = Real.exp (sliceYosidaWeight n) :=
      (Summable.sum_add_tsum_nat_add K
        hsummW).trans htsumW
    have hsummsh : Summable (fun i =>
        ((↑(i + K) ! : ℝ)⁻¹)
          • (sliceYosidaWeight n ^ (i + K))) :=
      (summable_nat_add_iff K).mpr hsummW
    have hnormbound : ∀ j, ‖((j ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ)) ^ j)‖
        ≤ ((j ! : ℝ)⁻¹)
          • (sliceYosidaWeight n ^ j) := by
      intro j
      have h1 : ‖((j ! : ℝ)⁻¹)
            • ((-(sliceYosidaSymbolClamp n μ))
              ^ j)‖
          = ((j ! : ℝ)⁻¹)
            * ‖(-(sliceYosidaSymbolClamp n μ))
              ^ j‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr
            (Nat.cast_nonneg _))]
      rw [h1, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_
        (inv_nonneg.mpr (Nat.cast_nonneg _))
      rw [norm_pow, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg hã0]
      exact pow_le_pow_left₀ hã0 hãW j
    have hsummn : Summable (fun i =>
        ‖((↑(i + K) ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ))
            ^ (i + K))‖) := by
      refine Summable.of_norm_bounded hsummsh
        (fun i => ?_)
      rw [Real.norm_eq_abs, abs_norm]
      exact hnormbound (i + K)
    have hnormle : ‖∑' i, ((↑(i + K) ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ))
            ^ (i + K))‖
        ≤ Real.exp (sliceYosidaWeight n)
          - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
              • (sliceYosidaWeight n ^ k) := by
      refine le_trans (norm_tsum_le_tsum_norm
        hsummn) ?_
      have hle2 := Summable.tsum_le_tsum
        (fun i => hnormbound (i + K)) hsummn
        hsummsh
      linarith
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have hsumform : (∑ k ∈ Finset.range K,
          ((k ! : ℝ)⁻¹)
          * (-(sliceYosidaSymbolClamp n μ)) ^ k)
        = ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ)) ^ k) :=
      Finset.sum_congr rfl (fun k _ => (smul_eq_mul
        _ _).symm)
    rw [hsumform]
    have hdiff : Real.exp
          (-(sliceYosidaSymbolClamp n μ))
        - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ)) ^ k)
        = ∑' i, ((↑(i + K) ! : ℝ)⁻¹)
          • ((-(sliceYosidaSymbolClamp n μ))
            ^ (i + K)) := by linarith
    rw [hdiff, ← Real.norm_eq_abs]
    exact hnormle
  have hD : Filter.Tendsto
      (fun K => cfc ((fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          - (fun μ => ∑ k ∈ Finset.range K,
              ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ)) ^ k))
          (sliceTc μG ρ hN2 hρcont hN β hpos))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have htail : Filter.Tendsto
        (fun K => Real.exp (sliceYosidaWeight n)
          - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
              • (sliceYosidaWeight n ^ k))
        Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto
          (fun K => Real.exp (sliceYosidaWeight n)
            - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
                • (sliceYosidaWeight n ^ k))
          Filter.atTop
          (nhds (Real.exp (sliceYosidaWeight n)
            - Real.exp (sliceYosidaWeight n))) :=
        tendsto_const_nhds.sub
          (sliceReal_exp_partial_tendsto
            (sliceYosidaWeight n))
      simpa using h
    exact squeeze_zero (fun K => norm_nonneg _)
      hbound htail
  have hkey : ∀ K, cfc ((fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          - (fun μ => ∑ k ∈ Finset.range K,
              ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ)) ^ k))
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)
        - ∑ k ∈ Finset.range K,
            cfc (fun μ => ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ)) ^ k)
              (sliceTc μG ρ hN2 hρcont hN β
                hpos) := by
    intro K
    have hfun : ((fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          - (fun μ => ∑ k ∈ Finset.range K,
              ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ)) ^ k))
        = (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ))
          - ∑ k ∈ Finset.range K, ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ))
                ^ k) :=
      funext fun μ => Pi.sub_apply _ _ _
    have hsumOn : ContinuousOn
        (fun μ => ∑ k ∈ Finset.range K,
          ((k ! : ℝ)⁻¹)
          * (-(sliceYosidaSymbolClamp n μ)) ^ k)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      (continuous_finsetSum (Finset.range K)
        (fun k _ => continuous_const.mul
          ((sliceYosidaSymbolClamp_continuous
            n).neg.pow k))).continuousOn.mono hsub
    rw [hfun, cfc_sub _ _ _ hexpOn hsumOn,
      sliceCfc_sum μG ρ hN2 hρcont hN β hpos
        (Finset.range K)
        (fun k μ => ((k ! : ℝ)⁻¹)
          * (-(sliceYosidaSymbolClamp n μ)) ^ k)
        (fun k _ => continuous_const.mul
          ((sliceYosidaSymbolClamp_continuous
            n).neg.pow k))]
  have hlim0 : Filter.Tendsto
      (fun K => cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)
        - ∑ k ∈ Finset.range K,
            cfc (fun μ => ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ)) ^ k)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr hkey hD
  have hlim : Filter.Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        cfc (fun μ => ((k ! : ℝ)⁻¹)
          * (-(sliceYosidaSymbolClamp n μ)) ^ k)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
      Filter.atTop
      (nhds (cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)
        - 0)) := by
    have h : Filter.Tendsto
        (fun K => cfc (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
          - (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos)
            - ∑ k ∈ Finset.range K,
                cfc (fun μ => ((k ! : ℝ)⁻¹)
                  * (-(sliceYosidaSymbolClamp n
                    μ)) ^ k)
                  (sliceTc μG ρ hN2 hρcont hN β
                    hpos)))
        Filter.atTop
        (nhds (cfc (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
          - 0)) :=
      tendsto_const_nhds.sub hlim0
    exact h.congr (fun K => by abel)
  simpa using hlim

/-- The approximant's action on ambient vectors is
the clamped symbol's cfc. -/
theorem sliceYosidaApprox_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (z : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceYosidaApprox μG ρ hN2 hρcont hN β hpos
      n) z).1
      = (cfc (sliceYosidaSymbolClamp n)
          (sliceTc μG ρ hN2 hρcont hN β hpos)) z.1 := by
  rw [sliceYosidaApprox_eq_cfcRestrict_clamp μG ρ
    hN2 hρcont hN β hpos n]
  exact sliceCfcRestrict_apply_coe μG ρ hN2 hρcont
    hN β hpos (sliceYosidaSymbolClamp n) z

set_option maxHeartbeats 1600000 in
/-- **Powers of the negated approximant, coerced**:
`((−1) • Ĥₙ)^k` acts on ambient vectors as the cfc
of `μ ↦ (−ãₙ(μ))^k`. -/
theorem sliceYosidaNeg_pow_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (k : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((((-1 : ℂ) • sliceYosidaApprox μG ρ hN2
        hρcont hN β hpos n) ^ k) u).1
      = (cfc (fun μ => (-(sliceYosidaSymbolClamp n
            μ)) ^ k)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1 := by
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hã : ContinuousOn (sliceYosidaSymbolClamp n)
      (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
        hpos)) :=
    (sliceYosidaSymbolClamp_continuous
      n).continuousOn.mono hsub
  have hstep : ∀ z : ↥(sliceFormClosure μG ρ hN2
        hρcont hN β hpos),
      ((((-1 : ℂ)) • sliceYosidaApprox μG ρ hN2
          hρcont hN β hpos n) z).1
        = (cfc (fun μ => -(sliceYosidaSymbolClamp n
              μ))
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            z.1 := by
    intro z
    have e1 : cfc (fun μ => -(sliceYosidaSymbolClamp
          n μ)) (sliceTc μG ρ hN2 hρcont hN β hpos)
        = ((-1 : ℝ)) • cfc (sliceYosidaSymbolClamp
            n) (sliceTc μG ρ hN2 hρcont hN β
              hpos) := by
      have hfun : (fun μ => -(sliceYosidaSymbolClamp
            n μ))
          = (fun μ => (-1 : ℝ)
              * sliceYosidaSymbolClamp n μ) :=
        funext fun μ => (neg_one_mul _).symm
      rw [hfun]
      exact cfc_const_mul (-1) (sliceYosidaSymbolClamp
        n) (sliceTc μG ρ hN2 hρcont hN β hpos) hã
    rw [smul_apply, Submodule.coe_smul,
      sliceYosidaApprox_coe μG ρ hN2 hρcont hN β
        hpos n z, e1, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    rfl
  induction k generalizing u with
  | zero =>
    rw [pow_zero, ContinuousLinearMap.one_apply,
      show (fun μ => (-(sliceYosidaSymbolClamp n
          μ)) ^ 0) = (fun _ => (1 : ℝ)) from
        funext fun μ => pow_zero _,
      sliceCfc_const μG ρ hN2 hρcont hN β hpos
        (1 : ℝ), map_one,
      ContinuousLinearMap.one_apply]
  | succ k ih =>
    have hãk : ContinuousOn
        (fun μ => (-(sliceYosidaSymbolClamp n μ))
          ^ k)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      ((sliceYosidaSymbolClamp_continuous n).neg.pow
        k).continuousOn.mono hsub
    calc ((((-1 : ℂ) • sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n) ^ (k + 1)) u).1
        = (cfc (fun μ => -(sliceYosidaSymbolClamp n
              μ))
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            ((((-1 : ℂ) • sliceYosidaApprox μG ρ
              hN2 hρcont hN β hpos n) ^ k) u).1 := by
          rw [pow_succ',
            ContinuousLinearMap.mul_apply, hstep]
      _ = (cfc (fun μ => (-(sliceYosidaSymbolClamp
              n μ)) ^ (k + 1))
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1 := by
          rw [ih u, ← ContinuousLinearMap.mul_apply,
            sliceCfc_mul_lambda μG ρ hN2 hρcont hN β
              hpos
              (fun μ => -(sliceYosidaSymbolClamp n
                μ))
              (fun μ => (-(sliceYosidaSymbolClamp n
                μ)) ^ k) hã.neg hãk]
          congr 1
          congr 1
          funext μ
          exact (pow_succ' _ _).symm

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CompleteSpace E]

/-- The exponential series at the CLM seat, routed
through FG-2c-3's `yosidaExpOf` (the §0-generic
helper does not unify with the CLM multiplication
instance at a concrete seat — an instance diamond,
see `LatticeSliceYosida` §0/§0b — so, following
FG-2c-3's own pattern, the seat gets its own
`E`-abstract statement). -/
theorem sliceExp_hasSum_clm (x : E →L[ℂ] E) :
    HasSum (fun k => ((k ! : ℂ)⁻¹) • (x ^ k))
      (yosidaExpOf x) :=
  NormedSpace.exp_series_hasSum_exp' x

/-- Operator-norm convergence transport at the CLM
seat, `E`-abstract (at a concrete seat the generic
`Tendsto.norm` / `tendsto_zero_iff_norm_tendsto_zero`
paths do not unify with the seat's op-norm instance
— the same instance diamond as for `exp`). -/
theorem sliceTendsto_norm_sub_zero
    (S : ℕ → (E →L[ℂ] E)) (e : E →L[ℂ] E)
    (h : Filter.Tendsto S Filter.atTop (nhds e)) :
    Filter.Tendsto (fun K => ‖S K - e‖)
      Filter.atTop (nhds 0) := by
  have hsub : Filter.Tendsto (fun K => S K - e)
      Filter.atTop (nhds 0) := by
    have htmp := h.sub (tendsto_const_nhds (x := e))
    simpa using htmp
  exact tendsto_zero_iff_norm_tendsto_zero.mp hsub

set_option maxHeartbeats 1600000 in
/-- **Step B (the exponential identity)**: for every
`u ∈ H'`, the Yosida exponential at `t = 1` acts on
ambient vectors as the cfc of `exp(−ãₙ)`:
`(exp(−Ĥₙ) u).1 = (cfc (exp(−ãₙ)) T̂_c) u.1`. Both
sides are limits of the same partial sums — §4's
operator-norm convergence on the cfc side,
`exp_series_hasSum_exp'` on the `H'` side, and the
term-by-term identification of
`sliceYosidaNeg_pow_coe`. -/
theorem sliceYosidaExp_one_coe (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    ((sliceYosidaExp μG ρ hN2 hρcont hN β hpos 1
      n) u).1
      = (cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1 := by
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hcast1 : (((-1 : ℝ)) : ℂ) = (-1 : ℂ) := by
    norm_num [Complex.ext_iff]
  have hExp : sliceYosidaExp μG ρ hN2 hρcont hN β
        hpos 1 n
      = yosidaExpOf (((-1 : ℂ))
          • sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) := by
    rw [sliceYosidaExp_eq μG ρ hN2 hρcont hN β hpos
      1 n, hcast1]
  haveI : CompleteSpace ↥(sliceFormClosure μG ρ
      hN2 hρcont hN β hpos) :=
    sliceFormClosure_completeSpace μG ρ hN2 hρcont
      hN β hpos
  have hsumB : HasSum (fun k => ((k ! : ℂ)⁻¹)
        • (((-1 : ℂ)) • sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n) ^ k)
      (yosidaExpOf (((-1 : ℂ))
        • sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n)) :=
    sliceExp_hasSum_clm _
  have hpart : Filter.Tendsto
      (fun K => ∑ k ∈ Finset.range K, ((k ! : ℂ)⁻¹)
        • (((-1 : ℂ)) • sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n) ^ k)
      Filter.atTop
      (nhds (yosidaExpOf (((-1 : ℂ))
        • sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n))) :=
    hsumB.tendsto_sum_nat
  have hterm : ∀ k, ((((k ! : ℂ)⁻¹)
        • (((-1 : ℂ)) • sliceYosidaApprox μG ρ hN2
            hρcont hN β hpos n) ^ k) u).1
      = (cfc (fun μ => ((k ! : ℝ)⁻¹)
            * (-(sliceYosidaSymbolClamp n μ)) ^ k)
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1 := by
    intro k
    have hãk : ContinuousOn
        (fun μ => (-(sliceYosidaSymbolClamp n μ))
          ^ k)
        (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
          hpos)) :=
      ((sliceYosidaSymbolClamp_continuous n).neg.pow
        k).continuousOn.mono hsub
    calc ((((k ! : ℂ)⁻¹)
          • (((-1 : ℂ)) • sliceYosidaApprox μG ρ
              hN2 hρcont hN β hpos n) ^ k) u).1
        = ((k ! : ℂ)⁻¹)
            • (cfc (fun μ =>
                (-(sliceYosidaSymbolClamp n μ)) ^ k)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1 := by
          rw [smul_apply, Submodule.coe_smul,
            sliceYosidaNeg_pow_coe μG ρ hN2 hρcont
              hN β hpos n k u]
      _ = (cfc (fun μ => ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ))
                ^ k)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1 := by
          rw [cfc_const_mul ((k ! : ℝ)⁻¹)
            (fun μ => (-(sliceYosidaSymbolClamp n
              μ)) ^ k)
            (sliceTc μG ρ hN2 hρcont hN β hpos) hãk,
            smul_apply,
            RCLike.real_smul_eq_coe_smul (K := ℂ),
            RCLike.ofReal_inv, RCLike.ofReal_natCast]
  have hEqK : ∀ K, ((∑ k ∈ Finset.range K,
        ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
          • sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n) ^ k) u).1
      = ((∑ k ∈ Finset.range K,
          cfc (fun μ => ((k ! : ℝ)⁻¹)
            * (-(sliceYosidaSymbolClamp n μ)) ^ k)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1) := by
    intro K
    calc ((∑ k ∈ Finset.range K, ((k ! : ℂ)⁻¹)
          • (((-1 : ℂ)) • sliceYosidaApprox μG ρ
              hN2 hρcont hN β hpos n) ^ k) u).1
        = ∑ k ∈ Finset.range K,
            ((((k ! : ℂ)⁻¹) • (((-1 : ℂ))
              • sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n) ^ k) u).1 := by
          rw [_root_.sum_apply]
          exact Submodule.coe_sum
            (p := sliceFormClosure μG ρ hN2 hρcont
              hN β hpos)
            (fun k => (((k ! : ℂ)⁻¹) • (((-1 : ℂ))
              • sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n) ^ k) u)
            (Finset.range K)
      _ = ∑ k ∈ Finset.range K,
            (cfc (fun μ => ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ))
                ^ k)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1 :=
          Finset.sum_congr rfl (fun k _ => hterm k)
      _ = ((∑ k ∈ Finset.range K,
            cfc (fun μ => ((k ! : ℝ)⁻¹)
              * (-(sliceYosidaSymbolClamp n μ))
                ^ k)
              (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1) := by
          rw [_root_.sum_apply]
  have hH : Filter.Tendsto
      (fun K => ((∑ k ∈ Finset.range K,
          ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
            • sliceYosidaApprox μG ρ hN2 hρcont hN
              β hpos n) ^ k) u).1)
      Filter.atTop
      (nhds ((yosidaExpOf (((-1 : ℂ))
          • sliceYosidaApprox μG ρ hN2 hρcont hN β
            hpos n)) u).1) := by
    have hdiff : Filter.Tendsto
        (fun K => ‖((∑ k ∈ Finset.range K,
              ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n) ^ k) u).1
            - ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1‖)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero
        (g := fun K => ‖(∑ k ∈ Finset.range K,
              ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n) ^ k)
            - yosidaExpOf (((-1 : ℂ))
              • sliceYosidaApprox μG ρ hN2 hρcont
                hN β hpos n)‖ * ‖u‖)
        (fun K => norm_nonneg _) (fun K => ?_) ?_
      · have h1 : ((∑ k ∈ Finset.range K,
              ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n) ^ k) u).1
            - ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1
          = (((∑ k ∈ Finset.range K, ((k ! : ℂ)⁻¹)
                • (((-1 : ℂ)) • sliceYosidaApprox
                  μG ρ hN2 hρcont hN β hpos n) ^ k)
              - yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1 := by
          rw [ContinuousLinearMap.sub_apply,
            Submodule.coe_sub]
        rw [h1, Submodule.norm_coe]
        exact ContinuousLinearMap.le_opNorm _ _
      · have h2 : Filter.Tendsto
            (fun K => ‖(∑ k ∈ Finset.range K,
                ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                  • sliceYosidaApprox μG ρ hN2
                    hρcont hN β hpos n) ^ k)
              - yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)‖ * ‖u‖)
            Filter.atTop (nhds 0) := by
          have h4 : Filter.Tendsto
              (fun K => ‖(∑ k ∈ Finset.range K,
                  ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                    • sliceYosidaApprox μG ρ hN2
                      hρcont hN β hpos n) ^ k)
                - yosidaExpOf (((-1 : ℂ))
                  • sliceYosidaApprox μG ρ hN2
                    hρcont hN β hpos n)‖)
              Filter.atTop (nhds 0) :=
            sliceTendsto_norm_sub_zero _ _ hpart
          have h5 : Filter.Tendsto
              (fun K => ‖(∑ k ∈ Finset.range K,
                  ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                    • sliceYosidaApprox μG ρ hN2
                      hρcont hN β hpos n) ^ k)
                - yosidaExpOf (((-1 : ℂ))
                  • sliceYosidaApprox μG ρ hN2
                    hρcont hN β hpos n)‖ * ‖u‖)
              Filter.atTop (nhds (0 * ‖u‖)) :=
            h4.mul (tendsto_const_nhds (x := ‖u‖))
          simpa using h5
        exact h2
    have h6 : Filter.Tendsto
        (fun K => ((∑ k ∈ Finset.range K,
              ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n) ^ k) u).1
            - ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1)
        Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
    have h7 := h6.add (tendsto_const_nhds (x :=
      ((yosidaExpOf (((-1 : ℂ))
        • sliceYosidaApprox μG ρ hN2 hρcont hN β
          hpos n)) u).1))
    have h8 : Filter.Tendsto
        (fun K => ((∑ k ∈ Finset.range K,
              ((k ! : ℂ)⁻¹) • (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n) ^ k) u).1
            - ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1
          + ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1)
        Filter.atTop
        (nhds (0 + ((yosidaExpOf (((-1 : ℂ))
                • sliceYosidaApprox μG ρ hN2 hρcont
                  hN β hpos n)) u).1)) :=
      h7
    have h9 := h8.congr (fun K => sub_add_cancel _ _)
    simpa using h9
  have hA : Filter.Tendsto
      (fun K => (∑ k ∈ Finset.range K,
          cfc (fun μ => ((k ! : ℝ)⁻¹)
            * (-(sliceYosidaSymbolClamp n μ)) ^ k)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1)
      Filter.atTop
      (nhds ((cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos))
          u.1)) := by
    have hdiff : Filter.Tendsto
        (fun K => ‖(∑ k ∈ Finset.range K,
              cfc (fun μ => ((k ! : ℝ)⁻¹)
                * (-(sliceYosidaSymbolClamp n μ))
                  ^ k)
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)) u.1
            - (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1‖)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero
        (g := fun K => ‖(∑ k ∈ Finset.range K,
              cfc (fun μ => ((k ! : ℝ)⁻¹)
                * (-(sliceYosidaSymbolClamp n μ))
                  ^ k)
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos))
            - cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β
                hpos)‖ * ‖u.1‖)
        (fun K => norm_nonneg _) (fun K => ?_) ?_
      · have h1 : (∑ k ∈ Finset.range K,
              cfc (fun μ => ((k ! : ℝ)⁻¹)
                * (-(sliceYosidaSymbolClamp n μ))
                  ^ k)
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)) u.1
            - (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1
          = ((∑ k ∈ Finset.range K,
                cfc (fun μ => ((k ! : ℝ)⁻¹)
                  * (-(sliceYosidaSymbolClamp n
                    μ)) ^ k)
                  (sliceTc μG ρ hN2 hρcont hN β
                    hpos))
              - cfc (fun μ => Real.exp
                  (-(sliceYosidaSymbolClamp n μ)))
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)) u.1 := by
          rw [ContinuousLinearMap.sub_apply]
        rw [h1]
        exact ContinuousLinearMap.le_opNorm _ _
      · have h2 : Filter.Tendsto
            (fun K => ‖(∑ k ∈ Finset.range K,
                cfc (fun μ => ((k ! : ℝ)⁻¹)
                  * (-(sliceYosidaSymbolClamp n
                    μ)) ^ k)
                  (sliceTc μG ρ hN2 hρcont hN β
                    hpos))
              - cfc (fun μ => Real.exp
                  (-(sliceYosidaSymbolClamp n
                    μ)))
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)‖ * ‖u.1‖)
            Filter.atTop (nhds 0) := by
          have h4 : Filter.Tendsto
              (fun K => ‖(∑ k ∈ Finset.range K,
                  cfc (fun μ => ((k ! : ℝ)⁻¹)
                    * (-(sliceYosidaSymbolClamp n
                      μ)) ^ k)
                    (sliceTc μG ρ hN2 hρcont hN β
                      hpos))
                - cfc (fun μ => Real.exp
                    (-(sliceYosidaSymbolClamp n
                      μ)))
                  (sliceTc μG ρ hN2 hρcont hN β
                    hpos)‖)
              Filter.atTop (nhds 0) :=
            sliceTendsto_norm_sub_zero _ _
              (sliceCfc_exp_partial_tendsto μG ρ
                hN2 hρcont hN β hpos n)
          have h5 : Filter.Tendsto
              (fun K => ‖(∑ k ∈ Finset.range K,
                  cfc (fun μ => ((k ! : ℝ)⁻¹)
                    * (-(sliceYosidaSymbolClamp n
                      μ)) ^ k)
                    (sliceTc μG ρ hN2 hρcont hN β
                      hpos))
                - cfc (fun μ => Real.exp
                    (-(sliceYosidaSymbolClamp n
                      μ)))
                  (sliceTc μG ρ hN2 hρcont hN β
                    hpos)‖ * ‖u.1‖)
              Filter.atTop (nhds (0 * ‖u.1‖)) :=
            h4.mul (tendsto_const_nhds (x := ‖u.1‖))
          simpa using h5
        exact h2
    have h6 : Filter.Tendsto
        (fun K => (∑ k ∈ Finset.range K,
              cfc (fun μ => ((k ! : ℝ)⁻¹)
                * (-(sliceYosidaSymbolClamp n μ))
                  ^ k)
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)) u.1
            - (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1)
        Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
    have h7 := h6.add (tendsto_const_nhds (x :=
      (cfc (fun μ => Real.exp
          (-(sliceYosidaSymbolClamp n μ)))
        (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1))
    have h8 : Filter.Tendsto
        (fun K => (∑ k ∈ Finset.range K,
              cfc (fun μ => ((k ! : ℝ)⁻¹)
                * (-(sliceYosidaSymbolClamp n μ))
                  ^ k)
                (sliceTc μG ρ hN2 hρcont hN β
                  hpos)) u.1
            - (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1
          + (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1)
        Filter.atTop
        (nhds (0 + (cfc (fun μ => Real.exp
                (-(sliceYosidaSymbolClamp n μ)))
              (sliceTc μG ρ hN2 hρcont hN β hpos))
              u.1)) :=
      h7
    have h9 := h8.congr (fun K => sub_add_cancel _ _)
    simpa using h9
  have hfin := tendsto_nhds_unique
    (Filter.Tendsto.congr hEqK hH) hA
  rwa [← hExp] at hfin

/-- **The clamped symbol in closed form** on
`(0, 1]`: `ãₙ(μ) = λₙ(−log μ)/(λₙ + (−log μ))`. -/
theorem sliceYosidaClamp_eq (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    sliceYosidaSymbolClamp n μ
      = sliceYosidaWeight n * (-Real.log μ)
        / (sliceYosidaWeight n + (-Real.log μ)) := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hL : 0 ≤ -Real.log μ :=
    neg_nonneg.mpr (Real.log_nonpos hμ.1 hμ.2)
  have hpos : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ) := by linarith
  rw [sliceYosidaSymbolClamp_eqOn n hμ]
  show sliceYosidaWeight n * (1 - sliceYosidaWeight n
      * sliceIdFun (sliceYosidaWeight n) μ) = _
  rw [sliceIdFun_of_ne_zero _ hμ0]
  have hsub : sliceYosidaWeight n - Real.log μ
      = sliceYosidaWeight n + (-Real.log μ) := by
    ring
  rw [hsub]
  field_simp
  ring

/-- The clamped symbol at `0` is the weight. -/
theorem sliceYosidaClamp_zero (n : ℕ) :
    sliceYosidaSymbolClamp n 0
      = sliceYosidaWeight n := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_refl 0, zero_le_one⟩
  rw [sliceYosidaSymbolClamp_eqOn n h0]
  show sliceYosidaWeight n * (1 - sliceYosidaWeight n
      * sliceIdFun (sliceYosidaWeight n) 0) = _
  rw [sliceIdFun_zero]
  simp

/-- The clamped symbol is nonnegative on `[0, 1]`. -/
theorem sliceYosidaClamp_nonneg (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sliceYosidaSymbolClamp n μ := by
  rw [sliceYosidaSymbolClamp_eqOn n hμ]
  exact sliceYosidaSymbol_nonneg n hμ

/-- The clamped symbol is at most `−log μ` on
`(0, 1]`: `λL/(λ + L) ≤ L`. -/
theorem sliceYosidaClamp_le_log (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    sliceYosidaSymbolClamp n μ ≤ -Real.log μ := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hL : 0 ≤ -Real.log μ :=
    neg_nonneg.mpr (Real.log_nonpos hμ.1 hμ.2)
  have hpos : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ) := by linarith
  rw [sliceYosidaClamp_eq n hμ hμ0, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (-Real.log μ)]

/-- The gap `−log μ − ãₙ(μ)` in closed form:
`(−log μ)²/(λₙ + (−log μ))`. -/
theorem sliceYosidaClamp_gap (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    (-Real.log μ) - sliceYosidaSymbolClamp n μ
      = (-Real.log μ) ^ 2
        / (sliceYosidaWeight n + (-Real.log μ)) := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hL : 0 ≤ -Real.log μ :=
    neg_nonneg.mpr (Real.log_nonpos hμ.1 hμ.2)
  have hpos : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ) := by linarith
  rw [sliceYosidaClamp_eq n hμ hμ0]
  field_simp
  ring

/-- The clamped symbol in difference form:
`ãₙ(μ) = λₙ − λₙ²/(λₙ + (−log μ))` on `(0, 1]`. -/
theorem sliceYosidaClamp_eq_sub (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : μ ≠ 0) :
    sliceYosidaSymbolClamp n μ
      = sliceYosidaWeight n
        - (sliceYosidaWeight n) ^ 2
          / (sliceYosidaWeight n + (-Real.log μ)) := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hL : 0 ≤ -Real.log μ :=
    neg_nonneg.mpr (Real.log_nonpos hμ.1 hμ.2)
  have hpos : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ) := by linarith
  rw [sliceYosidaClamp_eq n hμ hμ0]
  field_simp
  ring

/-- The clamped symbol is antitone on `(0, 1]`
(more mass at smaller `μ`). -/
theorem sliceYosidaClamp_anti (n : ℕ) {μ₁ μ₂ : ℝ}
    (h₁ : μ₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : μ₂ ∈ Set.Icc (0 : ℝ) 1)
    (h₁0 : μ₁ ≠ 0) (h₂0 : μ₂ ≠ 0) (h : μ₁ ≤ μ₂) :
    sliceYosidaSymbolClamp n μ₂
      ≤ sliceYosidaSymbolClamp n μ₁ := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hL : -Real.log μ₂ ≤ -Real.log μ₁ :=
    neg_le_neg (Real.log_le_log
      (h₁.1.lt_of_ne (Ne.symm h₁0)) h)
  have hL₁ : 0 ≤ -Real.log μ₁ :=
    neg_nonneg.mpr (Real.log_nonpos h₁.1 h₁.2)
  have hL₂ : 0 ≤ -Real.log μ₂ :=
    neg_nonneg.mpr (Real.log_nonpos h₂.1 h₂.2)
  have hpos₁ : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ₁) := by linarith
  have hpos₂ : (0 : ℝ) < sliceYosidaWeight n
      + (-Real.log μ₂) := by linarith
  rw [sliceYosidaClamp_eq_sub n h₁ h₁0,
    sliceYosidaClamp_eq_sub n h₂ h₂0]
  refine sub_le_sub_left ?_ (sliceYosidaWeight n)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_
    (sq_nonneg (sliceYosidaWeight n))
  exact inv_anti₀ hpos₂ (by linarith)

/-- `exp(−·)` is `1`-Lipschitz on `[0, ∞)` in the
form needed here: for `0 ≤ a ≤ L`,
`|exp(−a) − exp(−L)| ≤ L − a`. -/
theorem sliceExp_neg_le {a L : ℝ} (ha : 0 ≤ a)
    (haL : a ≤ L) :
    |Real.exp (-a) - Real.exp (-L)| ≤ L - a := by
  have hmono : Real.exp (-L) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  have hfac : Real.exp (-L)
      = Real.exp (-a) * Real.exp (-(L - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfac]
  have h1 : (1 : ℝ) - Real.exp (-(L - a)) ≤ L - a := by
    have h := Real.add_one_le_exp (-(L - a))
    linarith
  have hc : 0 ≤ (1 : ℝ) - Real.exp (-(L - a)) := by
    have h2 : Real.exp (-(L - a)) ≤ 1 :=
      calc Real.exp (-(L - a)) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    linarith
  have h2 : Real.exp (-a) ≤ 1 :=
    calc Real.exp (-a) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  calc Real.exp (-a)
        - Real.exp (-a) * Real.exp (-(L - a))
      = Real.exp (-a) * (1 - Real.exp (-(L - a))) := by
        ring
    _ ≤ 1 * (L - a) :=
        mul_le_mul h2 h1 hc (by norm_num)
    _ = L - a := one_mul _

/-- **The uniform error bound** for Step C:
with `ηₙ = λₙ⁻¹` as the split point,
`bₙ = λₙ⁻¹ + exp(−(log λₙ)/2) + (log λₙ)²/λₙ`. -/
noncomputable def sliceExpBound (n : ℕ) : ℝ :=
  (sliceYosidaWeight n)⁻¹
    + Real.exp (-(Real.log (sliceYosidaWeight n)
        / 2))
    + (Real.log (sliceYosidaWeight n)) ^ 2
      / sliceYosidaWeight n

/-- The bound is nonnegative. -/
theorem sliceExpBound_nonneg (n : ℕ) :
    0 ≤ sliceExpBound n := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  unfold sliceExpBound
  exact add_nonneg
    (add_nonneg (inv_nonneg.mpr hW.le)
      (Real.exp_nonneg _))
    (div_nonneg (sq_nonneg _) hW.le)

/-- The bound tends to zero. -/
theorem sliceExpBound_tendsto :
    Filter.Tendsto sliceExpBound Filter.atTop
      (nhds 0) := by
  have hW : Filter.Tendsto
      (fun n => sliceYosidaWeight n) Filter.atTop
      Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono
      (fun n => by
        show (n : ℝ) ≤ (n : ℝ) + 1
        have hnn : (0 : ℝ) ≤ (n : ℝ) :=
          Nat.cast_nonneg n
        linarith) h1
  have ht1 : Filter.Tendsto
      (fun n => (sliceYosidaWeight n)⁻¹)
      Filter.atTop (nhds 0) :=
    hW.inv_tendsto_atTop
  have ht2 : Filter.Tendsto
      (fun n => Real.exp
        (-(Real.log (sliceYosidaWeight n) / 2)))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto
        (fun n => Real.log (sliceYosidaWeight n))
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp hW
    have hdiv : Filter.Tendsto
        (fun n => Real.log (sliceYosidaWeight n) / 2)
        Filter.atTop Filter.atTop :=
      hlog.atTop_div_const (by norm_num : (0:ℝ) < 2)
    have hneg : Filter.Tendsto
        (fun n => -(Real.log (sliceYosidaWeight n)
          / 2))
        Filter.atTop Filter.atBot :=
      tendsto_neg_atTop_atBot.comp hdiv
    exact Real.tendsto_exp_atBot.comp hneg
  have ht3 : Filter.Tendsto
      (fun n => (Real.log (sliceYosidaWeight n)) ^ 2
        / sliceYosidaWeight n)
      Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 2 one_ne_zero).comp hW
    simpa only [Function.comp_def, one_mul,
      add_zero] using h
  have hsum := (ht1.add ht2).add ht3
  show Filter.Tendsto (fun n => sliceExpBound n)
    Filter.atTop (nhds 0)
  simpa only [sliceExpBound, add_zero] using hsum

/-- At the split point `ηₙ = λₙ⁻¹`, the clamped
symbol is at least `(log λₙ)/2`. -/
theorem sliceYosidaClamp_half (n : ℕ) :
    Real.log (sliceYosidaWeight n) / 2
      ≤ sliceYosidaSymbolClamp n
        (sliceYosidaWeight n)⁻¹ := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hW1 : (1 : ℝ) ≤ sliceYosidaWeight n := by
    show (1 : ℝ) ≤ (n : ℝ) + 1
    have hnn : (0 : ℝ) ≤ (n : ℝ) :=
      Nat.cast_nonneg n
    linarith
  have hη : (sliceYosidaWeight n)⁻¹
      ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hW.le, inv_le_one_of_one_le₀ hW1⟩
  have hη0 : (sliceYosidaWeight n)⁻¹ ≠ 0 :=
    inv_ne_zero hW.ne'
  have hL0 : 0 ≤ Real.log (sliceYosidaWeight n) :=
    Real.log_nonneg hW1
  have hLW : Real.log (sliceYosidaWeight n)
      ≤ sliceYosidaWeight n :=
    le_trans (Real.log_le_sub_one_of_pos hW)
      (by linarith)
  rw [sliceYosidaClamp_eq n hη hη0, Real.log_inv,
    neg_neg, le_div_iff₀
      (show (0 : ℝ) < sliceYosidaWeight n
        + Real.log (sliceYosidaWeight n) by
        linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hLW hL0]

/-- **The pointwise symbol bound** (Step C's
engine): for every `μ ∈ [0, 1]`,
`|exp(−ãₙ(μ)) − μ| ≤ bₙ`. Split at `ηₙ = λₙ⁻¹`:
below it both sides are small; above it the
Lipschitz bound and the gap formula give
`(log λₙ)²/λₙ`. -/
theorem sliceExpSymbol_le_bound (n : ℕ) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    |Real.exp (-(sliceYosidaSymbolClamp n μ)) - μ|
      ≤ sliceExpBound n := by
  have hW : 0 < sliceYosidaWeight n :=
    sliceYosidaWeight_pos n
  have hW1 : (1 : ℝ) ≤ sliceYosidaWeight n := by
    show (1 : ℝ) ≤ (n : ℝ) + 1
    have hnn : (0 : ℝ) ≤ (n : ℝ) :=
      Nat.cast_nonneg n
    linarith
  have hη : (sliceYosidaWeight n)⁻¹
      ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hW.le, inv_le_one_of_one_le₀ hW1⟩
  have hη0 : (sliceYosidaWeight n)⁻¹ ≠ 0 :=
    inv_ne_zero hW.ne'
  have ht1 : (sliceYosidaWeight n)⁻¹
      ≤ sliceExpBound n := by
    have h2 : 0 ≤ Real.exp
        (-(Real.log (sliceYosidaWeight n) / 2)) :=
      Real.exp_nonneg _
    have h3 : 0 ≤ (Real.log (sliceYosidaWeight n))
        ^ 2 / sliceYosidaWeight n :=
      div_nonneg (sq_nonneg _) hW.le
    unfold sliceExpBound
    linarith
  have ht2 : Real.exp
        (-(Real.log (sliceYosidaWeight n) / 2))
      ≤ sliceExpBound n := by
    have h1 : 0 ≤ (sliceYosidaWeight n)⁻¹ :=
      inv_nonneg.mpr hW.le
    have h3 : 0 ≤ (Real.log (sliceYosidaWeight n))
        ^ 2 / sliceYosidaWeight n :=
      div_nonneg (sq_nonneg _) hW.le
    unfold sliceExpBound
    linarith
  have ht3 : (Real.log (sliceYosidaWeight n)) ^ 2
        / sliceYosidaWeight n
      ≤ sliceExpBound n := by
    have h1 : 0 ≤ (sliceYosidaWeight n)⁻¹ :=
      inv_nonneg.mpr hW.le
    have h2 : 0 ≤ Real.exp
        (-(Real.log (sliceYosidaWeight n) / 2)) :=
      Real.exp_nonneg _
    unfold sliceExpBound
    linarith
  have hhalf := sliceYosidaClamp_half n
  have hexpη : Real.exp
        (-(sliceYosidaSymbolClamp n
          (sliceYosidaWeight n)⁻¹))
      ≤ Real.exp
        (-(Real.log (sliceYosidaWeight n) / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [sliceYosidaClamp_zero, sub_zero,
      abs_of_nonneg (Real.exp_nonneg _)]
    have hle : sliceYosidaSymbolClamp n
          (sliceYosidaWeight n)⁻¹
        ≤ sliceYosidaWeight n := by
      rw [sliceYosidaSymbolClamp_eqOn n hη]
      exact sliceYosidaSymbol_le n hη
    exact le_trans
      (Real.exp_le_exp.mpr (neg_le_neg hle))
      (le_trans hexpη ht2)
  · by_cases hμη : μ ≤ (sliceYosidaWeight n)⁻¹
    · have hanti : sliceYosidaSymbolClamp n
            (sliceYosidaWeight n)⁻¹
          ≤ sliceYosidaSymbolClamp n μ :=
        sliceYosidaClamp_anti n hμ hη hμ0 hη0 hμη
      have he : Real.exp
            (-(sliceYosidaSymbolClamp n μ))
          ≤ Real.exp
            (-(Real.log (sliceYosidaWeight n) / 2)) :=
        le_trans (Real.exp_le_exp.mpr
          (neg_le_neg hanti)) hexpη
      rcases le_total
          (Real.exp (-(sliceYosidaSymbolClamp n μ)))
          μ with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        have hμb : μ ≤ sliceExpBound n :=
          le_trans hμη ht1
        have he0 : 0 ≤ Real.exp
            (-(sliceYosidaSymbolClamp n μ)) :=
          Real.exp_nonneg _
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        linarith [he, ht2, hμ.1]
    · have hμη' : (sliceYosidaWeight n)⁻¹ ≤ μ :=
        (not_le.mp hμη).le
      have hL0 : 0 ≤ -Real.log μ :=
        neg_nonneg.mpr (Real.log_nonpos hμ.1 hμ.2)
      have hLlog : -Real.log μ
          ≤ Real.log (sliceYosidaWeight n) := by
        have h1 : Real.log (sliceYosidaWeight n)⁻¹
            ≤ Real.log μ :=
          Real.log_le_log (inv_pos.mpr hW) hμη'
        rw [Real.log_inv] at h1
        linarith
      have hμpos : 0 < μ :=
        lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
      have hmulog : Real.exp (-(-Real.log μ)) = μ := by
        rw [neg_neg]
        exact Real.exp_log hμpos
      have hgoal : |Real.exp
            (-(sliceYosidaSymbolClamp n μ)) - μ|
          = |Real.exp (-(sliceYosidaSymbolClamp n μ))
            - Real.exp (-(-Real.log μ))| := by
        rw [hmulog]
      rw [hgoal]
      refine le_trans
        (sliceExp_neg_le (sliceYosidaClamp_nonneg n
          hμ) (sliceYosidaClamp_le_log n hμ hμ0)) ?_
      rw [sliceYosidaClamp_gap n hμ hμ0]
      refine le_trans ?_ ht3
      have hsq : (-Real.log μ) ^ 2
          ≤ (Real.log (sliceYosidaWeight n)) ^ 2 :=
        pow_le_pow_left₀ hL0 hLlog 2
      calc (-Real.log μ) ^ 2
            / (sliceYosidaWeight n + (-Real.log μ))
          = (-Real.log μ) ^ 2
              * (sliceYosidaWeight n
                + (-Real.log μ))⁻¹ :=
            div_eq_mul_inv _ _
        _ ≤ (-Real.log μ) ^ 2
              * (sliceYosidaWeight n)⁻¹ :=
            mul_le_mul_of_nonneg_left
              (inv_anti₀ hW (by linarith))
              (pow_nonneg hL0 2)
        _ = (-Real.log μ) ^ 2 / sliceYosidaWeight n :=
            (div_eq_mul_inv _ _).symm
        _ ≤ (Real.log (sliceYosidaWeight n)) ^ 2
              / sliceYosidaWeight n := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hsq
              (inv_nonneg.mpr hW.le)

/-- **Step C (the cfc side converges to `T̂_c`)**:
for every `u ∈ H'`,
`(cfc (exp(−ãₙ)) T̂_c) u.1 → T̂_c u.1` in the
ambient norm — operator-norm convergence from the
pointwise symbol bound `sliceExpSymbol_le_bound`
and `sliceExpBound_tendsto`. -/
theorem sliceCfc_exp_tendsto_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceFormClosure μG ρ hN2 hρcont hN β
      hpos)) :
    Filter.Tendsto
      (fun n => (cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1)
      Filter.atTop
      (nhds ((sliceTc μG ρ hN2 hρcont hN β hpos)
        u.1)) := by
  have hsub : spectrum ℝ
      (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 :=
    sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
  have hdiff : Filter.Tendsto
      (fun n => ‖(cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1
        - (sliceTc μG ρ hN2 hρcont hN β hpos)
          u.1‖)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero
      (g := fun n => sliceExpBound n * ‖u.1‖)
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · have hfe : ContinuousOn
          (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
            hpos)) :=
        (Real.continuous_exp.comp
          (sliceYosidaSymbolClamp_continuous
            n).neg).continuousOn
      have hid : ContinuousOn (fun μ : ℝ => μ)
          (spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β
            hpos)) :=
        continuousOn_id
      have hnorm : ‖cfc (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)) - μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos)‖
          ≤ sliceExpBound n := by
        refine norm_cfc_le (sliceExpBound_nonneg n)
          (fun μ hμ => ?_)
        show |Real.exp (-(sliceYosidaSymbolClamp n
            μ)) - μ| ≤ sliceExpBound n
        exact sliceExpSymbol_le_bound n (hsub hμ)
      have h1 : (cfc (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)))
            (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1
          - (sliceTc μG ρ hN2 hρcont hN β hpos) u.1
        = (cfc (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)) - μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos))
            u.1 := by
        rw [cfc_sub (fun μ => Real.exp
              (-(sliceYosidaSymbolClamp n μ)))
            (fun μ : ℝ => μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            hfe hid,
          sliceCfc_id μG ρ hN2 hρcont hN β hpos,
          ContinuousLinearMap.sub_apply]
      rw [h1]
      exact le_trans (ContinuousLinearMap.le_opNorm
        _ _) (mul_le_mul_of_nonneg_right hnorm
          (norm_nonneg _))
    · have h2 : Filter.Tendsto
          (fun n => sliceExpBound n * ‖u.1‖)
          Filter.atTop (nhds (0 * ‖u.1‖)) :=
        sliceExpBound_tendsto.mul
          (tendsto_const_nhds (x := ‖u.1‖))
      simpa using h2
  have h6 : Filter.Tendsto
      (fun n => (cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1
        - (sliceTc μG ρ hN2 hρcont hN β hpos) u.1)
      Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
  have h7 := h6.add (tendsto_const_nhds (x :=
    (sliceTc μG ρ hN2 hρcont hN β hpos) u.1))
  have h8 : Filter.Tendsto
      (fun n => (cfc (fun μ => Real.exp
            (-(sliceYosidaSymbolClamp n μ)))
          (sliceTc μG ρ hN2 hρcont hN β hpos)) u.1
        - (sliceTc μG ρ hN2 hρcont hN β hpos) u.1
      + (sliceTc μG ρ hN2 hρcont hN β hpos) u.1)
      Filter.atTop
      (nhds (0 + (sliceTc μG ρ hN2 hρcont hN β hpos)
        u.1)) :=
    h7
  have h9 := h8.congr (fun n => sub_add_cancel _ _)
  simpa using h9

/-- **FG-2c-4 IDENTIFY — the headline.** The
semigroup constructed in FG-2c-3 is the transfer
operator's own: `S(1) = T̂_c` as continuous linear
maps on `H' = sliceFormClosure`. Both sides are
limits of the same sequence: `S(1)` by the Yosida
construction (`sliceYosidaS_tendsto`), `T̂_c` by
Step C's uniform symbol bound, and the two
approximating sequences agree term-by-term by
Step B's exponential identity
(`sliceYosidaExp_one_coe`). Uniqueness of limits
closes. This is Stage 2 completeness at FIXED
VOLUME: Items 3/4 are untouched, the dials are
0/4, NO CLAIM. -/
theorem sliceYosidaS_one_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceYosidaS μG ρ hN2 hρcont hN β hpos 1
      = sliceTcRestrict μG ρ hN2 hρcont hN β
        hpos := by
  ext u
  rw [sliceTcRestrict_apply_coe]
  have hS : Filter.Tendsto
      (fun n => ((sliceYosidaExp μG ρ hN2 hρcont
          hN β hpos 1 n) u).1)
      Filter.atTop
      (nhds ((sliceYosidaS μG ρ hN2 hρcont hN β
        hpos 1) u).1) :=
    (continuous_subtype_val.tendsto _).comp
      (sliceYosidaS_tendsto μG ρ hN2 hρcont hN β
        hpos 1 (by norm_num) u)
  have hC : Filter.Tendsto
      (fun n => ((sliceYosidaExp μG ρ hN2 hρcont
          hN β hpos 1 n) u).1)
      Filter.atTop
      (nhds ((sliceTc μG ρ hN2 hρcont hN β hpos)
        u.1)) :=
    Filter.Tendsto.congr
      (fun n => (sliceYosidaExp_one_coe μG ρ hN2
        hρcont hN β hpos n u).symm)
      (sliceCfc_exp_tendsto_apply μG ρ hN2 hρcont
        hN β hpos u)
  exact tendsto_nhds_unique hS hC

/-! ## §6. The battery corollary — the Jensen clause

The Jensen clause of `SliceSpectralCorrespondence` is
proved ELEMENTARILY here, at a general seat, with no
spectral measure: the battery energy `E x =
sliceFormVal (x.1).1` dominates every approximant
`q_K = ∑_{j=1}^K j⁻¹ a_j`, `a_j = ⟪x, Â_c^j x⟫.re`; the
moments obey `a_{j+1} ≥ a_j · a_1` (positivity of
`((1−μ) − a_1)((1−μ)^j − a_1^j)` in the `cfc` pairing);
hence `a_j ≥ a_1^j`, the approximants dominate the
logarithmic series, and `E x ≥ −log (1 − a_1)`, i.e.
`exp (−E x) ≤ 1 − a_1 = ⟪x, T̂_c x⟫.re`. The case
`a_1 = 1` is excluded by divergence of the harmonic
series against the finiteness of `E x`. The GAP clause
(`⟪x, T̂_c x⟫.re ≤ 1 − δ`) is NOT proved here:
`GapBoundU1` bounds the spectrum of the PRE-completion
`transferOp`, and no transport of that bound to the
completed `T̂_c`'s pairings exists in the record; it
remains the correspondence's one named open clause. -/

/-- Pairings split over pointwise differences of
functions. -/
theorem sliceJensen_pairing_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ y (cfc (fun μ => f μ - g μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (inner ℂ y (cfc f
            (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
        - (inner ℂ y (cfc g
            (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re := by
  rw [cfc_sub f g (sliceTc μG ρ hN2 hρcont hN β hpos)
    hf.continuousOn hg.continuousOn,
    ContinuousLinearMap.sub_apply, inner_sub_right,
    Complex.sub_re]

/-- Pairings split over pointwise sums of functions. -/
theorem sliceJensen_pairing_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ y (cfc (fun μ => f μ + g μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (inner ℂ y (cfc f
            (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
        + (inner ℂ y (cfc g
            (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re := by
  rw [cfc_add (sliceTc μG ρ hN2 hρcont hN β hpos) f g
    hf.continuousOn hg.continuousOn,
    ContinuousLinearMap.add_apply, inner_add_right,
    Complex.add_re]

/-- **J2 — the approximant as a moment sum**:
`q_K(y) = ∑_{j=1}^K j⁻¹ · a_j` with moments
`a_j = ⟪y, Â_c^j y⟫.re`. -/
theorem sliceJensen_approxC_sum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K y
      = ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
          * (inner ℂ y (((sliceAc μG ρ hN2 hρcont hN β
              hpos) ^ j) y)).re := by
  unfold sliceHamFormApproxC
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← sliceAc_pow_apply μG ρ hN2 hρcont hN β hpos j y]

/-- **J1 — every approximant is below the form value**
(at any vector of finite form value). -/
theorem sliceJensen_approxC_le_formVal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hfin : sliceHamFormC μG ρ hN2 hρcont hN β hpos y
      ≠ ⊤) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K y
      ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos y := by
  have hle := sliceHamFormApproxC_le μG ρ hN2 hρcont hN
    β hpos K y
  have h2 := (ENNReal.toReal_le_toReal
    ENNReal.ofReal_ne_top hfin).mpr hle
  rwa [ENNReal.toReal_ofReal
    (sliceHamFormApproxC_nonneg μG ρ hN2 hρcont hN β
      hpos K y)] at h2

/-- **The moments** of a vector under the completed
defect: `a_j(y) = ⟪y, Â_c^j y⟫.re`. -/
noncomputable def sliceJensenMoment (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (j : ℕ) : ℝ :=
  (inner ℂ y (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
    y)).re

/-- **J3a — the first moment is the defect pairing.** -/
theorem sliceJensen_first_moment (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ y (cfc (fun μ : ℝ => 1 - μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1 := by
  have hfun : (fun μ : ℝ => (1 : ℝ) - μ)
      = (fun μ : ℝ => (1 - μ) ^ 1) := by
    funext μ
    rw [pow_one]
  unfold sliceJensenMoment
  rw [hfun, sliceCfc_defect_pow μG ρ hN2 hρcont hN β
    hpos 1]

/-- **J3b — the transfer pairing is `1 − a₁`** for unit
`y` (since `Â_c = 1 − T̂_c`). -/
theorem sliceJensen_tc_pairing (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hy : ‖y‖ = 1) :
    (inner ℂ y ((sliceTc μG ρ hN2 hρcont hN β hpos)
        y)).re
      = 1 - sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1 := by
  have hself : (inner ℂ y y).re = 1 := by
    have h : (inner ℂ y y) = ((‖y‖ : ℂ)) ^ 2 :=
      inner_self_eq_norm_sq_to_K y
    rw [h, hy]
    simp
  have hA : sliceJensenMoment μG ρ hN2 hρcont hN β
        hpos y 1
      = (inner ℂ y y).re
        - (inner ℂ y ((sliceTc μG ρ hN2 hρcont hN β
            hpos) y)).re := by
    unfold sliceJensenMoment
    rw [pow_one, sliceAc_eq μG ρ hN2 hρcont hN β hpos,
      ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, inner_sub_right,
      Complex.sub_re]
  rw [hself] at hA
  linarith

/-- **J4 — the moment recursion** `a_j · a₁ ≤ a_{j+1}`:
positivity of `((1−μ) − a₁)((1−μ)^j − a₁^j)` in the
`cfc` pairing (its two factors have the same sign on
`[0, 1]`). -/
theorem sliceJensen_moment_step (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hy : ‖y‖ = 1)
    (ha1nn : 0 ≤ sliceJensenMoment μG ρ hN2 hρcont hN
      β hpos y 1)
    (ha1le : sliceJensenMoment μG ρ hN2 hρcont hN β
      hpos y 1 ≤ 1)
    (j : ℕ) :
    sliceJensenMoment μG ρ hN2 hρcont hN β hpos y j
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1
      ≤ sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y (j + 1) := by
  have hpos_pair : 0 ≤ (inner ℂ y
      (cfc (fun μ : ℝ =>
        ((1 - μ) - sliceJensenMoment μG ρ hN2 hρcont
          hN β hpos y 1)
        * ((1 - μ) ^ j
          - (sliceJensenMoment μG ρ hN2 hρcont hN β
              hpos y 1) ^ j))
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re := by
    refine sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN
      β hpos _ (fun μ hμ => ?_) y
    have ht0 : 0 ≤ 1 - μ := sub_nonneg.mpr hμ.2
    rcases le_total (1 - μ)
        (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr h)
        (sub_nonpos.mpr (pow_le_pow_left₀ ht0 h j))
    · exact mul_nonneg (sub_nonneg.mpr h)
        (sub_nonneg.mpr
          (pow_le_pow_left₀ ha1nn h j))
  have hfunid : (fun μ : ℝ =>
        ((1 - μ) - sliceJensenMoment μG ρ hN2 hρcont
          hN β hpos y 1)
        * ((1 - μ) ^ j
          - (sliceJensenMoment μG ρ hN2 hρcont hN β
              hpos y 1) ^ j))
      = (fun μ : ℝ =>
          ((1 - μ) ^ (j + 1)
            - sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1 * (1 - μ) ^ j)
          - ((sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1) ^ j * (1 - μ)
            - (sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1) ^ (j + 1))) := by
    funext μ
    ring
  have hsplit1 : (inner ℂ y
        (cfc (fun μ : ℝ =>
          ((1 - μ) ^ (j + 1)
            - sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1 * (1 - μ) ^ j)
          - ((sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1) ^ j * (1 - μ)
            - (sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1) ^ (j + 1)))
          (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (inner ℂ y
          (cfc (fun μ : ℝ => (1 - μ) ^ (j + 1)
              - sliceJensenMoment μG ρ hN2 hρcont hN
                β hpos y 1 * (1 - μ) ^ j)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            y)).re
        - (inner ℂ y
            (cfc (fun μ : ℝ =>
                (sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos y 1) ^ j * (1 - μ)
                - (sliceJensenMoment μG ρ hN2 hρcont
                    hN β hpos y 1) ^ (j + 1))
              (sliceTc μG ρ hN2 hρcont hN β hpos)
              y)).re :=
    sliceJensen_pairing_sub μG ρ hN2 hρcont hN β
      hpos
      (fun μ : ℝ => (1 - μ) ^ (j + 1)
        - sliceJensenMoment μG ρ hN2 hρcont hN β
          hpos y 1 * (1 - μ) ^ j)
      (fun μ : ℝ =>
        (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ j * (1 - μ)
        - (sliceJensenMoment μG ρ hN2 hρcont hN β
            hpos y 1) ^ (j + 1))
      (by fun_prop) (by fun_prop) y
  have hsplit2 : (inner ℂ y
        (cfc (fun μ : ℝ => (1 - μ) ^ (j + 1)
            - sliceJensenMoment μG ρ hN2 hρcont hN β
              hpos y 1 * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (inner ℂ y
          (cfc (fun μ : ℝ => (1 - μ) ^ (j + 1))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            y)).re
        - (inner ℂ y
            (cfc (fun μ : ℝ =>
                sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos y 1 * (1 - μ) ^ j)
              (sliceTc μG ρ hN2 hρcont hN β hpos)
              y)).re :=
    sliceJensen_pairing_sub μG ρ hN2 hρcont hN β
      hpos
      (fun μ : ℝ => (1 - μ) ^ (j + 1))
      (fun μ : ℝ => sliceJensenMoment μG ρ hN2
        hρcont hN β hpos y 1 * (1 - μ) ^ j)
      (by fun_prop) (by fun_prop) y
  have hsplit3 : (inner ℂ y
        (cfc (fun μ : ℝ =>
            (sliceJensenMoment μG ρ hN2 hρcont hN β
              hpos y 1) ^ j * (1 - μ)
            - (sliceJensenMoment μG ρ hN2 hρcont hN
                β hpos y 1) ^ (j + 1))
          (sliceTc μG ρ hN2 hρcont hN β hpos)
          y)).re
      = (inner ℂ y
          (cfc (fun μ : ℝ =>
              (sliceJensenMoment μG ρ hN2 hρcont hN β
                hpos y 1) ^ j * (1 - μ))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            y)).re
        - (inner ℂ y
            (cfc (fun _ : ℝ =>
                (sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos y 1) ^ (j + 1))
              (sliceTc μG ρ hN2 hρcont hN β hpos)
              y)).re :=
    sliceJensen_pairing_sub μG ρ hN2 hρcont hN β
      hpos
      (fun μ : ℝ =>
        (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ j * (1 - μ))
      (fun _ : ℝ => (sliceJensenMoment μG ρ hN2
        hρcont hN β hpos y 1) ^ (j + 1))
      (by fun_prop) (by fun_prop) y
  rw [hfunid, hsplit1, hsplit2, hsplit3] at hpos_pair
  have e1 : (inner ℂ y (cfc (fun μ : ℝ => (1 - μ)
        ^ (j + 1)) (sliceTc μG ρ hN2 hρcont hN β
        hpos) y)).re
      = sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y (j + 1) := by
    unfold sliceJensenMoment
    rw [sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos
      (j + 1)]
  have e2 : (inner ℂ y (cfc (fun μ : ℝ =>
        sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1 * (1 - μ) ^ j)
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
            y j := by
    rw [sliceCfc_factor_re μG ρ hN2 hρcont hN β hpos
      _ (fun μ : ℝ => (1 - μ) ^ j)
      ((continuous_const.sub continuous_id).pow _) y]
    unfold sliceJensenMoment
    rw [sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos j]
  have e3 : (inner ℂ y (cfc (fun μ : ℝ =>
        (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ j * (1 - μ))
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ j
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
            y 1 := by
    rw [sliceCfc_factor_re μG ρ hN2 hρcont hN β hpos
      _ (fun μ : ℝ => 1 - μ)
      (continuous_const.sub continuous_id) y,
      sliceJensen_first_moment μG ρ hN2 hρcont hN β
        hpos y]
  have e4 : (inner ℂ y (cfc (fun _ : ℝ =>
        (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ (j + 1))
        (sliceTc μG ρ hN2 hρcont hN β hpos) y)).re
      = (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ (j + 1) := by
    rw [sliceCfc_pairing_const μG ρ hN2 hρcont hN β
      hpos _ y, hy]
    norm_num
  rw [e1, e2, e3, e4] at hpos_pair
  have hpow : (sliceJensenMoment μG ρ hN2 hρcont hN
        β hpos y 1) ^ (j + 1)
      = (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1) ^ j
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
            y 1 := pow_succ _ j
  have hcomm : sliceJensenMoment μG ρ hN2 hρcont hN
        β hpos y 1
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y j
      = sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y j
        * sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y 1 := mul_comm _ _
  linarith

/-- **J5 — moments dominate powers of the first**:
`a₁^j ≤ a_j`. -/
theorem sliceJensen_moment_pow (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hy : ‖y‖ = 1)
    (ha1nn : 0 ≤ sliceJensenMoment μG ρ hN2 hρcont hN
      β hpos y 1)
    (ha1le : sliceJensenMoment μG ρ hN2 hρcont hN β
      hpos y 1 ≤ 1)
    (j : ℕ) :
    (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
        y 1) ^ j
      ≤ sliceJensenMoment μG ρ hN2 hρcont hN β hpos
          y j := by
  induction j with
  | zero =>
      have hA0 : sliceJensenMoment μG ρ hN2 hρcont hN
            β hpos y 0 = 1 := by
        have hself : (inner ℂ y y).re = 1 := by
          have h : (inner ℂ y y) = ((‖y‖ : ℂ)) ^ 2 :=
            inner_self_eq_norm_sq_to_K y
          rw [h, hy]
          simp
        unfold sliceJensenMoment
        rw [pow_zero, ContinuousLinearMap.one_apply]
        exact hself
      rw [hA0, pow_zero]
  | succ j ih =>
      rw [pow_succ]
      exact le_trans
        (mul_le_mul_of_nonneg_right ih ha1nn)
        (sliceJensen_moment_step μG ρ hN2 hρcont hN β
          hpos y hy ha1nn ha1le j)

/-- The reindexing bridge: `Icc 1 K` sums of
`j ↦ j⁻¹ b^j` are `range K` sums of the logarithmic
series terms. -/
theorem sliceJensen_sum_bridge (b : ℝ) (K : ℕ) :
    (∑ i ∈ Finset.range K, b ^ (i + 1) / ((i : ℝ) + 1))
      = ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * b ^ j := by
  rw [← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hc1 : ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 := by
    push_cast
    ring
  rw [hc1, add_comm (1 : ℕ) i, div_eq_mul_inv, mul_comm]

/-- **THE JENSEN CLAUSE (general seat).** For every
unit domain state `u` of `Ĥ`, `exp (−E u) ≤ ⟪u, T̂_c
u⟫.re` — elementarily, with no spectral measure and
NO vacuum-orthogonality hypothesis. The case `a₁ < 1`
runs through the logarithmic series; the case
`a₁ = 1` is excluded by harmonic divergence against
the finiteness of the form value. -/
theorem sliceJensen (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : ↥(sliceHamOperatorDomain μG ρ hN2 hρcont hN
      β hpos))
    (hu : ‖u.1‖ = 1) :
    Real.exp (- sliceBatteryEnergy μG ρ hN2 hρcont
        hN β hpos u)
      ≤ (inner ℂ (u.1).1 ((sliceTc μG ρ hN2 hρcont
          hN β hpos) (u.1).1)).re := by
  have hnormy : ‖(u.1).1‖ = 1 := by
    rw [Submodule.norm_coe]
    exact hu
  have hfin : sliceHamFormC μG ρ hN2 hρcont hN β hpos
        (u.1).1 ≠ ⊤ := by
    rw [← sliceHamC_mem_domain_iff μG ρ hN2 hρcont hN
      β hpos]
    have h2 := (sliceHamLift μG ρ hN2 hρcont hN β hpos
      u).toSub.2
    rwa [← sliceFormDomain.val_eq μG ρ hN2 hρcont hN
      β hpos _, sliceHamLift_val μG ρ hN2 hρcont hN β
      hpos u] at h2
  have ha1nn : 0 ≤ sliceJensenMoment μG ρ hN2 hρcont
        hN β hpos (u.1).1 1 := by
    rw [← sliceJensen_first_moment μG ρ hN2 hρcont hN
      β hpos (u.1).1]
    exact sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN β
      hpos (fun μ : ℝ => 1 - μ)
      (fun μ hμ => sub_nonneg.mpr hμ.2) (u.1).1
  have hTc := sliceJensen_tc_pairing μG ρ hN2 hρcont
    hN β hpos (u.1).1 hnormy
  have ha1le : sliceJensenMoment μG ρ hN2 hρcont hN β
        hpos (u.1).1 1 ≤ 1 := by
    have hnn : 0 ≤ (inner ℂ (u.1).1
        ((sliceTc μG ρ hN2 hρcont hN β hpos)
          (u.1).1)).re := by
      rw [← sliceCfc_id μG ρ hN2 hρcont hN β hpos]
      exact sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN
        β hpos (fun μ : ℝ => μ) (fun μ hμ => hμ.1)
        (u.1).1
    linarith
  rw [sliceBatteryEnergy_eq_formVal μG ρ hN2 hρcont
    hN β hpos u, hTc]
  rcases lt_or_eq_of_le ha1le with hlt | heq
  · -- Case `a₁ < 1`: the logarithmic series.
    have habs : |sliceJensenMoment μG ρ hN2 hρcont hN
          β hpos (u.1).1 1| < 1 := by
      rwa [abs_of_nonneg ha1nn]
    have hlim := (Real.hasSum_pow_div_log_of_abs_lt_one
      habs).tendsto_sum_nat
    have hbound : ∀ K : ℕ,
        (∑ i ∈ Finset.range K,
          (sliceJensenMoment μG ρ hN2 hρcont hN β hpos
            (u.1).1 1) ^ (i + 1) / ((i : ℝ) + 1))
          ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
              (u.1).1 := by
      intro K
      rw [sliceJensen_sum_bridge]
      calc ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
              * (sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos (u.1).1 1) ^ j
          ≤ ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
              * sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos (u.1).1 j :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left
                (sliceJensen_moment_pow μG ρ hN2
                  hρcont hN β hpos (u.1).1 hnormy ha1nn
                  ha1le j)
                (inv_nonneg.mpr (Nat.cast_nonneg j)))
        _ = sliceHamFormApproxC μG ρ hN2 hρcont hN β
              hpos K (u.1).1 := by
            rw [sliceJensen_approxC_sum μG ρ hN2
              hρcont hN β hpos K (u.1).1]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rfl
        _ ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
              (u.1).1 :=
            sliceJensen_approxC_le_formVal μG ρ hN2
              hρcont hN β hpos K (u.1).1 hfin
    have hE : -Real.log (1 - sliceJensenMoment μG ρ
          hN2 hρcont hN β hpos (u.1).1 1)
        ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
            (u.1).1 :=
      le_of_tendsto_of_tendsto hlim tendsto_const_nhds
        (Filter.Eventually.of_forall hbound)
    have h1 := neg_le_neg hE
    rw [neg_neg] at h1
    calc Real.exp (- sliceFormVal μG ρ hN2 hρcont hN
            β hpos (u.1).1)
        ≤ Real.exp (Real.log
            (1 - sliceJensenMoment μG ρ hN2 hρcont hN
              β hpos (u.1).1 1)) :=
          Real.exp_le_exp.mpr h1
      _ = 1 - sliceJensenMoment μG ρ hN2 hρcont hN β
            hpos (u.1).1 1 :=
          Real.exp_log (sub_pos.mpr hlt)
  · -- Case `a₁ = 1`: harmonic divergence contradicts
    -- the finiteness of the form value.
    exfalso
    have hbound : ∀ K : ℕ,
        (∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
          ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
              (u.1).1 := by
      intro K
      have hb1 : (∑ i ∈ Finset.range K,
            1 / ((i : ℝ) + 1))
          = ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * 1 := by
        have hbr := sliceJensen_sum_bridge 1 K
        simpa using hbr
      rw [hb1]
      calc ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * 1
          ≤ ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
              * sliceJensenMoment μG ρ hN2 hρcont hN
                  β hpos (u.1).1 j :=
            Finset.sum_le_sum (fun j _ => by
              refine mul_le_mul_of_nonneg_left ?_
                (inv_nonneg.mpr (Nat.cast_nonneg j))
              have h2 := sliceJensen_moment_pow μG ρ
                hN2 hρcont hN β hpos (u.1).1 hnormy
                ha1nn ha1le j
              rwa [heq, one_pow] at h2)
        _ = sliceHamFormApproxC μG ρ hN2 hρcont hN β
              hpos K (u.1).1 := by
            rw [sliceJensen_approxC_sum μG ρ hN2
              hρcont hN β hpos K (u.1).1]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rfl
        _ ≤ sliceFormVal μG ρ hN2 hρcont hN β hpos
              (u.1).1 :=
            sliceJensen_approxC_le_formVal μG ρ hN2
              hρcont hN β hpos K (u.1).1 hfin
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      ((tendsto_atTop.mp
        Real.tendsto_sum_range_one_div_nat_succ_atTop)
        (sliceFormVal μG ρ hN2 hρcont hN β hpos (u.1).1
          + 1))
    have hle := le_trans (hK K (le_refl K)) (hbound K)
    linarith

/-- **The battery's Jensen clause, discharged** (circle
seat): for every unit domain state — the
vacuum-orthogonality hypothesis of
`SliceSpectralCorrespondence` is NOT needed — its
Jensen (first) conjunct holds. The correspondence as a
whole remains a named hypothesis of the battery's T4
until its gap clause (`⟪x, T̂_c x⟫.re ≤ 1 − δ`) is
transported from `transferOp`'s pre-completion
spectrum to the completed operator's pairings; no
such transport exists in the record. -/
theorem sliceBattery_jensen (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N)
    (hpos : SliceHPosOne (haarProb Circle) circleRep
      hN2 circleRep_continuous β)
    (x : ↥(sliceHamOperatorDomain (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos))
    (hx : ‖x.1‖ = 1) :
    Real.exp (- sliceBatteryEnergy (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos
        x)
      ≤ (inner ℂ (x.1).1 (sliceTc (haarProb Circle)
          circleRep hN2 circleRep_continuous hN β hpos
            (x.1).1)).re :=
  sliceJensen (haarProb Circle) circleRep hN2
    circleRep_continuous hN β hpos x hx

end SliceIdentify

end ThetLogos
