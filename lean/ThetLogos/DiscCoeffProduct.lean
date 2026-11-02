import Mathlib.Analysis.Analytic.OfScalars
import ThetLogos.HfcDiscForward

/-!
# B4-PROD — the coefficient-product identity (SHELF-7b-disc chain, GATE-B)

Brick B4-PROD of the SHELF line (scoping
`whitepaper/scoping-gate-b4-2026-11-02.md`, ingredient 2b; pack
`routeb-general-scratch/pack-gate-b4-prod.md`).

## Verdict shape — read this first

The scoping's registered route (2b) proves the identity at an
*interior* presenting radius: "for `h k` holomorphic on a disc of
radius `> R'`, presenting at interior `R'`". That is the form
landed here, at full rank:

`discCoeff_mul`: for `DiscHolomorphic h R`, `DiscHolomorphic k R`
and every `0 < P < R`,
`discCoeff (fun z => h z * k z) P
  = discConv (discCoeff h P) (discCoeff k P)`,
with product holomorphicity at `R` *proved*
(`discHolomorphic_mul`), not assumed. The corollary
`discCoeff_mul_of_lt_radius` restates it in the "same radius"
shape under the strictly-larger holomorphicity radius the route
actually needs.

The literal boundary form — the same identity presented at the
holomorphicity radius `R` itself, from `DiscHolomorphic h R`
alone — is FALSE, for the same reason B1c's frozen form was
false: `discCoeff f R` reads only the values of `f` on the
circle `‖z‖ = R`, which open-disc holomorphicity does not
constrain. The kill is landed at full rank below
(`discCoeff_mul_boundary_not`): with `R = 1`,
`h z = z⁻¹` on `‖z‖ = 1` and `0` inside (so `DiscHolomorphic h 1`
and every `discCoeff h 1 n` is unconstrained by the interior),
and `k z = z`, the product is `1` on the circle and `0` inside,
so its zeroth coefficient is `1`
(`discCoeff_boundary_counterexample`), while the convolution's
zeroth coefficient is `discCoeff h 1 0 * discCoeff k 1 0 = 0`
because `discCoeff (fun z => z) 1 0 = 0`
(`discCoeff_id_zero`). This is a deviation from the pack's
literal target statement, forced by the mathematics; the
scoping's own route text (presenting at interior `R'`) is what
is landed, and B4-UNIT's consumption (presenting at `R₀`
strictly inside the zero-free radius) is exactly this form.

## Route (scoping 2b, steps 1–5)

1. Scalar Cauchy product at every interior point:
   `hasSum_discConv_discCoeff`, via the pin's
   `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
   applied to the two scalar series, absolute summability from
   B1b interior (`discSummable_discCoeff_interior`) and the
   values from corrected B1c (`scalarEval_discCoeff_eq_of_lt`).
2. Existence half: `hasFPowerSeriesOnBall_discConv_mul` — the
   product has the `ofScalars` Cauchy-product series as a
   `HasFPowerSeriesOnBall` at every interior radius `P`
   (radius lower bound from the `DiscSummable` majorant at
   scale `P` itself, via `FormalMultilinearSeries.
   le_radius_of_summable_norm` and 8a's `discSummable_conv`).
3. Uniqueness: against `DifferentiableOn.hasFPowerSeriesOnBall`
   for the product (closed-ball restriction at `P < R`), via
   `HasFPowerSeriesAt.eq_formalMultilinearSeries` — the exact
   pattern of B3′'s `discCoeff_const`. The pre-named PARTIAL
   seam (uniqueness unreachable) does NOT trigger.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

/-! ## Product holomorphicity (proved, not assumed) -/

/-- The product of two disc-holomorphic functions is
disc-holomorphic at the same radius. -/
theorem discHolomorphic_mul {h k : ℂ → ℂ} {R : ℝ}
    (hh : DiscHolomorphic h R) (hk : DiscHolomorphic k R) :
    DiscHolomorphic (fun z => h z * k z) R :=
  ⟨hh.1, hh.2.mul hk.2⟩

/-! ## Summability helpers -/

/-- Norm-summability of an interior-presented scalar coefficient
series at an interior point, from B1b interior summability. -/
theorem summable_norm_discCoeff_mul_pow {f : ℂ → ℂ} {R P : ℝ}
    (hf : DiscHolomorphic f R) (hPR : P < R) {z : ℂ} (hz : ‖z‖ < P) :
    Summable fun n => ‖discCoeff f P n * z ^ n‖ := by
  have hDisc : DiscSummable ‖z‖ (discCoeff f P) :=
    discSummable_discCoeff_interior hf hPR (norm_nonneg z) hz
  exact Summable.congr hDisc fun n => by rw [norm_mul, norm_pow]

/-- `DiscSummable` of an interior-presented coefficient sequence
at its own presenting scale: present at an intermediate radius
`Q`, `P < Q < R`, where B1b applies, and transport back by B1a
(`discCoeff_indep`). -/
theorem discSummable_discCoeff_presented_self {f : ℂ → ℂ} {R P : ℝ}
    (hf : DiscHolomorphic f R) (hP0 : 0 < P) (hPR : P < R) :
    DiscSummable P (discCoeff f P) := by
  obtain ⟨Q, hPQ, hQR⟩ := exists_between hPR
  have hQ0 : 0 < Q := hP0.trans hPQ
  have hDiscQ : DiscSummable P (discCoeff f Q) :=
    discSummable_discCoeff (discHolomorphic_of_lt hf hQ0 hQR) hP0.le hPQ
  rwa [discCoeff_indep hf hQ0 hQR hP0 hPR] at hDiscQ

/-! ## Step 1 — the scalar Cauchy product -/

/-- The Cauchy product of the two interior-presented scalar
series sums to the product value at every interior point
(scoping 2b step 1). -/
theorem hasSum_discConv_discCoeff {h k : ℂ → ℂ} {R P : ℝ}
    (hh : DiscHolomorphic h R) (hk : DiscHolomorphic k R)
    (hP0 : 0 < P) (hPR : P < R) {z : ℂ} (hz : ‖z‖ < P) :
    HasSum (fun n => discConv (discCoeff h P) (discCoeff k P) n * z ^ n)
      (h z * k z) := by
  have hsumn_h := summable_norm_discCoeff_mul_pow hh hPR hz
  have hsumn_k := summable_norm_discCoeff_mul_pow hk hPR hz
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hsumn_h hsumn_k
  have hval_h : (∑' n, discCoeff h P n * z ^ n) = h z :=
    scalarEval_discCoeff_eq_of_lt hh hP0 hPR hz
  have hval_k : (∑' n, discCoeff k P n * z ^ n) = k z :=
    scalarEval_discCoeff_eq_of_lt hk hP0 hPR hz
  have hterm : ∀ n, (∑ kl ∈ Finset.antidiagonal n,
        (discCoeff h P kl.1 * z ^ kl.1) * (discCoeff k P kl.2 * z ^ kl.2))
      = discConv (discCoeff h P) (discCoeff k P) n * z ^ n := by
    intro n
    rw [discConv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    rw [← hsum, pow_add]; ring
  have hDiscConv : DiscSummable ‖z‖
      (discConv (discCoeff h P) (discCoeff k P)) :=
    discSummable_conv (norm_nonneg z)
      (discSummable_discCoeff_interior hh hPR (norm_nonneg z) hz)
      (discSummable_discCoeff_interior hk hPR (norm_nonneg z) hz)
  have hsumm : Summable
      fun n => discConv (discCoeff h P) (discCoeff k P) n * z ^ n :=
    (Summable.congr hDiscConv fun n => by rw [norm_mul, norm_pow]).of_norm
  refine hsumm.hasSum_iff.mpr ?_
  calc (∑' n, discConv (discCoeff h P) (discCoeff k P) n * z ^ n)
      = ∑' n, ∑ kl ∈ Finset.antidiagonal n,
          (discCoeff h P kl.1 * z ^ kl.1)
            * (discCoeff k P kl.2 * z ^ kl.2) :=
        tsum_congr fun n => (hterm n).symm
    _ = (∑' n, discCoeff h P n * z ^ n)
          * (∑' n, discCoeff k P n * z ^ n) := hprod.symm
    _ = h z * k z := by rw [hval_h, hval_k]

/-! ## Step 2 — existence half: the product's `HasFPowerSeriesOnBall`
with the Cauchy-product series -/

/-- The product has the Cauchy-product `ofScalars` series as a
power series on every interior ball (scoping 2b step 2). This
is the brick's pre-named existence half, landed as a standalone
lemma; the uniqueness step below closes the identity, so the
PARTIAL seam does not trigger. -/
theorem hasFPowerSeriesOnBall_discConv_mul {h k : ℂ → ℂ} {R P : ℝ}
    (hh : DiscHolomorphic h R) (hk : DiscHolomorphic k R)
    (hP0 : 0 < P) (hPR : P < R) {rnn : ℝ≥0} (hrnn : (rnn : ℝ) = P) :
    HasFPowerSeriesOnBall (fun z => h z * k z)
      (FormalMultilinearSeries.ofScalars ℂ
        (discConv (discCoeff h P) (discCoeff k P)))
      0 (rnn : ℝ≥0∞) := by
  have hDiscP : DiscSummable P
      (discConv (discCoeff h P) (discCoeff k P)) :=
    discSummable_conv hP0.le
      (discSummable_discCoeff_presented_self hh hP0 hPR)
      (discSummable_discCoeff_presented_self hk hP0 hPR)
  refine ⟨?_, ?_, ?_⟩
  · refine (FormalMultilinearSeries.ofScalars ℂ
        (discConv (discCoeff h P) (discCoeff k P))).le_radius_of_summable_norm
      (r := rnn) ?_
    rw [hrnn]
    refine Summable.congr hDiscP fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
  · have h0 : (0 : ℝ) < (rnn : ℝ) := hrnn.symm ▸ hP0
    simpa using h0
  · intro y hy
    have hy' : ‖y‖ < P := by
      rw [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero,
        ← ENNReal.ofReal_coe_nnreal, hrnn] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff hP0).mp hy
    rw [zero_add]
    have hfun : (fun n => FormalMultilinearSeries.ofScalars ℂ
          (discConv (discCoeff h P) (discCoeff k P)) n (fun _ => y))
        = (fun n => discConv (discCoeff h P) (discCoeff k P) n * y ^ n) := by
      rw [FormalMultilinearSeries.ofScalars_apply_eq']
      funext n
      rw [smul_eq_mul]
    rw [hfun]
    exact hasSum_discConv_discCoeff hh hk hP0 hPR hy'

/-! ## Steps 3–5 — uniqueness and the coefficient identity -/

/-- **Headline (interior form).** The coefficient-product
identity at every interior presenting radius: for `h k`
holomorphic on the disc of radius `R` and `0 < P < R`,
the coefficients of the product at `P` are the Cauchy product
of the coefficients at `P`. Product holomorphicity at `R` is
proved (`discHolomorphic_mul`), not assumed. -/
theorem discCoeff_mul {h k : ℂ → ℂ} {R P : ℝ}
    (hh : DiscHolomorphic h R) (hk : DiscHolomorphic k R)
    (hP0 : 0 < P) (hPR : P < R) :
    discCoeff (fun z => h z * k z) P
      = discConv (discCoeff h P) (discCoeff k P) := by
  funext n
  have hdiff : DifferentiableOn ℂ (fun z => h z * k z)
      (Metric.closedBall 0 P) :=
    (hh.2.mul hk.2).mono (Metric.closedBall_subset_ball hPR)
  let rnn : ℝ≥0 := ⟨P, hP0.le⟩
  have hrnnR : (rnn : ℝ) = P := rfl
  have hcauchy : HasFPowerSeriesOnBall (fun z => h z * k z)
      (cauchyPowerSeries (fun z => h z * k z) 0 (rnn : ℝ)) 0 (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall hdiff hP0
  have heq : cauchyPowerSeries (fun z => h z * k z) 0 (rnn : ℝ)
      = FormalMultilinearSeries.ofScalars ℂ
          (discConv (discCoeff h P) (discCoeff k P)) :=
    hcauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_discConv_mul hh hk hP0 hPR
        (rnn := ⟨P, hP0.le⟩) rfl).hasFPowerSeriesAt
  have h3 : cauchyPowerSeries (fun z => h z * k z) 0 (rnn : ℝ) n
        (fun _ => (1 : ℂ))
      = FormalMultilinearSeries.ofScalars ℂ
          (discConv (discCoeff h P) (discCoeff k P)) n (fun _ => (1 : ℂ)) := by
    rw [heq]
  rw [hrnnR] at h3
  show cauchyPowerSeries (fun z => h z * k z) 0 P n (fun _ => (1 : ℂ)) = _
  rw [h3]
  simp

/-- The identity in "same radius" shape, under the hypothesis
the route actually needs: holomorphicity on a strictly larger
disc than the presenting radius. -/
theorem discCoeff_mul_of_lt_radius {h k : ℂ → ℂ} {R Rbig : ℝ}
    (hh : DiscHolomorphic h Rbig) (hk : DiscHolomorphic k Rbig)
    (hR0 : 0 < R) (hR : R < Rbig) :
    discCoeff (fun z => h z * k z) R
      = discConv (discCoeff h R) (discCoeff k R) :=
  discCoeff_mul hh hk hR0 hR

/-! ## The literal boundary form is false (kill, at full rank) -/

/-- The zeroth coefficient of the identity function at radius
`1` vanishes: on the circle the Cauchy kernel times `z` is
`1`, whose circle integral is `0`. -/
theorem discCoeff_id_zero :
    discCoeff (fun z : ℂ => z) 1 0 = 0 := by
  show cauchyPowerSeries (fun z : ℂ => z) 0 1 0 (fun _ => (1 : ℂ)) = 0
  rw [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply]
  simp only [pow_zero, one_smul, Fin.prod_const]
  have hint : (∮ z in C(0, 1), (z - 0)⁻¹ • z)
      = ∮ z in C(0, 1), (1 : ℂ) :=
    circleIntegral.integral_congr zero_le_one fun z hz => by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      have hz0 : z ≠ 0 := by
        rintro rfl; simp at hz
      simp [smul_eq_mul, inv_mul_cancel₀ hz0]
  have hzero : (∮ z in C(0, 1), (1 : ℂ)) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt zero_le_one
      (fun z _ => (hasDerivAt_id z).hasDerivWithinAt)
  rw [hint, hzero, smul_zero]

/-- **K-B4-PROD-BOUNDARY, at full rank:** the coefficient-product
identity presented at the holomorphicity radius itself does
not follow from `DiscHolomorphic` at that radius. Witness:
`h z = z⁻¹` on `‖z‖ = 1`, `0` inside (holomorphic — indeed
zero — on the open unit disc), and `k z = z`. The product is
the B1c boundary witness, whose zeroth coefficient is `1`,
while the convolution's zeroth coefficient factors through
`discCoeff (fun z => z) 1 0 = 0`. -/
theorem discCoeff_mul_boundary_not :
    ¬ ∀ (h k : ℂ → ℂ) (R : ℝ), DiscHolomorphic h R → DiscHolomorphic k R →
      discCoeff (fun z => h z * k z) R
        = discConv (discCoeff h R) (discCoeff k R) := by
  intro hcontra
  set h : ℂ → ℂ := fun z => if ‖z‖ = 1 then z⁻¹ else 0 with hh_def
  have hh : DiscHolomorphic h 1 := by
    refine ⟨one_pos, ?_⟩
    refine (differentiableOn_const (0 : ℂ)).congr (fun z hz => ?_)
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    simp [hh_def, ne_of_lt hz]
  have hk : DiscHolomorphic (fun z : ℂ => z) 1 :=
    ⟨one_pos, differentiableOn_id⟩
  have hEq := hcontra h (fun z : ℂ => z) 1 hh hk
  have h0 := congrFun hEq 0
  have hprod_eq : (fun z => h z * z)
      = (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) := by
    funext z
    by_cases hz : ‖z‖ = 1
    · have hz0 : z ≠ 0 := by
        rintro rfl; simp at hz
      simp [hh_def, hz, inv_mul_cancel₀ hz0]
    · simp [hh_def, hz]
  have hLHS : discCoeff (fun z => h z * z) 1 0 = 1 := by
    rw [hprod_eq]
    exact discCoeff_boundary_counterexample
  have hRHS : discConv (discCoeff h 1) (discCoeff (fun z : ℂ => z) 1) 0
      = 0 := by
    rw [discConv]
    simp [discCoeff_id_zero]
  rw [hLHS] at h0
  rw [hRHS] at h0
  exact one_ne_zero h0

end

end ThetLogos
