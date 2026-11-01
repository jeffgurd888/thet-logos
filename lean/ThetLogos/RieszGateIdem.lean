/-
# GATE-A2 - Riesz projections: idempotence (SHELF gate, brick 2 of 2)

Brick GATE-A2 of the SHELF contour-gate line (scoping dossier
`whitepaper/shelf-contour-gate-scoping-2026-11-01.md` SS3/SS6,
pack `routeb-general-scratch/pack-gate-a2.md`): idempotence of the
single-circle Riesz projection of GATE-A1
(`ThetLogos.RieszGate`). NO CLAIM beyond the theorems below; no
dial is touched. This brick completes the minimal SHELF-8b gate:
a projection is its idempotence.

Route (the dossier's two-radii double integral): for
`0 < r1 < r2 <= R` under `specIsolatedWithin a lam R`, the product
`rieszProj a lam r1 * rieszProj a lam r2` is written as a double
circle integral of `resolvent a z * resolvent a w`; GATE-A1's first
resolvent identity splits the integrand as
`(w - z)⁻¹ • (resolvent a z - resolvent a w)`. The first piece is
evaluated in the inner (`w`) integral by
`circleIntegral.integral_sub_inv_of_mem_ball` (the point `z` lies
inside the outer circle), giving `(2 * pi * i) • resolvent a z`.
The second piece is swapped by Fubini
(`intervalIntegral_intervalIntegral_swap`, after unfolding both
circle integrals to interval integrals over the angle rectangle;
the joint integrand is continuous because the two circles are
disjoint and the resolvent is continuous on the outer circle),
and then its inner (`z`) integral vanishes by disc
Cauchy-Goursat (`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`),
the point `w` lying outside the inner disc. One integrability
point is worth recording: the outer function of the second piece
is circle-integrable because, pointwise on the inner circle, it
has the closed form `resolvent a z * ((2 * pi * i) • 1 - J2)`
( multiply the auxiliary identity
`(algebraMap z - a) * H z = (2 * pi * i) • 1 - J2`, proved by
pulling the constant `(algebraMap z - a)` through the outer
integral and using the pointwise identity
`(algebraMap z - a) * resolvent a w = 1 - (w - z) • resolvent a w`,
by `resolvent a z` on the left). The single-radius headline then
follows from the two-radii form at `r/2 < r` by GATE-A1's radius
independence. Every analytic step cites a lemma owned by the
pin or landed in GATE-A1; no step is asserted.
-/

import ThetLogos.RieszGate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral

open Real

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## Sphere bookkeeping for two distinct radii -/

/-- Points on two concentric spheres of distinct radii differ. -/
theorem ne_of_mem_sphere_of_lt {c z w : ℂ} {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere c r₁) (hw : w ∈ Metric.sphere c r₂)
    (h : r₁ < r₂) : w ≠ z := by
  intro hzw
  subst hzw
  rw [Metric.mem_sphere, dist_eq_norm] at hz hw
  rw [hz] at hw
  exact (ne_of_lt h) hw

/-- A point of the inner sphere lies in the open ball of the
outer radius. -/
theorem mem_ball_of_mem_sphere_of_lt {c z : ℂ} {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere c r₁) (h : r₁ < r₂) :
    z ∈ Metric.ball c r₂ := by
  rw [Metric.mem_sphere] at hz
  rw [Metric.mem_ball, hz]
  exact h

/-- A point of the inner sphere does not lie on the outer
sphere. -/
theorem not_mem_sphere_of_mem_sphere_of_lt {c z : ℂ} {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere c r₁) (h : r₁ < r₂) (hr₂ : 0 < r₂) :
    z ∉ Metric.sphere c |r₂| := by
  rw [abs_of_pos hr₂]
  exact fun hz2 => (ne_of_mem_sphere_of_lt hz hz2 h) rfl

/-! ## Resolvent-set and integrability facts on a sphere inside
the isolation radius (consuming GATE-A1's corrected
`circleIntegrable_resolvent_of_nonneg`) -/

theorem mem_resolventSet_of_sphere_of_isolated {lam : ℂ} {R r : ℝ}
    (hR : specIsolatedWithin a lam R) (hr : 0 < r) (hrR : r ≤ R)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r) : z ∈ resolventSet ℂ a := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  refine mem_resolventSet_of_specIsolatedWithin a hR (hz.le.trans hrR)
    (fun hzz => ?_)
  subst hzz
  rw [sub_self, norm_zero] at hz
  exact hr.ne' hz.symm

theorem circleIntegrable_resolvent_of_isolated {lam : ℂ} {R r : ℝ}
    (hR : specIsolatedWithin a lam R) (hr : 0 < r) (hrR : r ≤ R) :
    CircleIntegrable (resolvent a) lam r :=
  circleIntegrable_resolvent_of_nonneg a hr.le
    (fun z hz => mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz)

/-! ## Circle integrability of the kernel pieces -/

theorem circleIntegrable_inv_sub_smul_const {lam : ℂ} {r₁ r₂ : ℝ}
    {z : ℂ} (x : A) (hz : z ∈ Metric.sphere lam r₁) (h : r₁ < r₂)
    (hr₂ : 0 < r₂) :
    CircleIntegrable (fun w => (w - z)⁻¹ • x) lam r₂ := by
  have h := (circleIntegrable_const x lam r₂).sub_zpow_smul (-1 : ℤ)
    (not_mem_sphere_of_mem_sphere_of_lt hz h hr₂)
  simpa only [zpow_neg_one] using h

theorem circleIntegrable_inv_sub_smul_resolvent {lam : ℂ} {r₁ r₂ : ℝ}
    {z : ℂ} (hf : CircleIntegrable (resolvent a) lam r₂)
    (hz : z ∈ Metric.sphere lam r₁) (h : r₁ < r₂) (hr₂ : 0 < r₂) :
    CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w) lam r₂ := by
  have h := hf.sub_zpow_smul (-1 : ℤ)
    (not_mem_sphere_of_mem_sphere_of_lt hz h hr₂)
  simpa only [zpow_neg_one] using h

/-! ## The pointwise resolvent-identity split -/

theorem resolvent_mul_eq_inv_sub_smul_sub {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a)
    (hzw : w ≠ z) :
    resolvent a z * resolvent a w
      = (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
  have h := resolvent_sub_resolvent_eq a hz hw
  rw [h, inv_smul_smul₀ (sub_ne_zero.mpr hzw)]

/-- The pointwise identity behind the auxiliary closed form:
`(z - a) * R(w) = 1 - (w - z) • R(w)`. -/
theorem sub_a_mul_resolvent {z w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    (algebraMap ℂ A z - a) * resolvent a w
      = 1 - (w - z) • resolvent a w := by
  have h1 : (algebraMap ℂ A w - a) * resolvent a w = 1 := by
    have e : (algebraMap ℂ A w - a) * resolvent a w
        = ↑hw.unit * ↑hw.unit⁻¹ := by
      rw [spectrum.resolvent_eq hw, hw.unit_spec]
    rw [e]
    exact Units.mul_inv _
  have h2 : (algebraMap ℂ A z - algebraMap ℂ A w) * resolvent a w
      = (z - w) • resolvent a w := by
    rw [← map_sub, Algebra.smul_def]
  calc (algebraMap ℂ A z - a) * resolvent a w
      = (algebraMap ℂ A z - algebraMap ℂ A w) * resolvent a w
        + (algebraMap ℂ A w - a) * resolvent a w := by
        rw [← add_mul]
        congr 1
        abel
    _ = (z - w) • resolvent a w + 1 := by rw [h2, h1]
    _ = 1 - (w - z) • resolvent a w := by
        have h3 : (z - w) • resolvent a w = -((w - z) • resolvent a w) := by
          rw [show (z - w) = -(w - z) from (neg_sub w z).symm, neg_smul]
        rw [h3]
        exact (add_comm _ _).trans (sub_eq_add_neg (1 : A) _).symm

/-! ## Inner-integral evaluations -/

/-- Inner evaluation, first piece: for `z` inside the outer
circle, the `w`-integral of `(w - z)⁻¹ • x` is `(2 * pi * i) • x`
(the pin's `integral_sub_inv_of_mem_ball`). -/
theorem circleIntegral_inv_sub_smul_const {lam : ℂ} {r₂ : ℝ}
    {z : ℂ} (x : A) (hz : z ∈ Metric.ball lam r₂) :
    (∮ w in C(lam, r₂), (w - z)⁻¹ • x)
      = (2 * π * Complex.I : ℂ) • x := by
  rw [circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball hz]

/-- Disc Cauchy-Goursat for the kernel `(z - w)⁻¹ • x` with `w`
outside the closed disc. -/
theorem circleIntegral_sub_inv_smul_const_eq_zero {lam : ℂ} {r₁ : ℝ}
    (hr₁ : 0 ≤ r₁) {w : ℂ} (hw : w ∉ Metric.closedBall lam r₁)
    (x : A) :
    (∮ z in C(lam, r₁), (z - w)⁻¹ • x) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr₁ Set.countable_empty ?_ ?_
  · refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul
      continuousOn_const
    intro z hz
    show (z - w) ≠ 0
    rw [sub_ne_zero]
    intro hzw
    apply hw
    rw [← hzw]
    exact hz
  · intro z hz
    have hzw : z ≠ w := by
      intro h
      apply hw
      rw [← h]
      exact Metric.ball_subset_closedBall hz.1
    exact DifferentiableAt.smul_const
      (DifferentiableAt.inv (DifferentiableAt.sub_const differentiableAt_id w)
        (sub_ne_zero.mpr hzw)) x

/-- Inner evaluation, second piece after the swap: for `w` on
the outer sphere, the `z`-integral of `(w - z)⁻¹ • x` over the
inner circle vanishes. -/
theorem circleIntegral_inv_sub_smul_const_eq_zero {lam : ℂ}
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) {w : ℂ}
    (hw : w ∈ Metric.sphere lam r₂) (h : r₁ < r₂) (x : A) :
    (∮ z in C(lam, r₁), (w - z)⁻¹ • x) = 0 := by
  have hw' : ‖w - lam‖ = r₂ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hw
  have hwcb : w ∉ Metric.closedBall lam r₁ := by
    intro hwc
    rw [Metric.mem_closedBall, dist_eq_norm] at hwc
    exact (not_le_of_gt h) (hw' ▸ hwc)
  have hEq : (∮ z in C(lam, r₁), (w - z)⁻¹ • x)
      = ∮ z in C(lam, r₁), (-1 : ℂ) • ((z - w)⁻¹ • x) := by
    refine circleIntegral.integral_congr hr₁ (fun z _ => ?_)
    rw [smul_smul]
    congr 1
    rw [neg_mul, one_mul, ← inv_neg, neg_sub]
  rw [hEq, circleIntegral.integral_smul,
    circleIntegral_sub_inv_smul_const_eq_zero hr₁ hwcb x, smul_zero]

/-! ## The auxiliary closed form for the second piece -/

theorem sub_a_mul_circleIntegral_inv_sub_smul_resolvent {lam : ℂ}
    {R : ℝ} (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    (algebraMap ℂ A z - a)
        * (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      = (2 * π * Complex.I : ℂ) • (1 : A)
        - ∮ w in C(lam, r₂), resolvent a w := by
  have hf2 : CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w)
      lam r₂ :=
    circleIntegrable_inv_sub_smul_resolvent a
      (circleIntegrable_resolvent_of_isolated a hR hr₂ hr₂R) hz h12 hr₂
  have hf1 : CircleIntegrable (fun w => (w - z)⁻¹ • (1 : A)) lam r₂ :=
    circleIntegrable_inv_sub_smul_const (1 : A) hz h12 hr₂
  have hfR : CircleIntegrable (resolvent a) lam r₂ :=
    circleIntegrable_resolvent_of_isolated a hR hr₂ hr₂R
  calc (algebraMap ℂ A z - a)
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      = ∮ w in C(lam, r₂),
          (algebraMap ℂ A z - a) * ((w - z)⁻¹ • resolvent a w) :=
        const_mul_circleIntegral (algebraMap ℂ A z - a) hf2
    _ = ∮ w in C(lam, r₂), ((w - z)⁻¹ • (1 : A) - resolvent a w) := by
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        have hwres : w ∈ resolventSet ℂ a :=
          mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw
        have hzw : w ≠ z := ne_of_mem_sphere_of_lt hz hw h12
        rw [mul_smul_comm, sub_a_mul_resolvent a hwres, smul_sub,
          inv_smul_smul₀ (sub_ne_zero.mpr hzw)]
    _ = (∮ w in C(lam, r₂), (w - z)⁻¹ • (1 : A))
          - ∮ w in C(lam, r₂), resolvent a w :=
        circleIntegral.integral_sub hf1 hfR
    _ = (2 * π * Complex.I : ℂ) • (1 : A)
          - ∮ w in C(lam, r₂), resolvent a w := by
        rw [circleIntegral_inv_sub_smul_const (1 : A)
          (mem_ball_of_mem_sphere_of_lt hz h12)]

theorem circleIntegral_inv_sub_smul_resolvent_eq {lam : ℂ}
    {R : ℝ} (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      = resolvent a z * ((2 * π * Complex.I : ℂ) • (1 : A)
        - ∮ w in C(lam, r₂), resolvent a w) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hzres : z ∈ resolventSet ℂ a :=
    mem_resolventSet_of_sphere_of_isolated a hR hr₁
      (h12.le.trans hr₂R) hz
  have hstep := sub_a_mul_circleIntegral_inv_sub_smul_resolvent a hR
    hr₂ hr₂R h12 hz
  have hunit : resolvent a z * (algebraMap ℂ A z - a) = 1 := by
    have e : resolvent a z * (algebraMap ℂ A z - a)
        = ↑hzres.unit⁻¹ * ↑hzres.unit := by
      rw [spectrum.resolvent_eq hzres, hzres.unit_spec]
    rw [e]
    exact Units.inv_mul _
  calc (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      = (resolvent a z * (algebraMap ℂ A z - a))
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w) := by
        rw [hunit, one_mul]
    _ = resolvent a z * ((algebraMap ℂ A z - a)
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)) :=
        mul_assoc _ _ _
    _ = resolvent a z * ((2 * π * Complex.I : ℂ) • (1 : A)
          - ∮ w in C(lam, r₂), resolvent a w) := by
        rw [hstep]

/-- The outer function of the second piece is circle-integrable
on the inner circle: on that circle it agrees with the closed
form of the previous lemma. -/
theorem circleIntegrable_circleIntegral_inv_sub_smul_resolvent
    {lam : ℂ} {R : ℝ} (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      lam r₁ := by
  refine (circleIntegrable_congr (f₂ := fun z => resolvent a z
    * ((2 * π * Complex.I : ℂ) • (1 : A)
      - ∮ w in C(lam, r₂), resolvent a w)) ?_).mpr ?_
  · intro z hz
    rw [abs_of_pos hr₁] at hz
    exact circleIntegral_inv_sub_smul_resolvent_eq a hR hr₁ h12 hr₂R hz
  · refine ((continuousOn_resolvent a ?_).mul
      continuousOn_const).circleIntegrable hr₁.le
    intro z hz
    exact mem_resolventSet_of_sphere_of_isolated a hR hr₁
      (h12.le.trans hr₂R) hz

/-- The double integral of the first piece evaluates to
`(2 * pi * i)` times the inner resolvent integral. -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_self
    {lam : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a z)
      = (2 * π * Complex.I : ℂ)
        • ∮ z in C(lam, r₁), resolvent a z := by
  rw [← circleIntegral.integral_smul]
  refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
  exact circleIntegral_inv_sub_smul_const (resolvent a z)
    (mem_ball_of_mem_sphere_of_lt hz h12)

/-! ## The Fubini swap for the second piece -/

theorem continuous_resolvent_circleMap {lam : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ Metric.sphere lam r, z ∈ resolventSet ℂ a) :
    Continuous (fun θ => resolvent a (circleMap lam r θ)) :=
  (continuousOn_resolvent a h).comp_continuous (continuous_circleMap lam r)
    (fun θ => circleMap_mem_sphere lam hr θ)

theorem continuous_deriv_circleMap (c : ℂ) (R : ℝ) :
    Continuous (deriv (circleMap c R)) := by
  rw [funext (deriv_circleMap c R)]
  exact (continuous_circleMap 0 R).mul continuous_const

/-- The joint angle integrand of the second piece is
continuous on the whole angle plane: the two circles are
disjoint (distinct radii) and the resolvent is continuous at
every point of the outer circle. -/
theorem continuous_joint_kernel_resolvent {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    Continuous (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • resolvent a (circleMap lam r₂ p.2))) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hRcm : Continuous (fun θ => resolvent a (circleMap lam r₂ θ)) :=
    continuous_resolvent_circleMap a hr₂.le
      (fun z hz => mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hz)
  have hne : ∀ p : ℝ × ℝ,
      circleMap lam r₂ p.2 - circleMap lam r₁ p.1 ≠ 0 := by
    intro p
    exact sub_ne_zero.mpr (ne_of_mem_sphere_of_lt
      (circleMap_mem_sphere lam hr₁.le p.1)
      (circleMap_mem_sphere lam hr₂.le p.2) h12)
  have hd : Continuous (fun p : ℝ × ℝ =>
      deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) :=
    ((continuous_deriv_circleMap lam r₁).comp continuous_fst).mul
      ((continuous_deriv_circleMap lam r₂).comp continuous_snd)
  have hker : Continuous (fun p : ℝ × ℝ =>
      (circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
        • resolvent a (circleMap lam r₂ p.2)) :=
    ((((continuous_circleMap lam r₂).comp continuous_snd).sub
      ((continuous_circleMap lam r₁).comp continuous_fst)).inv₀ hne).smul
      (hRcm.comp continuous_snd)
  exact hd.smul hker

theorem integrableOn_joint_kernel_resolvent {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • resolvent a (circleMap lam r₂ p.2)))
      (Set.uIoc 0 (2 * π) ×ˢ Set.uIoc 0 (2 * π)) MeasureTheory.volume := by
  have hcont := continuous_joint_kernel_resolvent a hR hr₁ h12 hr₂R
  have hIcc : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • resolvent a (circleMap lam r₂ p.2)))
      (Set.Icc (0 : ℝ × ℝ) (2 * π, 2 * π)) MeasureTheory.volume :=
    hcont.integrableOn_Icc
  refine hIcc.mono_set ?_
  rw [Set.uIoc_of_le Real.two_pi_pos.le]
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨⟨hp1.1.le, hp2.1.le⟩, ⟨hp1.2, hp2.2⟩⟩

/-- The second piece's double integral as an iterated interval
integral over the angle rectangle (inner circle outer). -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_eq_interval
    {lam : ℂ} {r₁ r₂ : ℝ} :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
    = ∫ θ in 0..2 * π, ∫ φ in 0..2 * π,
        (deriv (circleMap lam r₁) θ * deriv (circleMap lam r₂) φ) •
          ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
            • resolvent a (circleMap lam r₂ φ)) := by
  show (∫ θ in 0..2 * π, deriv (circleMap lam r₁) θ
      • (∮ w in C(lam, r₂), (w - circleMap lam r₁ θ)⁻¹ • resolvent a w))
    = _
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  show deriv (circleMap lam r₁) θ
      • (∫ φ in 0..2 * π, deriv (circleMap lam r₂) φ
        • ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
          • resolvent a (circleMap lam r₂ φ)))
    = ∫ φ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun φ _ => smul_smul _ _ _)

/-- The second piece's double integral as an iterated interval
integral over the angle rectangle (outer circle outer). -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_swap_eq_interval
    {lam : ℂ} {r₁ r₂ : ℝ} :
    (∮ w in C(lam, r₂), ∮ z in C(lam, r₁), (w - z)⁻¹ • resolvent a w)
    = ∫ φ in 0..2 * π, ∫ θ in 0..2 * π,
        (deriv (circleMap lam r₁) θ * deriv (circleMap lam r₂) φ) •
          ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
            • resolvent a (circleMap lam r₂ φ)) := by
  show (∫ φ in 0..2 * π, deriv (circleMap lam r₂) φ
      • (∮ z in C(lam, r₁), (circleMap lam r₂ φ - z)⁻¹
        • resolvent a (circleMap lam r₂ φ)))
    = _
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  show deriv (circleMap lam r₂) φ
      • (∫ θ in 0..2 * π, deriv (circleMap lam r₁) θ
        • ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
          • resolvent a (circleMap lam r₂ φ)))
    = ∫ θ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [smul_smul, mul_comm (deriv (circleMap lam r₂) φ)
    (deriv (circleMap lam r₁) θ)]

/-- Fubini swap of the second piece's double circle integral
(the pin's `intervalIntegral_intervalIntegral_swap`). -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_swap
    {lam : ℂ} {R : ℝ} (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
    = ∮ w in C(lam, r₂), ∮ z in C(lam, r₁), (w - z)⁻¹ • resolvent a w := by
  rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_eq_interval,
    circleIntegral_circleIntegral_inv_sub_smul_resolvent_swap_eq_interval]
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap
    (integrableOn_joint_kernel_resolvent a hR hr₁ h12 hr₂R)

/-- The second piece's double integral vanishes: swap, then
evaluate the inner integral by disc Cauchy-Goursat. -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_eq_zero
    {lam : ℂ} {R : ℝ} (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      = 0 := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_swap a hR
    hr₁ h12 hr₂R]
  have h0 : (∮ w in C(lam, r₂), ∮ z in C(lam, r₁),
        (w - z)⁻¹ • resolvent a w)
      = ∮ w in C(lam, r₂), (0 : A) := by
    refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
    exact circleIntegral_inv_sub_smul_const_eq_zero hr₁.le hw h12
      (resolvent a w)
  rw [h0]
  show (∫ θ in 0..2 * π, deriv (circleMap lam r₂) θ • (0 : A)) = 0
  simp

/-! ## The product as a double integral, and its evaluation -/

theorem circleIntegral_mul_circleIntegral_resolvent {lam : ℂ}
    {r₁ r₂ : ℝ} (hf₁ : CircleIntegrable (resolvent a) lam r₁)
    (hf₂ : CircleIntegrable (resolvent a) lam r₂) (hr₁ : 0 ≤ r₁) :
    (∮ z in C(lam, r₁), resolvent a z)
        * (∮ w in C(lam, r₂), resolvent a w)
      = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          resolvent a z * resolvent a w := by
  rw [circleIntegral_mul_const (∮ w in C(lam, r₂), resolvent a w) hf₁]
  refine circleIntegral.integral_congr hr₁ (fun z _ => ?_)
  exact const_mul_circleIntegral (resolvent a z) hf₂

/-- The key computation: the product of the resolvent integrals
at two radii `r₁ < r₂` is `(2 * pi * i)` times the inner one. -/
theorem circleIntegral_resolvent_mul_eq {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), resolvent a z)
        * (∮ w in C(lam, r₂), resolvent a w)
      = (2 * π * Complex.I : ℂ)
        • ∮ z in C(lam, r₁), resolvent a z := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
  have hf₁ : CircleIntegrable (resolvent a) lam r₁ :=
    circleIntegrable_resolvent_of_isolated a hR hr₁ hr₁R
  have hf₂ : CircleIntegrable (resolvent a) lam r₂ :=
    circleIntegrable_resolvent_of_isolated a hR hr₂ hr₂R
  have hD1 : ∀ z ∈ Metric.sphere lam r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a z) lam r₂ :=
    fun z hz => circleIntegrable_inv_sub_smul_const (resolvent a z)
      hz h12 hr₂
  have hD2 : ∀ z ∈ Metric.sphere lam r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w) lam r₂ :=
    fun z hz => circleIntegrable_inv_sub_smul_resolvent a hf₂ hz h12 hr₂
  have hG1 : CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a z)
      lam r₁ := by
    refine (circleIntegrable_congr (f₂ := fun z =>
      (2 * π * Complex.I : ℂ) • resolvent a z) ?_).mpr ?_
    · intro z hz
      rw [abs_of_pos hr₁] at hz
      exact circleIntegral_inv_sub_smul_const (resolvent a z)
        (mem_ball_of_mem_sphere_of_lt hz h12)
    · refine (continuousOn_const.smul (continuousOn_resolvent a
        ?_)).circleIntegrable hr₁.le
      intro z hz
      exact mem_resolventSet_of_sphere_of_isolated a hR hr₁ hr₁R hz
  have hG2 : CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w)
      lam r₁ :=
    circleIntegrable_circleIntegral_inv_sub_smul_resolvent a hR hr₁
      h12 hr₂R
  calc (∮ z in C(lam, r₁), resolvent a z)
          * (∮ w in C(lam, r₂), resolvent a w)
      = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          resolvent a z * resolvent a w :=
        circleIntegral_mul_circleIntegral_resolvent a hf₁ hf₂ hr₁.le
    _ = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        exact resolvent_mul_eq_inv_sub_smul_sub a
          (mem_resolventSet_of_sphere_of_isolated a hR hr₁ hr₁R hz)
          (mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw)
          (ne_of_mem_sphere_of_lt hz hw h12)
    _ = ∮ z in C(lam, r₁), ((∮ w in C(lam, r₂),
            (w - z)⁻¹ • resolvent a z)
          - ∮ w in C(lam, r₂), (w - z)⁻¹ • resolvent a w) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        have hfun : (fun w => (w - z)⁻¹ • (resolvent a z - resolvent a w))
            = (fun w => (w - z)⁻¹ • resolvent a z)
              - (fun w => (w - z)⁻¹ • resolvent a w) :=
          funext fun w => smul_sub _ _ _
        rw [hfun]
        exact circleIntegral.integral_sub (hD1 z hz) (hD2 z hz)
    _ = (∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
            (w - z)⁻¹ • resolvent a z)
          - (∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
            (w - z)⁻¹ • resolvent a w) :=
        circleIntegral.integral_sub hG1 hG2
    _ = ((2 * π * Complex.I : ℂ)
            • ∮ z in C(lam, r₁), resolvent a z) - 0 := by
        rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_self
            a hr₁ h12,
          circleIntegral_circleIntegral_inv_sub_smul_resolvent_eq_zero
            a hR hr₁ h12 hr₂R]
    _ = (2 * π * Complex.I : ℂ)
          • ∮ z in C(lam, r₁), resolvent a z := sub_zero _

/-! ## Idempotence -/

/-- Two-radii idempotence: for `0 < r₁ < r₂ ≤ R` under
isolation, `P r₁ * P r₂ = P r₁`. -/
theorem rieszProj_mul_rieszProj_of_lt {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    rieszProj a lam r₁ * rieszProj a lam r₂ = rieszProj a lam r₁ := by
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJJ := circleIntegral_resolvent_mul_eq a hR hr₁ h12 hr₂R
  have hsc : (2 * π * Complex.I : ℂ)⁻¹ * (2 * π * Complex.I : ℂ)⁻¹
        * (2 * π * Complex.I : ℂ)
      = (2 * π * Complex.I : ℂ)⁻¹ := by
    have h1 : (2 * π * Complex.I : ℂ)⁻¹ * (2 * π * Complex.I : ℂ)
        = 1 := inv_mul_cancel₀ h2pi
    calc (2 * π * Complex.I : ℂ)⁻¹ * (2 * π * Complex.I : ℂ)⁻¹
          * (2 * π * Complex.I : ℂ)
        = (2 * π * Complex.I : ℂ)⁻¹
            * ((2 * π * Complex.I : ℂ)⁻¹
              * (2 * π * Complex.I : ℂ)) := mul_assoc _ _ _
      _ = (2 * π * Complex.I : ℂ)⁻¹ * 1 := by rw [h1]
      _ = (2 * π * Complex.I : ℂ)⁻¹ := mul_one _
  show ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ z in C(lam, r₁), resolvent a z)
      * ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ w in C(lam, r₂), resolvent a w)
    = (2 * π * Complex.I : ℂ)⁻¹
        • ∮ z in C(lam, r₁), resolvent a z
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hJJ, smul_smul, hsc]

/-- **Headline (GATE-A2): idempotence of the Riesz projection.**
Under `specIsolatedWithin a lam R`, for `0 < r ≤ R`,
`rieszProj a lam r * rieszProj a lam r = rieszProj a lam r`.
By the two-radii form at `r / 2 < r` and GATE-A1's radius
independence. -/
theorem rieszProj_mul_self {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r * rieszProj a lam r = rieszProj a lam r := by
  have hr2 : 0 < r / 2 := by linarith
  have hPeq : rieszProj a lam r = rieszProj a lam (r / 2) :=
    rieszProj_eq_of_le a hR hr hr2 hrR (by linarith)
  calc rieszProj a lam r * rieszProj a lam r
      = rieszProj a lam (r / 2) * rieszProj a lam r :=
        congrArg (· * rieszProj a lam r) hPeq
    _ = rieszProj a lam (r / 2) :=
        rieszProj_mul_rieszProj_of_lt a hR hr2 (by linarith) hrR
    _ = rieszProj a lam r := hPeq.symm

end

end ThetLogos
