/-
# GATE-A1 - Riesz projections: interface + first properties (SHELF gate)

Brick GATE-A1 of the SHELF contour-gate line (scoping dossier
`routeb-general-scratch/scoping-shelf-contour-gate-2026-11-01.md` SS6,
pack `routeb-general-scratch/pack-gate-a1.md`): the minimal gate for
SHELF-8b, Riesz projections for isolated spectral points of an element
of a complex Banach algebra. NO CLAIM beyond the theorems below; no
dial is touched. GATE-A2 (idempotence of the projection) is NOT in
this brick.

The two definitions are frozen verbatim from the dossier, as are the
headline statements, with ONE exception, flagged at full rank:

* Headline 4 (`circleIntegrable_resolvent`) as pinned is FALSE as
  stated. Its hypothesis quantifies over `Metric.sphere lam r`, which
  is empty for `r < 0`, so for negative `r` the hypothesis is vacuous
  while the conclusion asserts integrability on the geometric circle
  of radius `|r|`, where the resolvent can blow up non-integrably.
  Counterexample: `A = C`, `a = 1`, `lam = 0`, `r = -1`: the
  hypothesis is vacuous, but on `|z| = 1` the resolvent `(z - 1)^{-1}`
  blows up like `1/|theta - pi|`, which is not interval-integrable.
  What is landed instead is the corrected support
  `circleIntegrable_resolvent_of_nonneg` (same statement plus
  `0 <= r`), which is what headlines 5 and 7 consume (their radii
  are positive). The frozen form is NOT silently weakened: it is
  absent, and this note is the record.

Everything else is landed as pinned: the first resolvent identity,
resolvent commutation, commutation of `a` with its resolvent, radius
independence of the Riesz projection under isolation (the annulus
Cauchy-Goursat step, owned by the pin in
`Mathlib/Analysis/Complex/CauchyIntegral.lean`), commutation of `a`
with the projection, and non-vanishing of the projection under
isolation (by the contrapositive argument of the dossier: if the
projection were `0`, the auxiliary integral of
`(z - lam)^{-1} • resolvent a z` would exhibit `algebraMap C A lam - a`
as a unit, contradicting `lam \in spectrum C a`).
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

open Real

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

/-! ## Frozen definitions (verbatim from the dossier) -/

/-- The Riesz projection of `a` at the spectral point `lam`, defined
as the normalized circle integral of the resolvent over the circle of
radius `r` around `lam`. -/
def rieszProj (a : A) (lam : ℂ) (r : ℝ) : A :=
  (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z

/-- Quantitative isolation of the spectral point `lam`: `lam` is in
the spectrum, and every other spectral point is at distance `> R`
from `lam`. -/
def specIsolatedWithin (a : A) (lam : ℂ) (R : ℝ) : Prop :=
  lam ∈ spectrum ℂ a ∧
    ∀ z ∈ spectrum ℂ a, z ≠ lam → R < ‖z - lam‖

variable (a : A)

/-! ## Support: points within the isolation radius lie in the
resolvent set -/

theorem mem_resolventSet_of_specIsolatedWithin {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {z : ℂ} (hzR : ‖z - lam‖ ≤ R)
    (hz : z ≠ lam) : z ∈ resolventSet ℂ a := by
  obtain ⟨-, hiso⟩ := hR
  by_contra hcon
  have hzspec : z ∈ spectrum ℂ a := hcon
  exact absurd (hiso z hzspec hz) (not_lt_of_ge hzR)

/-! ## Headline 1: the first resolvent identity -/

theorem resolvent_sub_resolvent_eq {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    resolvent a z - resolvent a w
      = (w - z) • (resolvent a z * resolvent a w) := by
  rw [spectrum.resolvent_eq hz, spectrum.resolvent_eq hw, Algebra.smul_def,
    map_sub]
  have hdiff : algebraMap ℂ A w - algebraMap ℂ A z
      = (↑hw.unit : A) - ↑hz.unit := by
    rw [hz.unit_spec, hw.unit_spec]; abel
  have hcomm : (algebraMap ℂ A w - algebraMap ℂ A z) * (↑hz.unit⁻¹ : A)
      = (↑hz.unit⁻¹ : A) * (algebraMap ℂ A w - algebraMap ℂ A z) := by
    rw [← map_sub]; exact Algebra.commutes (w - z) (↑hz.unit⁻¹ : A)
  rw [← mul_assoc, hcomm, hdiff, mul_sub, Units.inv_mul, sub_mul, mul_assoc,
    Units.mul_inv, mul_one, one_mul]

/-! ## Headline 3 (proved before headline 2's corollaries use the
same units machinery): `a` commutes with its resolvent -/

theorem commute_a_resolvent {z : ℂ}
    (hz : z ∈ resolventSet ℂ a) : Commute a (resolvent a z) := by
  have h : Commute a (↑hz.unit : A) := by
    rw [hz.unit_spec]
    exact Commute.sub_right (Commute.symm (Algebra.commutes z a))
      (Commute.refl a)
  rw [spectrum.resolvent_eq hz]
  exact Commute.units_inv_right h

/-! ## Headline 2: resolvents commute -/

theorem commute_resolvent_resolvent {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    Commute (resolvent a z) (resolvent a w) := by
  have hUV : Commute (↑hz.unit : A) (↑hw.unit : A) := by
    rw [hz.unit_spec, hw.unit_spec]
    exact Commute.sub_left (Algebra.commutes z (algebraMap ℂ A w - a))
      (Commute.sub_right (Commute.symm (Algebra.commutes w a)) (Commute.refl a))
  rw [spectrum.resolvent_eq hz, spectrum.resolvent_eq hw]
  exact Commute.units_inv_right (Commute.units_inv_left hUV)

/-! ## Headline 4 (corrected support form; see the header note):
circle integrability of the resolvent -/

theorem continuousOn_resolvent {s : Set ℂ} (hs : s ⊆ resolventSet ℂ a) :
    ContinuousOn (resolvent a) s := by
  have hd : DifferentiableOn ℂ (resolvent a) s :=
    fun z hz =>
      (spectrum.hasDerivAt_resolvent_const_left (hs hz)).differentiableAt
        |>.differentiableWithinAt
  exact DifferentiableOn.continuousOn hd

theorem circleIntegrable_resolvent_of_nonneg {lam : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ Metric.sphere lam r, z ∈ resolventSet ℂ a) :
    CircleIntegrable (resolvent a) lam r :=
  (continuousOn_resolvent a (fun z hz => h z hz)).circleIntegrable hr

/-! ## Support: `a` commutes with the resolvent everywhere (at
spectral points the resolvent is `0`) -/

theorem commute_a_resolvent_all {z : ℂ} : Commute a (resolvent a z) := by
  by_cases hz : z ∈ resolventSet ℂ a
  · exact commute_a_resolvent a hz
  · have hz' : z ∈ spectrum ℂ a := hz
    rw [spectrum.resolvent_zero_of_mem_spectrum hz']
    show a * 0 = 0 * a
    rw [mul_zero, zero_mul]

/-! ## Support: constant factors pull through circle integrals -/

theorem const_mul_circleIntegral (b : A) {f : ℂ → A} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    b * (∮ z in C(c, R), f z) = ∮ z in C(c, R), b * f z := by
  have hL := (ContinuousLinearMap.mul ℂ A b).intervalIntegral_comp_comm hf.out
  show (ContinuousLinearMap.mul ℂ A b)
      (∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ))
    = ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • (b * f (circleMap c R θ))
  rw [← hL]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [ContinuousLinearMap.mul_apply', mul_smul_comm]

theorem circleIntegral_mul_const (b : A) {f : ℂ → A} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) * b = ∮ z in C(c, R), f z * b := by
  have hL := ((ContinuousLinearMap.mul ℂ A).flip b).intervalIntegral_comp_comm
    hf.out
  show ((ContinuousLinearMap.mul ℂ A).flip b)
      (∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ))
    = ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • (f (circleMap c R θ) * b)
  rw [← hL]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    smul_mul_assoc]

/-! ## Headline 5: radius independence under isolation -/

theorem circleIntegral_resolvent_eq_of_isolated {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∮ z in C(lam, R), resolvent a z) = ∮ z in C(lam, r), resolvent a z := by
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty ?_ ?_
  · refine continuousOn_resolvent a (fun z hz => ?_)
    obtain ⟨hz1, hz2⟩ := hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz1
    refine mem_resolventSet_of_specIsolatedWithin a hR hz1 (fun hzz => ?_)
    subst hzz
    exact hz2 (Metric.mem_ball_self hr)
  · intro z hz
    obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz1
    have hzmem : z ∈ resolventSet ℂ a :=
      mem_resolventSet_of_specIsolatedWithin a hR hz1.le (fun hzz => by
        subst hzz
        exact hz2 (Metric.mem_closedBall_self hr.le))
    exact (spectrum.hasDerivAt_resolvent_const_left hzmem).differentiableAt

theorem rieszProj_eq_of_le {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ R) (h₂ : r₂ ≤ R) :
    rieszProj a lam r₁ = rieszProj a lam r₂ := by
  have e1 := circleIntegral_resolvent_eq_of_isolated a hR hr₁ h₁
  have e2 := circleIntegral_resolvent_eq_of_isolated a hR hr₂ h₂
  show (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r₁), resolvent a z)
    = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r₂), resolvent a z)
  rw [← e1, ← e2]

/-! ## Headline 6: `a` commutes with the Riesz projection -/

theorem commute_a_rieszProj (lam : ℂ) (r : ℝ) :
    Commute a (rieszProj a lam r) := by
  by_cases hf : CircleIntegrable (resolvent a) lam r
  · have hJ : a * (∮ z in C(lam, r), resolvent a z)
        = (∮ z in C(lam, r), resolvent a z) * a := by
      rw [const_mul_circleIntegral a hf, circleIntegral_mul_const a hf]
      show (∫ θ : ℝ in 0..2 * π,
          deriv (circleMap lam r) θ • (a * resolvent a (circleMap lam r θ)))
        = ∫ θ : ℝ in 0..2 * π,
          deriv (circleMap lam r) θ • (resolvent a (circleMap lam r θ) * a)
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      exact congrArg _ (Commute.eq (commute_a_resolvent_all a))
    show a * ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z) * a
    rw [mul_smul_comm, smul_mul_assoc, hJ]
  · show a * ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z) * a
    rw [circleIntegral.integral_undef hf, smul_zero, mul_zero, zero_mul]

/-! ## Headline 7: the projection is nonzero under isolation -/

theorem rieszProj_ne_zero {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r ≠ 0 := by
  have hRcopy := hR
  obtain ⟨hlam, -⟩ := hRcopy
  intro hP
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsphere : ∀ z ∈ Metric.sphere lam r, z ∈ resolventSet ℂ a := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    refine mem_resolventSet_of_specIsolatedWithin a hR (hz.le.trans hrR)
      (fun hzz => ?_)
    subst hzz
    rw [sub_self, norm_zero] at hz
    exact hr.ne' hz.symm
  have hfR : CircleIntegrable (resolvent a) lam r :=
    circleIntegrable_resolvent_of_nonneg a hr.le hsphere
  have hnotmem : lam ∉ Metric.sphere lam |r| := by
    rw [Metric.mem_sphere, dist_self, abs_of_pos hr]
    exact ne_of_lt hr
  have hfAux : CircleIntegrable
      (fun z => (z - lam)⁻¹ • resolvent a z) lam r := by
    have h := hfR.sub_zpow_smul (-1 : ℤ) hnotmem
    simpa only [zpow_neg_one] using h
  have hfConst : CircleIntegrable
      (fun z => (z - lam)⁻¹ • (1 : A)) lam r := by
    have h := (circleIntegrable_const (1 : A) lam r).sub_zpow_smul (-1 : ℤ)
      hnotmem
    simpa only [zpow_neg_one] using h
  -- The pointwise identity behind both auxiliary computations.
  have key : ∀ z ∈ Metric.sphere lam r,
      (algebraMap ℂ A lam - a) * resolvent a z
        = 1 - (z - lam) • resolvent a z := by
    intro z hz
    have hzR : z ∈ resolventSet ℂ a := hsphere z hz
    have h1 : (algebraMap ℂ A z - a) * resolvent a z = 1 := by
      have e : (algebraMap ℂ A z - a) * resolvent a z
          = ↑hzR.unit * ↑hzR.unit⁻¹ := by
        rw [spectrum.resolvent_eq hzR, hzR.unit_spec]
      rw [e]; exact Units.mul_inv _
    have h2 : (algebraMap ℂ A lam - algebraMap ℂ A z) * resolvent a z
        = -((z - lam) • resolvent a z) := by
      have e1 : algebraMap ℂ A lam - algebraMap ℂ A z
          = -algebraMap ℂ A (z - lam) := by
        rw [← map_sub, ← neg_sub z lam, map_neg]
      rw [e1, Algebra.smul_def, neg_mul]
    calc (algebraMap ℂ A lam - a) * resolvent a z
        = (algebraMap ℂ A lam - algebraMap ℂ A z) * resolvent a z
          + (algebraMap ℂ A z - a) * resolvent a z := by
          rw [← add_mul]; congr 1; abel
      _ = 1 - (z - lam) • resolvent a z := by rw [h2, h1]; abel
  have heqL : Set.EqOn
      (fun z => (algebraMap ℂ A lam - a) * ((z - lam)⁻¹ • resolvent a z))
      (fun z => (z - lam)⁻¹ • (1 : A) - resolvent a z)
      (Metric.sphere lam r) := by
    intro z hz
    have hzne : z ≠ lam := by
      intro hzz
      rw [Metric.mem_sphere, dist_eq_norm, hzz, sub_self, norm_zero] at hz
      exact hr.ne' hz.symm
    show (algebraMap ℂ A lam - a) * ((z - lam)⁻¹ • resolvent a z)
      = (z - lam)⁻¹ • (1 : A) - resolvent a z
    rw [mul_smul_comm, key z hz, smul_sub, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hzne), one_smul]
  have heqR : Set.EqOn
      (fun z => ((z - lam)⁻¹ • resolvent a z) * (algebraMap ℂ A lam - a))
      (fun z => (z - lam)⁻¹ • (1 : A) - resolvent a z)
      (Metric.sphere lam r) := by
    intro z hz
    have hcomm : Commute (algebraMap ℂ A lam - a) (resolvent a z) :=
      Commute.sub_left (Algebra.commutes lam (resolvent a z))
        (commute_a_resolvent_all a)
    show ((z - lam)⁻¹ • resolvent a z) * (algebraMap ℂ A lam - a)
      = (z - lam)⁻¹ • (1 : A) - resolvent a z
    rw [smul_mul_assoc, ← Commute.eq hcomm, ← mul_smul_comm]
    exact heqL hz
  have hJeq : (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
    show (∮ z in C(lam, r), resolvent a z)
      = (2 * π * Complex.I : ℂ)
        • ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
    rw [smul_inv_smul₀ h2pi]
  have hAuxL : (algebraMap ℂ A lam - a)
      * (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
      = (2 * π * Complex.I : ℂ) • (1 : A) := by
    calc (algebraMap ℂ A lam - a)
          * (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
        = ∮ z in C(lam, r),
            (algebraMap ℂ A lam - a) * ((z - lam)⁻¹ • resolvent a z) :=
          const_mul_circleIntegral (algebraMap ℂ A lam - a) hfAux
      _ = ∮ z in C(lam, r), ((z - lam)⁻¹ • (1 : A) - resolvent a z) :=
          circleIntegral.integral_congr hr.le heqL
      _ = (∮ z in C(lam, r), (z - lam)⁻¹ • (1 : A))
          - ∮ z in C(lam, r), resolvent a z :=
          circleIntegral.integral_sub hfConst hfR
      _ = (2 * π * Complex.I : ℂ) • (1 : A)
          - (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
          rw [circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (Metric.mem_ball_self hr), hJeq]
      _ = (2 * π * Complex.I : ℂ) • (1 : A) := by
          rw [hP, smul_zero, sub_zero]
  have hAuxR : (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
        * (algebraMap ℂ A lam - a)
      = (2 * π * Complex.I : ℂ) • (1 : A) := by
    calc (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z)
          * (algebraMap ℂ A lam - a)
        = ∮ z in C(lam, r),
            ((z - lam)⁻¹ • resolvent a z) * (algebraMap ℂ A lam - a) :=
          circleIntegral_mul_const (algebraMap ℂ A lam - a) hfAux
      _ = ∮ z in C(lam, r), ((z - lam)⁻¹ • (1 : A) - resolvent a z) :=
          circleIntegral.integral_congr hr.le heqR
      _ = (∮ z in C(lam, r), (z - lam)⁻¹ • (1 : A))
          - ∮ z in C(lam, r), resolvent a z :=
          circleIntegral.integral_sub hfConst hfR
      _ = (2 * π * Complex.I : ℂ) • (1 : A)
          - (2 * π * Complex.I : ℂ) • rieszProj a lam r := by
          rw [circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (Metric.mem_ball_self hr), hJeq]
      _ = (2 * π * Complex.I : ℂ) • (1 : A) := by
          rw [hP, smul_zero, sub_zero]
  have hunit : IsUnit (algebraMap ℂ A lam - a) := by
    refine ⟨⟨algebraMap ℂ A lam - a,
      (2 * π * Complex.I : ℂ)⁻¹
        • (∮ z in C(lam, r), (z - lam)⁻¹ • resolvent a z), ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, hAuxL, smul_smul, inv_mul_cancel₀ h2pi, one_smul]
    · rw [smul_mul_assoc, hAuxR, smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  exact spectrum.mem_iff.mp hlam hunit

end

end ThetLogos
