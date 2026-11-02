/-
# SHELF-8b, brick 2 (8B-2) - two-point Riesz orthogonality

Brick 8B-2 of SHELF-8b (scoping dossier
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS2/SS3, seam
S-8B-2, pack `routeb-general-scratch/pack-8b-2.md`): for two
distinct isolated spectral points with disjoint separating
discs, the Riesz projections of GATE-A1/GATE-A2
(`ThetLogos.RieszGate`, `ThetLogos.RieszGateIdem`) are
orthogonal. NO CLAIM beyond the theorems below; no dial is
touched. 8b is not 7b's general contour calculus.
K-8B-KILLED-FORM binds: nothing here consumes the killed
`circleIntegrable_resolvent`; the only integrability forms
used are the corrected
`circleIntegrable_resolvent_of_nonneg` (via GATE-A2's
`circleIntegrable_resolvent_of_isolated`) and `sub_zpow_smul`
descendants of it carrying the separation hypothesis on
their face.

Engine (the scoping's): GATE-A2's two-radii double-integral
pattern with two centres. The product is a double circle
integral of `resolvent a z * resolvent a w`; GATE-A1's first
resolvent identity splits the integrand as
`(w - z)⁻¹ • (resolvent a z - resolvent a w)`. Now BOTH
pieces vanish (contrast A2, where exactly one residue
survived): the first piece's inner (`w`) integral vanishes
by disc Cauchy-Goursat, since for `z` on the first circle
the pole `z` lies outside the closed second disc
(`‖z - lam₂‖ ≥ ‖lam₂ - lam₁‖ - r₁ > r₂`); the second piece
is swapped by Fubini (the joint angle integrand is
continuous because the circles are disjoint by the
separation grade `r₁ + r₂ < ‖lam₂ - lam₁‖` and the
resolvent is continuous on the second circle), and then
its inner (`z`) integral vanishes by disc Cauchy-Goursat,
the pole `w` lying outside the closed first disc. The
outer integrability of the second piece is obtained from
the two-centre auxiliary closed form
`H z = resolvent a z * (-∮ w in C(lam₂, r₂), resolvent a w)`:
multiplying `H z` by `algebraMap z - a` kills the kernel
piece by the same outside-the-disc vanishing (not by a
residue - contrast A2's `(2 * pi * i) • 1 - J₂`), leaving
`-∮ resolvent`. Every analytic step cites a lemma owned by
the pin or landed in GATE-A1/GATE-A2.
-/

import ThetLogos.RieszGateIdem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral

open Real

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

variable (a : A)

/-! ## Separation bookkeeping for two distinct centres -/

/-- The centres' distance is bounded by the cross distance
plus the two radii: `lam₂ - lam₁ = (lam₂ - w) + (w - z) +
(z - lam₁)`. -/
theorem norm_sub_le_add_of_mem_spheres_sep {lam₁ lam₂ z w : ℂ}
    {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere lam₁ r₁) (hw : w ∈ Metric.sphere lam₂ r₂) :
    ‖lam₂ - lam₁‖ ≤ ‖w - z‖ + (r₁ + r₂) := by
  have hz1 : ‖z - lam₁‖ = r₁ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  have hw2 : ‖w - lam₂‖ = r₂ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hw
  have key : lam₂ - lam₁ = (lam₂ - w) + (w - z) + (z - lam₁) := by abel
  have htri : ‖lam₂ - lam₁‖
      ≤ ‖lam₂ - w‖ + ‖w - z‖ + ‖z - lam₁‖ := by
    rw [key]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_sub_rev lam₂ w, hw2, hz1] at htri
  linarith

/-- Points on two separated spheres differ. -/
theorem ne_of_mem_spheres_sep {lam₁ lam₂ z w : ℂ} {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere lam₁ r₁) (hw : w ∈ Metric.sphere lam₂ r₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) : w ≠ z := by
  intro hzw
  have hle := norm_sub_le_add_of_mem_spheres_sep hz hw
  rw [← hzw, sub_self, norm_zero, zero_add] at hle
  exact (not_lt_of_ge hle) hsep

/-- A point of the first sphere lies outside the closed
second disc: `lam₂ - lam₁ = (lam₂ - z) + (z - lam₁)`. -/
theorem not_mem_closedBall_two_of_mem_sphere_sep {lam₁ lam₂ z : ℂ}
    {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere lam₁ r₁)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    z ∉ Metric.closedBall lam₂ r₂ := by
  have hz1 : ‖z - lam₁‖ = r₁ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  intro hc
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  have key : lam₂ - lam₁ = (lam₂ - z) + (z - lam₁) := by abel
  have htri : ‖lam₂ - lam₁‖ ≤ ‖lam₂ - z‖ + ‖z - lam₁‖ := by
    rw [key]
    exact norm_add_le _ _
  rw [norm_sub_rev lam₂ z, hz1] at htri
  linarith

/-- A point of the second sphere lies outside the closed
first disc: `lam₂ - lam₁ = (lam₂ - w) + (w - lam₁)`. -/
theorem not_mem_closedBall_one_of_mem_sphere_sep {lam₁ lam₂ w : ℂ}
    {r₁ r₂ : ℝ}
    (hw : w ∈ Metric.sphere lam₂ r₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    w ∉ Metric.closedBall lam₁ r₁ := by
  have hw2 : ‖w - lam₂‖ = r₂ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hw
  intro hc
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  have key : lam₂ - lam₁ = (lam₂ - w) + (w - lam₁) := by abel
  have htri : ‖lam₂ - lam₁‖ ≤ ‖lam₂ - w‖ + ‖w - lam₁‖ := by
    rw [key]
    exact norm_add_le _ _
  rw [norm_sub_rev lam₂ w, hw2] at htri
  linarith

/-- A point of the first sphere does not lie on the second
sphere (the `sub_zpow_smul` side condition, two-centre
form). -/
theorem not_mem_sphere_two_of_mem_sphere_sep {lam₁ lam₂ z : ℂ}
    {r₁ r₂ : ℝ}
    (hz : z ∈ Metric.sphere lam₁ r₁)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₂ : 0 < r₂) :
    z ∉ Metric.sphere lam₂ |r₂| := by
  rw [abs_of_pos hr₂]
  intro hs
  apply not_mem_closedBall_two_of_mem_sphere_sep hz hsep
  rw [Metric.mem_closedBall]
  exact le_of_eq (Metric.mem_sphere.mp hs)

/-- A point of the second sphere does not lie on the first
sphere. -/
theorem not_mem_sphere_one_of_mem_sphere_sep {lam₁ lam₂ w : ℂ}
    {r₁ r₂ : ℝ}
    (hw : w ∈ Metric.sphere lam₂ r₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₁ : 0 < r₁) :
    w ∉ Metric.sphere lam₁ |r₁| := by
  rw [abs_of_pos hr₁]
  intro hs
  apply not_mem_closedBall_one_of_mem_sphere_sep hw hsep
  rw [Metric.mem_closedBall]
  exact le_of_eq (Metric.mem_sphere.mp hs)

/-! ## Circle integrability of the kernel pieces (two centres) -/

theorem circleIntegrable_inv_sub_smul_const_sep {lam₁ lam₂ : ℂ}
    {r₁ r₂ : ℝ} {z : ℂ} (x : A)
    (hz : z ∈ Metric.sphere lam₁ r₁)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₂ : 0 < r₂) :
    CircleIntegrable (fun w => (w - z)⁻¹ • x) lam₂ r₂ := by
  have h := (circleIntegrable_const x lam₂ r₂).sub_zpow_smul (-1 : ℤ)
    (not_mem_sphere_two_of_mem_sphere_sep hz hsep hr₂)
  simpa only [zpow_neg_one] using h

theorem circleIntegrable_inv_sub_smul_resolvent_sep {lam₁ lam₂ : ℂ}
    {r₁ r₂ : ℝ} {z : ℂ}
    (hf : CircleIntegrable (resolvent a) lam₂ r₂)
    (hz : z ∈ Metric.sphere lam₁ r₁)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₂ : 0 < r₂) :
    CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w) lam₂ r₂ := by
  have h := hf.sub_zpow_smul (-1 : ℤ)
    (not_mem_sphere_two_of_mem_sphere_sep hz hsep hr₂)
  simpa only [zpow_neg_one] using h

/-! ## Inner-integral evaluations: both vanish -/

/-- First piece, inner evaluation: for `z` on the first
circle, the `w`-integral of `(w - z)⁻¹ • x` over the second
circle vanishes - the pole `z` lies outside the closed
second disc, so disc Cauchy-Goursat (GATE-A2's
`circleIntegral_sub_inv_smul_const_eq_zero`) applies. -/
theorem circleIntegral_inv_sub_smul_const_sep_eq_zero {lam₁ lam₂ : ℂ}
    {r₁ r₂ : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere lam₁ r₁)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₂ : 0 < r₂) (x : A) :
    (∮ w in C(lam₂, r₂), (w - z)⁻¹ • x) = 0 :=
  circleIntegral_sub_inv_smul_const_eq_zero hr₂.le
    (not_mem_closedBall_two_of_mem_sphere_sep hz hsep) x

/-- Second piece after the swap, inner evaluation: for `w`
on the second circle, the `z`-integral of `(w - z)⁻¹ • x`
over the first circle vanishes - the pole `w` lies outside
the closed first disc. -/
theorem circleIntegral_inv_sub_smul_const_sep_swap_eq_zero
    {lam₁ lam₂ : ℂ} {r₁ r₂ : ℝ} {w : ℂ}
    (hw : w ∈ Metric.sphere lam₂ r₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) (hr₁ : 0 < r₁) (x : A) :
    (∮ z in C(lam₁, r₁), (w - z)⁻¹ • x) = 0 := by
  have hwcb : w ∉ Metric.closedBall lam₁ r₁ :=
    not_mem_closedBall_one_of_mem_sphere_sep hw hsep
  have hEq : (∮ z in C(lam₁, r₁), (w - z)⁻¹ • x)
      = ∮ z in C(lam₁, r₁), (-1 : ℂ) • ((z - w)⁻¹ • x) := by
    refine circleIntegral.integral_congr hr₁.le (fun z _ => ?_)
    rw [smul_smul]
    congr 1
    rw [neg_mul, one_mul, ← inv_neg, neg_sub]
  rw [hEq, circleIntegral.integral_smul,
    circleIntegral_sub_inv_smul_const_eq_zero hr₁.le hwcb x, smul_zero]

/-! ## The auxiliary closed form for the second piece -/

/-- Two-centre auxiliary identity: multiplying the second
piece's outer function by `algebraMap z - a` leaves
`-∮ resolvent` over the second circle - the kernel term
vanishes because `z` lies outside the second disc (in A2's
concentric case it contributed `(2 * pi * i) • 1`). -/
theorem sub_a_mul_circleIntegral_inv_sub_smul_resolvent_sep
    {lam₁ lam₂ : ℂ} {R₂ : ℝ}
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖)
    {z : ℂ} (hz : z ∈ Metric.sphere lam₁ r₁) :
    (algebraMap ℂ A z - a)
        * (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      = - ∮ w in C(lam₂, r₂), resolvent a w := by
  have hf2 : CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w)
      lam₂ r₂ :=
    circleIntegrable_inv_sub_smul_resolvent_sep a
      (circleIntegrable_resolvent_of_isolated a h₂ hr₂ hr₂R) hz hsep hr₂
  have hf1 : CircleIntegrable (fun w => (w - z)⁻¹ • (1 : A)) lam₂ r₂ :=
    circleIntegrable_inv_sub_smul_const_sep (1 : A) hz hsep hr₂
  have hfR : CircleIntegrable (resolvent a) lam₂ r₂ :=
    circleIntegrable_resolvent_of_isolated a h₂ hr₂ hr₂R
  calc (algebraMap ℂ A z - a)
          * (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      = ∮ w in C(lam₂, r₂),
          (algebraMap ℂ A z - a) * ((w - z)⁻¹ • resolvent a w) :=
        const_mul_circleIntegral (algebraMap ℂ A z - a) hf2
    _ = ∮ w in C(lam₂, r₂), ((w - z)⁻¹ • (1 : A) - resolvent a w) := by
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        have hwres : w ∈ resolventSet ℂ a :=
          mem_resolventSet_of_sphere_of_isolated a h₂ hr₂ hr₂R hw
        have hzw : w ≠ z := ne_of_mem_spheres_sep hz hw hsep
        rw [mul_smul_comm, sub_a_mul_resolvent a hwres, smul_sub,
          inv_smul_smul₀ (sub_ne_zero.mpr hzw)]
    _ = (∮ w in C(lam₂, r₂), (w - z)⁻¹ • (1 : A))
          - ∮ w in C(lam₂, r₂), resolvent a w :=
        circleIntegral.integral_sub hf1 hfR
    _ = - ∮ w in C(lam₂, r₂), resolvent a w := by
        rw [circleIntegral_inv_sub_smul_const_sep_eq_zero hz hsep hr₂
          (1 : A), zero_sub]

/-- Closed form of the second piece's outer function on the
first circle. -/
theorem circleIntegral_inv_sub_smul_resolvent_sep_eq {lam₁ lam₂ : ℂ}
    {R₁ R₂ : ℝ} (h₁ : specIsolatedWithin a lam₁ R₁)
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁R : r₁ ≤ R₁) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖)
    {z : ℂ} (hz : z ∈ Metric.sphere lam₁ r₁) :
    (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      = resolvent a z * (- ∮ w in C(lam₂, r₂), resolvent a w) := by
  have hzres : z ∈ resolventSet ℂ a :=
    mem_resolventSet_of_sphere_of_isolated a h₁ hr₁ hr₁R hz
  have hstep := sub_a_mul_circleIntegral_inv_sub_smul_resolvent_sep a h₂
    hr₂ hr₂R hsep hz
  have hunit : resolvent a z * (algebraMap ℂ A z - a) = 1 := by
    have e : resolvent a z * (algebraMap ℂ A z - a)
        = ↑hzres.unit⁻¹ * ↑hzres.unit := by
      rw [spectrum.resolvent_eq hzres, hzres.unit_spec]
    rw [e]
    exact Units.inv_mul _
  calc (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      = (resolvent a z * (algebraMap ℂ A z - a))
          * (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w) := by
        rw [hunit, one_mul]
    _ = resolvent a z * ((algebraMap ℂ A z - a)
          * (∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)) :=
        mul_assoc _ _ _
    _ = resolvent a z * (- ∮ w in C(lam₂, r₂), resolvent a w) := by
        rw [hstep]

/-- The outer function of the second piece is
circle-integrable on the first circle: on that circle it
agrees with the closed form of the previous lemma. -/
theorem circleIntegrable_circleIntegral_inv_sub_smul_resolvent_sep
    {lam₁ lam₂ : ℂ} {R₁ R₂ : ℝ}
    (h₁ : specIsolatedWithin a lam₁ R₁)
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁R : r₁ ≤ R₁) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    CircleIntegrable
      (fun z => ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      lam₁ r₁ := by
  refine (circleIntegrable_congr (f₂ := fun z => resolvent a z
    * (- ∮ w in C(lam₂, r₂), resolvent a w)) ?_).mpr ?_
  · intro z hz
    rw [abs_of_pos hr₁] at hz
    exact circleIntegral_inv_sub_smul_resolvent_sep_eq a h₁ h₂ hr₁ hr₂
      hr₁R hr₂R hsep hz
  · refine ((continuousOn_resolvent a ?_).mul
      continuousOn_const).circleIntegrable hr₁.le
    intro z hz
    exact mem_resolventSet_of_sphere_of_isolated a h₁ hr₁ hr₁R hz

/-- The first piece's double integral vanishes: its inner
integral vanishes pointwise on the first circle. -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_first_eq_zero
    {lam₁ lam₂ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a z)
      = 0 := by
  have h0 : (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
        (w - z)⁻¹ • resolvent a z)
      = ∮ z in C(lam₁, r₁), (0 : A) := by
    refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
    exact circleIntegral_inv_sub_smul_const_sep_eq_zero hz hsep hr₂
      (resolvent a z)
  rw [h0]
  show (∫ θ in 0..2 * π, deriv (circleMap lam₁ r₁) θ • (0 : A)) = 0
  simp

/-! ## The Fubini swap for the second piece -/

/-- The joint angle integrand of the second piece is
continuous on the whole angle plane: the two circles are
disjoint by the separation grade, and the resolvent is
continuous at every point of the second circle. -/
theorem continuous_joint_kernel_resolvent_sep {lam₁ lam₂ : ℂ}
    {R₂ : ℝ} (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    Continuous (fun p : ℝ × ℝ =>
      (deriv (circleMap lam₁ r₁) p.1 * deriv (circleMap lam₂ r₂) p.2) •
        ((circleMap lam₂ r₂ p.2 - circleMap lam₁ r₁ p.1)⁻¹
          • resolvent a (circleMap lam₂ r₂ p.2))) := by
  have hRcm : Continuous (fun θ => resolvent a (circleMap lam₂ r₂ θ)) :=
    continuous_resolvent_circleMap a hr₂.le
      (fun z hz => mem_resolventSet_of_sphere_of_isolated a h₂ hr₂ hr₂R hz)
  have hne : ∀ p : ℝ × ℝ,
      circleMap lam₂ r₂ p.2 - circleMap lam₁ r₁ p.1 ≠ 0 := by
    intro p
    exact sub_ne_zero.mpr (ne_of_mem_spheres_sep
      (circleMap_mem_sphere lam₁ hr₁.le p.1)
      (circleMap_mem_sphere lam₂ hr₂.le p.2) hsep)
  have hd : Continuous (fun p : ℝ × ℝ =>
      deriv (circleMap lam₁ r₁) p.1 * deriv (circleMap lam₂ r₂) p.2) :=
    ((continuous_deriv_circleMap lam₁ r₁).comp continuous_fst).mul
      ((continuous_deriv_circleMap lam₂ r₂).comp continuous_snd)
  have hker : Continuous (fun p : ℝ × ℝ =>
      (circleMap lam₂ r₂ p.2 - circleMap lam₁ r₁ p.1)⁻¹
        • resolvent a (circleMap lam₂ r₂ p.2)) :=
    ((((continuous_circleMap lam₂ r₂).comp continuous_snd).sub
      ((continuous_circleMap lam₁ r₁).comp continuous_fst)).inv₀ hne).smul
      (hRcm.comp continuous_snd)
  exact hd.smul hker

theorem integrableOn_joint_kernel_resolvent_sep {lam₁ lam₂ : ℂ}
    {R₂ : ℝ} (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam₁ r₁) p.1 * deriv (circleMap lam₂ r₂) p.2) •
        ((circleMap lam₂ r₂ p.2 - circleMap lam₁ r₁ p.1)⁻¹
          • resolvent a (circleMap lam₂ r₂ p.2)))
      (Set.uIoc 0 (2 * π) ×ˢ Set.uIoc 0 (2 * π)) MeasureTheory.volume := by
  have hcont := continuous_joint_kernel_resolvent_sep a h₂ hr₁ hr₂ hr₂R hsep
  have hIcc : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam₁ r₁) p.1 * deriv (circleMap lam₂ r₂) p.2) •
        ((circleMap lam₂ r₂ p.2 - circleMap lam₁ r₁ p.1)⁻¹
          • resolvent a (circleMap lam₂ r₂ p.2)))
      (Set.Icc (0 : ℝ × ℝ) (2 * π, 2 * π)) MeasureTheory.volume :=
    hcont.integrableOn_Icc
  refine hIcc.mono_set ?_
  rw [Set.uIoc_of_le Real.two_pi_pos.le]
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨⟨hp1.1.le, hp2.1.le⟩, ⟨hp1.2, hp2.2⟩⟩

/-- The second piece's double integral as an iterated
interval integral over the angle rectangle (first circle
outer). -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_eq_interval
    {lam₁ lam₂ : ℂ} {r₁ r₂ : ℝ} :
    (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
    = ∫ θ in 0..2 * π, ∫ φ in 0..2 * π,
        (deriv (circleMap lam₁ r₁) θ * deriv (circleMap lam₂ r₂) φ) •
          ((circleMap lam₂ r₂ φ - circleMap lam₁ r₁ θ)⁻¹
            • resolvent a (circleMap lam₂ r₂ φ)) := by
  show (∫ θ in 0..2 * π, deriv (circleMap lam₁ r₁) θ
      • (∮ w in C(lam₂, r₂), (w - circleMap lam₁ r₁ θ)⁻¹ • resolvent a w))
    = _
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  show deriv (circleMap lam₁ r₁) θ
      • (∫ φ in 0..2 * π, deriv (circleMap lam₂ r₂) φ
        • ((circleMap lam₂ r₂ φ - circleMap lam₁ r₁ θ)⁻¹
          • resolvent a (circleMap lam₂ r₂ φ)))
    = ∫ φ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun φ _ => smul_smul _ _ _)

/-- The second piece's double integral as an iterated
interval integral over the angle rectangle (second circle
outer). -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_swap_eq_interval
    {lam₁ lam₂ : ℂ} {r₁ r₂ : ℝ} :
    (∮ w in C(lam₂, r₂), ∮ z in C(lam₁, r₁), (w - z)⁻¹ • resolvent a w)
    = ∫ φ in 0..2 * π, ∫ θ in 0..2 * π,
        (deriv (circleMap lam₁ r₁) θ * deriv (circleMap lam₂ r₂) φ) •
          ((circleMap lam₂ r₂ φ - circleMap lam₁ r₁ θ)⁻¹
            • resolvent a (circleMap lam₂ r₂ φ)) := by
  show (∫ φ in 0..2 * π, deriv (circleMap lam₂ r₂) φ
      • (∮ z in C(lam₁, r₁), (circleMap lam₂ r₂ φ - z)⁻¹
        • resolvent a (circleMap lam₂ r₂ φ)))
    = _
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  show deriv (circleMap lam₂ r₂) φ
      • (∫ θ in 0..2 * π, deriv (circleMap lam₁ r₁) θ
        • ((circleMap lam₂ r₂ φ - circleMap lam₁ r₁ θ)⁻¹
          • resolvent a (circleMap lam₂ r₂ φ)))
    = ∫ θ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [smul_smul, mul_comm (deriv (circleMap lam₂ r₂) φ)
    (deriv (circleMap lam₁ r₁) θ)]

/-- Fubini swap of the second piece's double circle
integral. -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_swap
    {lam₁ lam₂ : ℂ} {R₂ : ℝ}
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
    = ∮ w in C(lam₂, r₂), ∮ z in C(lam₁, r₁), (w - z)⁻¹ • resolvent a w := by
  rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_eq_interval,
    circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_swap_eq_interval]
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap
    (integrableOn_joint_kernel_resolvent_sep a h₂ hr₁ hr₂ hr₂R hsep)

/-- The second piece's double integral vanishes: swap, then
evaluate the inner integral by disc Cauchy-Goursat. -/
theorem circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_eq_zero
    {lam₁ lam₂ : ℂ} {R₂ : ℝ}
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      = 0 := by
  rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_swap a h₂
    hr₁ hr₂ hr₂R hsep]
  have h0 : (∮ w in C(lam₂, r₂), ∮ z in C(lam₁, r₁),
        (w - z)⁻¹ • resolvent a w)
      = ∮ w in C(lam₂, r₂), (0 : A) := by
    refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
    exact circleIntegral_inv_sub_smul_const_sep_swap_eq_zero hw hsep hr₁
      (resolvent a w)
  rw [h0]
  show (∫ θ in 0..2 * π, deriv (circleMap lam₂ r₂) θ • (0 : A)) = 0
  simp

/-! ## The product as a double integral, and its evaluation -/

theorem circleIntegral_mul_circleIntegral_resolvent_sep {lam₁ lam₂ : ℂ}
    {r₁ r₂ : ℝ} (hf₁ : CircleIntegrable (resolvent a) lam₁ r₁)
    (hf₂ : CircleIntegrable (resolvent a) lam₂ r₂) (hr₁ : 0 ≤ r₁) :
    (∮ z in C(lam₁, r₁), resolvent a z)
        * (∮ w in C(lam₂, r₂), resolvent a w)
      = ∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
          resolvent a z * resolvent a w := by
  rw [circleIntegral_mul_const (∮ w in C(lam₂, r₂), resolvent a w) hf₁]
  refine circleIntegral.integral_congr hr₁ (fun z _ => ?_)
  exact const_mul_circleIntegral (resolvent a z) hf₂

/-- The key computation: the product of the resolvent
integrals over two separated circles is zero - both pieces
of the resolvent-identity split vanish. -/
theorem circleIntegral_resolvent_mul_eq_zero_sep {lam₁ lam₂ : ℂ}
    {R₁ R₂ : ℝ} (h₁ : specIsolatedWithin a lam₁ R₁)
    (h₂ : specIsolatedWithin a lam₂ R₂) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁R : r₁ ≤ R₁) (hr₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    (∮ z in C(lam₁, r₁), resolvent a z)
        * (∮ w in C(lam₂, r₂), resolvent a w)
      = 0 := by
  have hf₁ : CircleIntegrable (resolvent a) lam₁ r₁ :=
    circleIntegrable_resolvent_of_isolated a h₁ hr₁ hr₁R
  have hf₂ : CircleIntegrable (resolvent a) lam₂ r₂ :=
    circleIntegrable_resolvent_of_isolated a h₂ hr₂ hr₂R
  have hD1 : ∀ z ∈ Metric.sphere lam₁ r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a z) lam₂ r₂ :=
    fun z hz => circleIntegrable_inv_sub_smul_const_sep (resolvent a z)
      hz hsep hr₂
  have hD2 : ∀ z ∈ Metric.sphere lam₁ r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • resolvent a w) lam₂ r₂ :=
    fun z hz => circleIntegrable_inv_sub_smul_resolvent_sep a hf₂ hz hsep hr₂
  have hG1 : CircleIntegrable
      (fun z => ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a z)
      lam₁ r₁ := by
    refine (circleIntegrable_congr (f₂ := fun _ => (0 : A)) ?_).mpr
      (circleIntegrable_const (0 : A) lam₁ r₁)
    intro z hz
    rw [abs_of_pos hr₁] at hz
    exact circleIntegral_inv_sub_smul_const_sep_eq_zero hz hsep hr₂
      (resolvent a z)
  have hG2 : CircleIntegrable
      (fun z => ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w)
      lam₁ r₁ :=
    circleIntegrable_circleIntegral_inv_sub_smul_resolvent_sep a h₁ h₂
      hr₁ hr₂ hr₁R hr₂R hsep
  calc (∮ z in C(lam₁, r₁), resolvent a z)
          * (∮ w in C(lam₂, r₂), resolvent a w)
      = ∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
          resolvent a z * resolvent a w :=
        circleIntegral_mul_circleIntegral_resolvent_sep a hf₁ hf₂ hr₁.le
    _ = ∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
          (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        exact resolvent_mul_eq_inv_sub_smul_sub a
          (mem_resolventSet_of_sphere_of_isolated a h₁ hr₁ hr₁R hz)
          (mem_resolventSet_of_sphere_of_isolated a h₂ hr₂ hr₂R hw)
          (ne_of_mem_spheres_sep hz hw hsep)
    _ = ∮ z in C(lam₁, r₁), ((∮ w in C(lam₂, r₂),
            (w - z)⁻¹ • resolvent a z)
          - ∮ w in C(lam₂, r₂), (w - z)⁻¹ • resolvent a w) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        have hfun : (fun w => (w - z)⁻¹ • (resolvent a z - resolvent a w))
            = (fun w => (w - z)⁻¹ • resolvent a z)
              - (fun w => (w - z)⁻¹ • resolvent a w) :=
          funext fun w => smul_sub _ _ _
        rw [hfun]
        exact circleIntegral.integral_sub (hD1 z hz) (hD2 z hz)
    _ = (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
            (w - z)⁻¹ • resolvent a z)
          - (∮ z in C(lam₁, r₁), ∮ w in C(lam₂, r₂),
            (w - z)⁻¹ • resolvent a w) :=
        circleIntegral.integral_sub hG1 hG2
    _ = 0 - 0 := by
        rw [circleIntegral_circleIntegral_inv_sub_smul_resolvent_first_eq_zero
            a hr₁ hr₂ hsep,
          circleIntegral_circleIntegral_inv_sub_smul_resolvent_sep_eq_zero
            a h₂ hr₁ hr₂ hr₂R hsep]
    _ = 0 := sub_self 0

/-! ## Orthogonality -/

/-- **Headline (8B-2): two-point Riesz orthogonality.** For
two isolated spectral points with disjoint separating discs
(the grade hypothesis `r₁ + r₂ < ‖lam₂ - lam₁‖`, radii
inside the isolation radii), the Riesz projections are
orthogonal. Note the grade hypothesis forces `lam₁ ≠ lam₂`
(the distance is positive). -/
theorem rieszProj_mul_rieszProj_of_isolated_ne {lam₁ lam₂ : ℂ}
    {R₁ R₂ : ℝ} {r₁ r₂ : ℝ}
    (h₁ : specIsolatedWithin a lam₁ R₁) (h₂ : specIsolatedWithin a lam₂ R₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁R : r₁ ≤ R₁) (h₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    rieszProj a lam₁ r₁ * rieszProj a lam₂ r₂ = 0 := by
  have hJJ := circleIntegral_resolvent_mul_eq_zero_sep a h₁ h₂ hr₁ hr₂
    h₁R h₂R hsep
  show ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ z in C(lam₁, r₁), resolvent a z)
      * ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ w in C(lam₂, r₂), resolvent a w)
    = 0
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hJJ, smul_zero]

/-- Symmetric companion: the product in the other order
also vanishes, by the headline with the two points swapped
(`‖lam₁ - lam₂‖ = ‖lam₂ - lam₁‖`). -/
theorem rieszProj_mul_rieszProj_of_isolated_ne_swap {lam₁ lam₂ : ℂ}
    {R₁ R₂ : ℝ} {r₁ r₂ : ℝ}
    (h₁ : specIsolatedWithin a lam₁ R₁) (h₂ : specIsolatedWithin a lam₂ R₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁R : r₁ ≤ R₁) (h₂R : r₂ ≤ R₂)
    (hsep : r₁ + r₂ < ‖lam₂ - lam₁‖) :
    rieszProj a lam₂ r₂ * rieszProj a lam₁ r₁ = 0 := by
  have hnorm : ‖lam₁ - lam₂‖ = ‖lam₂ - lam₁‖ := by
    rw [← neg_sub lam₂ lam₁, norm_neg]
  have hsep' : r₂ + r₁ < ‖lam₁ - lam₂‖ := by
    rw [hnorm]
    linarith
  exact rieszProj_mul_rieszProj_of_isolated_ne a h₂ h₁ hr₂ hr₁ h₂R h₁R hsep'

/-- Two-point radius independence: the product of the two
projections does not depend on the chosen radii inside the
isolation radii (each factor by GATE-A1's
`rieszProj_eq_of_le`). -/
theorem rieszProj_two_point_radius_indep {lam₁ lam₂ : ℂ}
    {R₁ R₂ : ℝ}
    (h₁ : specIsolatedWithin a lam₁ R₁) (h₂ : specIsolatedWithin a lam₂ R₂)
    {r₁ r₁' r₂ r₂' : ℝ}
    (hr₁ : 0 < r₁) (hr₁' : 0 < r₁') (hr₂ : 0 < r₂) (hr₂' : 0 < r₂')
    (h₁R : r₁ ≤ R₁) (h₁R' : r₁' ≤ R₁) (h₂R : r₂ ≤ R₂) (h₂R' : r₂' ≤ R₂) :
    rieszProj a lam₁ r₁ * rieszProj a lam₂ r₂
      = rieszProj a lam₁ r₁' * rieszProj a lam₂ r₂' := by
  rw [rieszProj_eq_of_le a h₁ hr₁ hr₁' h₁R h₁R',
    rieszProj_eq_of_le a h₂ hr₂ hr₂' h₂R h₂R']

end

end ThetLogos
