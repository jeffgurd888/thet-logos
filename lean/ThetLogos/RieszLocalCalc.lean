/-
# SHELF 8B-3 - Local single-circle calculus at an isolated point

Extension 8B-3 registered in
`whitepaper/shelf-8b345-registration-2026-11-02.md`, scoped in
`whitepaper/shelf-8b-scoping-2026-11-02.md` SS2 (8B-3 paragraph):
the local functional calculus of a holomorphic germ `f` at an
isolated spectral point `lam` of an element `a` of a complex Banach
algebra, defined by the single circle integral
`rieszLocalFC a lam r f = (2 pi i)^{-1} . \oint f(z) . resolvent a z`.

Landed headlines: radius independence under `specIsolatedWithin`
(the `f`-weighted annulus Cauchy-Goursat step, pattern of GATE-A1's
`circleIntegral_resolvent_eq_of_isolated`); the values at `f = 1`
(the Riesz projection) and at `f = id` (`a * rieszProj`); additivity
and scalar rules; commutation with `a`; MULTIPLICATIVITY
`FC (f * g) = FC f * FC g` (the `f`-weighted double integral, on
GATE-A2's engine: first resolvent identity, Cauchy integral formula
for `g` on the inner piece, Fubini swap and disc Cauchy-Goursat for
the second piece, with the auxiliary closed form for the
`g`-weighted kernel exactly as in GATE-A2's
`circleIntegral_inv_sub_smul_resolvent_eq`); and corner absorption
`P * FC = FC = FC * P`, as corollaries of multiplicativity at
`f = 1`.

Seam S-8B-3 (pre-registered): the multiplicativity seam does NOT
trigger - headline (7) is landed in full, so this brick lands FULL,
not PARTIAL, and "multiplicativity of the local calculus" is not an
open remainder of this module.

Fences on the face: only the corrected integrability form
`circleIntegrable_resolvent_of_nonneg` (RieszGate.lean:135) is
consumed from GATE-A1 - the killed form `circleIntegrable_resolvent`
(K-8B-KILLED-FORM) does not exist in-tree and is never cited; every
`f`-weighted integrability analogue proved here carries `0 < r`
(or `0 <= r`) on its face, and radii in headlines are `0 < r <= R`.
This is a SINGLE-circle local calculus at an isolated point - not
the general contour calculus, not SHELF-7b. NO CLAIM; dials 0/4.
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

/-- The local functional calculus at `lam`: the normalized circle
integral of `f z . resolvent a z` over the circle of radius `r`
around `lam`. -/
def rieszLocalFC (a : A) (lam : ℂ) (r : ℝ) (f : ℂ → ℂ) : A :=
  (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z

variable {f g : ℂ → ℂ} {lam : ℂ} {R : ℝ}

/-! ## Support: differentiability and continuity of the weighted
integrand -/

/-- A function differentiable on a closed ball is differentiable at
every interior point of the ball. -/
theorem differentiableAt_of_differentiableOn_closedBall
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R)) {z : ℂ}
    (hz : z ∈ Metric.ball lam R) : DifferentiableAt ℂ f z :=
  hf.differentiableAt
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
      Metric.ball_subset_closedBall)

/-- The weighted integrand `f z . resolvent a z` is continuous on
any set inside the closed disc where the resolvent is defined. -/
theorem continuousOn_smul_resolvent_of_differentiableOn
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {s : Set ℂ} (hsR : s ⊆ Metric.closedBall lam R)
    (hs : s ⊆ resolventSet ℂ a) :
    ContinuousOn (fun z => f z • resolvent a z) s :=
  (hf.continuousOn.mono hsR).smul (continuousOn_resolvent a hs)

/-! ## The `f`-weighted integrability analogue (corrected form:
`0 < r` on its face; K-8B-KILLED-FORM respected) -/

theorem circleIntegrable_smul_resolvent_of_isolated
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    CircleIntegrable (fun z => f z • resolvent a z) lam r := by
  refine (continuousOn_smul_resolvent_of_differentiableOn a hf
    (s := Metric.sphere lam r) ?_ ?_).circleIntegrable hr.le
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hz.le.trans hrR
  · intro z hz
    exact mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz

/-! ## Headline (1): radius independence -/

theorem circleIntegral_smul_resolvent_eq_of_isolated
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∮ z in C(lam, R), f z • resolvent a z)
      = ∮ z in C(lam, r), f z • resolvent a z := by
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty ?_ ?_
  · refine continuousOn_smul_resolvent_of_differentiableOn a hf ?_ ?_
    · exact Set.sdiff_subset
    · intro z hz
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
    exact (differentiableAt_of_differentiableOn_closedBall hf
      (by rwa [Metric.mem_ball, dist_eq_norm])).smul
        (spectrum.hasDerivAt_resolvent_const_left hzmem).differentiableAt

theorem rieszLocalFC_eq_of_le (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ R) (h₂ : r₂ ≤ R) :
    rieszLocalFC a lam r₁ f = rieszLocalFC a lam r₂ f := by
  have e1 := circleIntegral_smul_resolvent_eq_of_isolated a hR hf hr₁ h₁
  have e2 := circleIntegral_smul_resolvent_eq_of_isolated a hR hf hr₂ h₂
  show (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r₁), f z • resolvent a z)
    = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r₂), f z • resolvent a z)
  rw [← e1, ← e2]

/-! ## Headline (2): the value at `f = 1` -/

theorem rieszLocalFC_one (r : ℝ) :
    rieszLocalFC a lam r (fun _ => (1 : ℂ)) = rieszProj a lam r := by
  show (2 * π * Complex.I : ℂ)⁻¹
      • (∮ z in C(lam, r), (fun _ => (1 : ℂ)) z • resolvent a z)
    = (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z
  congr 2
  funext z
  exact one_smul ℂ (resolvent a z)

/-! ## Headline (3): the value at `f = id` -/

/-- The circle integral of the constant function `1` vanishes. -/
theorem circleIntegral_const_one (c : ℂ) (r : ℝ) :
    (∮ z in C(c, r), (1 : A)) = 0 :=
  circleIntegral.integral_eq_zero_of_hasDerivWithinAt'
    (f := fun z => z • (1 : A)) (f' := fun _ => (1 : A))
    (fun z _ => by
      simpa using ((hasDerivAt_id z).smul_const (1 : A)).hasDerivWithinAt)

/-- Pointwise: `z . resolvent a z = 1 + a * resolvent a z` at
resolvent points. -/
theorem smul_resolvent_eq_one_add {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    z • resolvent a z = 1 + a * resolvent a z := by
  have h1 : (algebraMap ℂ A z - a) * resolvent a z = 1 := by
    have e : (algebraMap ℂ A z - a) * resolvent a z
        = ↑hz.unit * ↑hz.unit⁻¹ := by
      rw [spectrum.resolvent_eq hz, hz.unit_spec]
    rw [e]
    exact Units.mul_inv _
  have h2 : algebraMap ℂ A z * resolvent a z = 1 + a * resolvent a z := by
    have := h1
    rw [sub_mul] at this
    exact eq_add_of_sub_eq this
  calc z • resolvent a z = algebraMap ℂ A z * resolvent a z := by
        rw [Algebra.smul_def]
    _ = 1 + a * resolvent a z := h2

theorem rieszLocalFC_id (hR : specIsolatedWithin a lam R)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rieszLocalFC a lam r id = a * rieszProj a lam r := by
  have hfR : CircleIntegrable (resolvent a) lam r :=
    circleIntegrable_resolvent_of_isolated a hR hr hrR
  have hJ : (∮ z in C(lam, r), id z • resolvent a z)
      = a * ∮ z in C(lam, r), resolvent a z := by
    have heq : (∮ z in C(lam, r), id z • resolvent a z)
        = ∮ z in C(lam, r), ((1 : A) + a * resolvent a z) := by
      refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
      exact smul_resolvent_eq_one_add a
        (mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz)
    have hfM : CircleIntegrable (fun z => a * resolvent a z) lam r := by
      refine ((continuousOn_const.mul (continuousOn_resolvent a ?_)).circleIntegrable
        hr.le)
      intro z hz
      exact mem_resolventSet_of_sphere_of_isolated a hR hr hrR hz
    rw [heq, circleIntegral.integral_add (circleIntegrable_const (1 : A) lam r)
      hfM, circleIntegral_const_one lam r, zero_add]
    exact (const_mul_circleIntegral a hfR).symm
  show (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r), id z • resolvent a z)
    = a * ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z)
  rw [hJ, mul_smul_comm]

/-! ## Headline (4): additivity and scalar rules -/

theorem rieszLocalFC_add (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rieszLocalFC a lam r (f + g)
      = rieszLocalFC a lam r f + rieszLocalFC a lam r g := by
  have hfI := circleIntegrable_smul_resolvent_of_isolated a hR hf hr hrR
  have hgI := circleIntegrable_smul_resolvent_of_isolated a hR hg hr hrR
  have hstep : (∮ z in C(lam, r), (f + g) z • resolvent a z)
      = ∮ z in C(lam, r), (f z • resolvent a z + g z • resolvent a z) :=
    circleIntegral.integral_congr hr.le (fun z _ => by
      simp only [Pi.add_apply, add_smul])
  show (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r), (f + g) z • resolvent a z)
    = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r), f z • resolvent a z)
      + (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r), g z • resolvent a z)
  rw [hstep, circleIntegral.integral_add hfI hgI, smul_add]

theorem rieszLocalFC_smul (c : ℂ) (r : ℝ) :
    rieszLocalFC a lam r (c • f) = c • rieszLocalFC a lam r f := by
  have hfun : (fun z => (c • f) z • resolvent a z)
      = (fun z => c • (f z • resolvent a z)) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm c (f z)]
  show (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(lam, r), (c • f) z • resolvent a z)
    = c • ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z)
  rw [hfun, circleIntegral.integral_smul, smul_smul,
    mul_comm ((2 * π * Complex.I : ℂ)⁻¹) c, ← smul_smul]

/-! ## Headline (6): commutation with `a` (no holomorphicity
hypothesis needed) -/

theorem commute_a_rieszLocalFC (r : ℝ) : Commute a (rieszLocalFC a lam r f) := by
  by_cases hf : CircleIntegrable (fun z => f z • resolvent a z) lam r
  · have hJ : a * (∮ z in C(lam, r), f z • resolvent a z)
        = (∮ z in C(lam, r), f z • resolvent a z) * a := by
      rw [const_mul_circleIntegral a hf, circleIntegral_mul_const a hf]
      show (∫ θ : ℝ in 0..2 * π,
          deriv (circleMap lam r) θ • (a * (f (circleMap lam r θ)
            • resolvent a (circleMap lam r θ))))
        = ∫ θ : ℝ in 0..2 * π,
          deriv (circleMap lam r) θ • ((f (circleMap lam r θ)
            • resolvent a (circleMap lam r θ)) * a)
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      congr 1
      rw [mul_smul_comm, smul_mul_assoc, Commute.eq (commute_a_resolvent_all a)]
    show a * ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z)
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z) * a
    rw [mul_smul_comm, smul_mul_assoc, hJ]
  · show a * ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z)
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z) * a
    rw [circleIntegral.integral_undef hf, smul_zero, mul_zero, zero_mul]

/-! ## Headline (7) engine: the `f`-weighted double integral
(GATE-A2 pattern, with the scalar weights `f, g` carried through) -/

/-- Inner integrability, second piece kernel: for `z` on the inner
sphere, `w ↦ (w - z)⁻¹ . (g w . resolvent a w)` is circle-integrable
on the outer circle. -/
theorem circleIntegrable_inv_sub_smul_weighted_resolvent
    (hR : specIsolatedWithin a lam R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    CircleIntegrable (fun w => (w - z)⁻¹ • (g w • resolvent a w)) lam r₂ := by
  have hgC : ContinuousOn g (Metric.sphere lam r₂) := by
    refine hg.continuousOn.mono (fun w hw => ?_)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw.le.trans hr₂R
  have hRC : ContinuousOn (resolvent a) (Metric.sphere lam r₂) :=
    continuousOn_resolvent a
      (fun w hw => mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw)
  have hinv : ContinuousOn (fun w => (w - z)⁻¹) (Metric.sphere lam r₂) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (ne_of_mem_sphere_of_lt hz hw h12))
  exact (hinv.smul (hgC.smul hRC)).circleIntegrable hr₂.le

/-- Inner integrability, first piece kernel: for `z` on the inner
sphere and a constant `x : A`, `w ↦ (w - z)⁻¹ . (g w . x)` is
circle-integrable on the outer circle. -/
theorem circleIntegrable_inv_sub_smul_weighted_const
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) (x : A) :
    CircleIntegrable (fun w => (w - z)⁻¹ • (g w • x)) lam r₂ := by
  have hgC : ContinuousOn g (Metric.sphere lam r₂) := by
    refine hg.continuousOn.mono (fun w hw => ?_)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw.le.trans hr₂R
  have hinv : ContinuousOn (fun w => (w - z)⁻¹) (Metric.sphere lam r₂) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (ne_of_mem_sphere_of_lt hz hw h12))
  exact (hinv.smul (hgC.smul continuousOn_const)).circleIntegrable hr₂.le

/-- Inner integrability, second piece as it appears in the split:
`w ↦ (w - z)⁻¹ . (f z . (g w . resolvent a w))`. -/
theorem circleIntegrable_piece_two_inner
    (hR : specIsolatedWithin a lam R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    CircleIntegrable
      (fun w => (w - z)⁻¹ • (f z • (g w • resolvent a w))) lam r₂ := by
  have hgC : ContinuousOn g (Metric.sphere lam r₂) := by
    refine hg.continuousOn.mono (fun w hw => ?_)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw.le.trans hr₂R
  have hRC : ContinuousOn (resolvent a) (Metric.sphere lam r₂) :=
    continuousOn_resolvent a
      (fun w hw => mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw)
  have hinv : ContinuousOn (fun w => (w - z)⁻¹) (Metric.sphere lam r₂) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (ne_of_mem_sphere_of_lt hz hw h12))
  exact (hinv.smul (continuousOn_const.smul (hgC.smul hRC))).circleIntegrable
    hr₂.le

/-- Inner evaluation, first piece: the Cauchy integral formula for
`g` (the pin's `DifferentiableOn.circleIntegral_sub_inv_smul`). -/
theorem circleIntegral_inv_sub_smul_weighted_const
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) (x : A) :
    (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • x)) = (2 * π * Complex.I : ℂ) • (g z • x) := by
  have hd : DifferentiableOn ℂ (fun w => g w • x) (Metric.closedBall lam r₂) :=
    (hg.mono (Metric.closedBall_subset_closedBall hr₂R)).smul_const x
  exact hd.circleIntegral_sub_inv_smul (mem_ball_of_mem_sphere_of_lt hz h12)

/-- Inner vanishing, second piece after the swap: for `w` on the
outer sphere and a constant `y : A`, the `z`-integral of
`(w - z)⁻¹ . (f z . y)` over the inner circle is `0` (disc
Cauchy-Goursat; `w` lies outside the inner disc and `f` is
holomorphic on the large disc). -/
theorem circleIntegral_inv_sub_smul_weighted_eq_zero
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R)
    {w : ℂ} (hw : w ∈ Metric.sphere lam r₂) (y : A) :
    (∮ z in C(lam, r₁), (w - z)⁻¹ • (f z • y)) = 0 := by
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
  have hw' : ‖w - lam‖ = r₂ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hw
  have hne : ∀ z ∈ Metric.closedBall lam r₁, w - z ≠ 0 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    refine sub_ne_zero.mpr (fun hzw => ?_)
    rw [← hzw] at hz
    exact (not_le_of_gt h12) (hw' ▸ hz)
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr₁.le Set.countable_empty ?_ ?_
  · have hinv : ContinuousOn (fun z => (w - z)⁻¹) (Metric.closedBall lam r₁) :=
      (continuousOn_const.sub continuousOn_id).inv₀ hne
    have hfC : ContinuousOn (fun z => f z • y) (Metric.closedBall lam r₁) :=
      (hf.continuousOn.mono
        (Metric.closedBall_subset_closedBall hr₁R)).smul continuousOn_const
    exact hinv.smul hfC
  · intro z hz
    obtain ⟨hzball, -⟩ := hz
    have hzR : z ∈ Metric.ball lam R :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hzball)
        (h12.le.trans hr₂R))
    have hfd : DifferentiableAt ℂ f z :=
      differentiableAt_of_differentiableOn_closedBall hf hzR
    have hinvd : DifferentiableAt ℂ (fun z => (w - z)⁻¹) z :=
      ((differentiableAt_const w).sub differentiableAt_id).inv
        (hne z (Metric.ball_subset_closedBall hzball))
    exact hinvd.smul (hfd.smul_const y)

/-- The auxiliary closed form for the `g`-weighted kernel
`H z = ∮ (w - z)⁻¹ . (g w . resolvent a w)`, multiplied by
`algebraMap z - a` (GATE-A2's auxiliary identity, weighted). -/
theorem sub_a_mul_circleIntegral_inv_sub_smul_weighted_resolvent
    (hR : specIsolatedWithin a lam R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂R : r₂ ≤ R) (h12 : r₁ < r₂)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    (algebraMap ℂ A z - a)
        * (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w))
      = (2 * π * Complex.I : ℂ) • (g z • (1 : A))
        - ∮ w in C(lam, r₂), g w • resolvent a w := by
  have hf2 : CircleIntegrable (fun w => (w - z)⁻¹ • (g w • resolvent a w))
      lam r₂ :=
    circleIntegrable_inv_sub_smul_weighted_resolvent a hR hg hr₂ hr₂R h12 hz
  have hf1 : CircleIntegrable (fun w => (w - z)⁻¹ • (g w • (1 : A))) lam r₂ :=
    circleIntegrable_inv_sub_smul_weighted_const hg hr₂ hr₂R h12 hz (1 : A)
  have hfR : CircleIntegrable (fun w => g w • resolvent a w) lam r₂ :=
    circleIntegrable_smul_resolvent_of_isolated a hR hg hr₂ hr₂R
  calc (algebraMap ℂ A z - a)
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w))
      = ∮ w in C(lam, r₂),
          (algebraMap ℂ A z - a) * ((w - z)⁻¹ • (g w • resolvent a w)) :=
        const_mul_circleIntegral (algebraMap ℂ A z - a) hf2
    _ = ∮ w in C(lam, r₂), ((w - z)⁻¹ • (g w • (1 : A)) - g w • resolvent a w) := by
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        have hwres : w ∈ resolventSet ℂ a :=
          mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw
        have hzw : w ≠ z := ne_of_mem_sphere_of_lt hz hw h12
        have e3 : (w - z)⁻¹ • (g w • ((w - z) • resolvent a w))
            = g w • resolvent a w := by
          simp only [smul_smul]
          congr 1
          rw [mul_comm (g w) (w - z), ← mul_assoc,
            inv_mul_cancel₀ (sub_ne_zero.mpr hzw), one_mul]
        calc (algebraMap ℂ A z - a) * ((w - z)⁻¹ • (g w • resolvent a w))
            = (w - z)⁻¹ • (g w • (1 - (w - z) • resolvent a w)) := by
              rw [mul_smul_comm, mul_smul_comm, sub_a_mul_resolvent a hwres]
          _ = (w - z)⁻¹ • (g w • (1 : A)) - g w • resolvent a w := by
              rw [smul_sub, smul_sub, e3]
    _ = (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • (1 : A)))
          - ∮ w in C(lam, r₂), g w • resolvent a w :=
        circleIntegral.integral_sub hf1 hfR
    _ = (2 * π * Complex.I : ℂ) • (g z • (1 : A))
          - ∮ w in C(lam, r₂), g w • resolvent a w := by
        rw [circleIntegral_inv_sub_smul_weighted_const hg hr₂R h12 hz (1 : A)]

/-- The closed form for the `g`-weighted kernel itself, by left
multiplication with `resolvent a z`. -/
theorem circleIntegral_inv_sub_smul_weighted_resolvent_eq
    (hR : specIsolatedWithin a lam R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R)
    {z : ℂ} (hz : z ∈ Metric.sphere lam r₁) :
    (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w))
      = resolvent a z * ((2 * π * Complex.I : ℂ) • (g z • (1 : A))
        - ∮ w in C(lam, r₂), g w • resolvent a w) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hzres : z ∈ resolventSet ℂ a :=
    mem_resolventSet_of_sphere_of_isolated a hR hr₁
      (h12.le.trans hr₂R) hz
  have hstep := sub_a_mul_circleIntegral_inv_sub_smul_weighted_resolvent a hR
    hg hr₂ hr₂R h12 hz
  have hunit : resolvent a z * (algebraMap ℂ A z - a) = 1 := by
    have e : resolvent a z * (algebraMap ℂ A z - a)
        = ↑hzres.unit⁻¹ * ↑hzres.unit := by
      rw [spectrum.resolvent_eq hzres, hzres.unit_spec]
    rw [e]
    exact Units.inv_mul _
  calc (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w))
      = (resolvent a z * (algebraMap ℂ A z - a))
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w)) := by
        rw [hunit, one_mul]
    _ = resolvent a z * ((algebraMap ℂ A z - a)
          * (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w))) :=
        mul_assoc _ _ _
    _ = resolvent a z * ((2 * π * Complex.I : ℂ) • (g z • (1 : A))
          - ∮ w in C(lam, r₂), g w • resolvent a w) := by
        rw [hstep]

/-- The outer function of the second piece, `z ↦ f z . H z`, is
circle-integrable on the inner circle: on that circle it agrees
with the closed form of the previous lemma, weighted by `f`. -/
theorem circleIntegrable_circleIntegral_piece_two
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
      lam r₁ := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
  refine (circleIntegrable_congr (f₂ := fun z => f z
    • (resolvent a z * ((2 * π * Complex.I : ℂ) • (g z • (1 : A))
      - ∮ w in C(lam, r₂), g w • resolvent a w))) ?_).mpr ?_
  · intro z hz
    rw [abs_of_pos hr₁] at hz
    have hH := circleIntegral_inv_sub_smul_weighted_resolvent_eq a hR hg
      hr₁ h12 hr₂R hz
    have hstep : (∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
        = f z • (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • resolvent a w)) := by
      rw [← circleIntegral.integral_smul]
      refine circleIntegral.integral_congr hr₂.le (fun w _ => ?_)
      simp only [smul_smul]
      congr 1
      ring
    show (∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
      = f z • (resolvent a z * ((2 * π * Complex.I : ℂ) • (g z • (1 : A))
        - ∮ w in C(lam, r₂), g w • resolvent a w))
    rw [hstep, hH]
  · refine ((hf.continuousOn.mono ?_).smul
      ((continuousOn_resolvent a ?_).mul
        ((continuousOn_const.smul
          ((hg.continuousOn.mono ?_).smul continuousOn_const)).sub
          continuousOn_const))).circleIntegrable hr₁.le
    · intro z hz
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hz.le.trans hr₁R
    · intro z hz
      exact mem_resolventSet_of_sphere_of_isolated a hR hr₁ hr₁R hz
    · intro z hz
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hz.le.trans hr₁R

/-- The outer function of the first piece is circle-integrable on
the inner circle: on that circle its inner integral is the Cauchy
value `(2 pi i) . ((f * g) z . resolvent a z)`. -/
theorem circleIntegrable_circleIntegral_piece_one
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • (f z • resolvent a z)))
      lam r₁ := by
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
  refine (circleIntegrable_congr (f₂ := fun z =>
    (2 * π * Complex.I : ℂ) • ((f * g) z • resolvent a z)) ?_).mpr ?_
  · intro z hz
    rw [abs_of_pos hr₁] at hz
    show (∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • (f z • resolvent a z)))
      = (2 * π * Complex.I : ℂ) • ((f * g) z • resolvent a z)
    rw [circleIntegral_inv_sub_smul_weighted_const hg hr₂R h12 hz
      (f z • resolvent a z)]
    congr 1
    rw [Pi.mul_apply, smul_smul, mul_comm (g z) (f z)]
  · refine (continuousOn_const.smul
      (continuousOn_smul_resolvent_of_differentiableOn a
        (hf.mul hg) ?_ ?_)).circleIntegrable hr₁.le
    · intro z hz
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hz.le.trans hr₁R
    · intro z hz
      exact mem_resolventSet_of_sphere_of_isolated a hR hr₁ hr₁R hz

/-- The first piece's double integral evaluates to `(2 pi i)` times
the `(f * g)`-weighted inner integral. -/
theorem circleIntegral_circleIntegral_piece_one_self
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • (f z • resolvent a z)))
      = (2 * π * Complex.I : ℂ)
        • ∮ z in C(lam, r₁), (f * g) z • resolvent a z := by
  rw [← circleIntegral.integral_smul]
  refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
  rw [circleIntegral_inv_sub_smul_weighted_const hg hr₂R h12 hz
    (f z • resolvent a z)]
  congr 1
  rw [Pi.mul_apply, smul_smul, mul_comm (g z) (f z)]

/-! ## The Fubini swap for the second piece (GATE-A2 pattern,
weighted) -/

/-- The joint angle integrand of the second piece is continuous:
the two circles are disjoint, `f, g` are continuous on their
circles, and the resolvent is continuous on the outer circle. -/
theorem continuous_joint_kernel_weighted
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    Continuous (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • (f (circleMap lam r₁ p.1)
            • (g (circleMap lam r₂ p.2)
              • resolvent a (circleMap lam r₂ p.2))))) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
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
  have hfcm : Continuous (fun p : ℝ × ℝ => f (circleMap lam r₁ p.1)) := by
    refine hf.continuousOn.comp_continuous
      ((continuous_circleMap lam r₁).comp continuous_fst) (fun p => ?_)
    have hmem := circleMap_mem_sphere lam hr₁.le p.1
    rw [Metric.mem_sphere, dist_eq_norm] at hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem.le.trans hr₁R
  have hgcm : Continuous (fun p : ℝ × ℝ => g (circleMap lam r₂ p.2)) := by
    refine hg.continuousOn.comp_continuous
      ((continuous_circleMap lam r₂).comp continuous_snd) (fun p => ?_)
    have hmem := circleMap_mem_sphere lam hr₂.le p.2
    rw [Metric.mem_sphere, dist_eq_norm] at hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem.le.trans hr₂R
  have hker : Continuous (fun p : ℝ × ℝ =>
      (circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
        • (f (circleMap lam r₁ p.1)
          • (g (circleMap lam r₂ p.2)
            • resolvent a (circleMap lam r₂ p.2)))) := by
    refine Continuous.smul ?_ ?_
    · exact (((continuous_circleMap lam r₂).comp continuous_snd).sub
        ((continuous_circleMap lam r₁).comp continuous_fst)).inv₀ hne
    · exact hfcm.smul (hgcm.smul (hRcm.comp continuous_snd))
  exact hd.smul hker

theorem integrableOn_joint_kernel_weighted
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • (f (circleMap lam r₁ p.1)
            • (g (circleMap lam r₂ p.2)
              • resolvent a (circleMap lam r₂ p.2)))))
      (Set.uIoc 0 (2 * π) ×ˢ Set.uIoc 0 (2 * π)) MeasureTheory.volume := by
  have hcont := continuous_joint_kernel_weighted a hR hf hg hr₁ h12 hr₂R
  have hIcc : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (circleMap lam r₁) p.1 * deriv (circleMap lam r₂) p.2) •
        ((circleMap lam r₂ p.2 - circleMap lam r₁ p.1)⁻¹
          • (f (circleMap lam r₁ p.1)
            • (g (circleMap lam r₂ p.2)
              • resolvent a (circleMap lam r₂ p.2)))))
      (Set.Icc (0 : ℝ × ℝ) (2 * π, 2 * π)) MeasureTheory.volume :=
    hcont.integrableOn_Icc
  refine hIcc.mono_set ?_
  rw [Set.uIoc_of_le Real.two_pi_pos.le]
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨⟨hp1.1.le, hp2.1.le⟩, ⟨hp1.2, hp2.2⟩⟩

/-- The second piece's double integral as an iterated interval
integral over the angle rectangle (inner circle outer). -/
theorem circleIntegral_circleIntegral_piece_two_eq_interval {r₁ r₂ : ℝ} :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
    = ∫ θ in 0..2 * π, ∫ φ in 0..2 * π,
        (deriv (circleMap lam r₁) θ * deriv (circleMap lam r₂) φ) •
          ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
            • (f (circleMap lam r₁ θ)
              • (g (circleMap lam r₂ φ)
                • resolvent a (circleMap lam r₂ φ)))) := by
  show (∫ θ in 0..2 * π, deriv (circleMap lam r₁) θ
      • (∮ w in C(lam, r₂), (w - circleMap lam r₁ θ)⁻¹
        • (f (circleMap lam r₁ θ) • (g w • resolvent a w))))
    = _
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  show deriv (circleMap lam r₁) θ
      • (∫ φ in 0..2 * π, deriv (circleMap lam r₂) φ
        • ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
          • (f (circleMap lam r₁ θ)
            • (g (circleMap lam r₂ φ)
              • resolvent a (circleMap lam r₂ φ)))))
    = ∫ φ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  simp only [smul_smul]
  congr 1
  ring

/-- The second piece's double integral as an iterated interval
integral over the angle rectangle (outer circle outer). -/
theorem circleIntegral_circleIntegral_piece_two_swap_eq_interval {r₁ r₂ : ℝ} :
    (∮ w in C(lam, r₂), ∮ z in C(lam, r₁), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
    = ∫ φ in 0..2 * π, ∫ θ in 0..2 * π,
        (deriv (circleMap lam r₁) θ * deriv (circleMap lam r₂) φ) •
          ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
            • (f (circleMap lam r₁ θ)
              • (g (circleMap lam r₂ φ)
                • resolvent a (circleMap lam r₂ φ)))) := by
  show (∫ φ in 0..2 * π, deriv (circleMap lam r₂) φ
      • (∮ z in C(lam, r₁), (circleMap lam r₂ φ - z)⁻¹
        • (f z • (g (circleMap lam r₂ φ)
          • resolvent a (circleMap lam r₂ φ)))))
    = _
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  show deriv (circleMap lam r₂) φ
      • (∫ θ in 0..2 * π, deriv (circleMap lam r₁) θ
        • ((circleMap lam r₂ φ - circleMap lam r₁ θ)⁻¹
          • (f (circleMap lam r₁ θ)
            • (g (circleMap lam r₂ φ)
              • resolvent a (circleMap lam r₂ φ)))))
    = ∫ θ in 0..2 * π, _
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [smul_smul]
  congr 1
  ring

/-- Fubini swap of the second piece's double circle integral. -/
theorem circleIntegral_circleIntegral_piece_two_swap
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
    = ∮ w in C(lam, r₂), ∮ z in C(lam, r₁), (w - z)⁻¹ • (f z • (g w • resolvent a w)) := by
  rw [circleIntegral_circleIntegral_piece_two_eq_interval,
    circleIntegral_circleIntegral_piece_two_swap_eq_interval]
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap
    (integrableOn_joint_kernel_weighted a hR hf hg hr₁ h12 hr₂R)

/-- The second piece's double integral vanishes: swap, then
evaluate the inner integral by disc Cauchy-Goursat. -/
theorem circleIntegral_circleIntegral_piece_two_eq_zero
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
      = 0 := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  rw [circleIntegral_circleIntegral_piece_two_swap a hR hf hg hr₁ h12 hr₂R]
  have h0 : (∮ w in C(lam, r₂), ∮ z in C(lam, r₁),
        (w - z)⁻¹ • (f z • (g w • resolvent a w)))
      = ∮ w in C(lam, r₂), (0 : A) := by
    refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
    exact circleIntegral_inv_sub_smul_weighted_eq_zero hf hr₁ h12 hr₂R hw
      (g w • resolvent a w)
  rw [h0]
  show (∫ θ in 0..2 * π, deriv (circleMap lam r₂) θ • (0 : A)) = 0
  simp

/-! ## The product as a double integral, its split, and its
evaluation -/

theorem circleIntegral_mul_circleIntegral_weighted {r₁ r₂ : ℝ}
    (hf₁ : CircleIntegrable (fun z => f z • resolvent a z) lam r₁)
    (hf₂ : CircleIntegrable (fun w => g w • resolvent a w) lam r₂)
    (hr₁ : 0 ≤ r₁) :
    (∮ z in C(lam, r₁), f z • resolvent a z)
        * (∮ w in C(lam, r₂), g w • resolvent a w)
      = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          (f z • resolvent a z) * (g w • resolvent a w) := by
  rw [circleIntegral_mul_const (∮ w in C(lam, r₂), g w • resolvent a w) hf₁]
  refine circleIntegral.integral_congr hr₁ (fun z _ => ?_)
  exact const_mul_circleIntegral (f z • resolvent a z) hf₂

/-- The pointwise resolvent-identity split, weighted. -/
theorem smul_resolvent_mul_smul_resolvent_eq {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) (hzw : w ≠ z) :
    (f z • resolvent a z) * (g w • resolvent a w)
      = (w - z)⁻¹ • (g w • (f z • resolvent a z))
        - (w - z)⁻¹ • (f z • (g w • resolvent a w)) := by
  have h := resolvent_mul_eq_inv_sub_smul_sub a hz hw hzw
  calc (f z • resolvent a z) * (g w • resolvent a w)
      = (f z * g w) • (resolvent a z * resolvent a w) :=
        smul_mul_smul_comm _ _ _ _
    _ = (f z * g w) • ((w - z)⁻¹ • (resolvent a z - resolvent a w)) := by
        rw [h]
    _ = (w - z)⁻¹ • (g w • (f z • resolvent a z))
          - (w - z)⁻¹ • (f z • (g w • resolvent a w)) := by
        simp only [smul_sub, smul_smul]
        congr 1 <;> congr 1 <;> ring

/-- The key computation: the product of the weighted resolvent
integrals at two radii `r₁ < r₂` is `(2 pi i)` times the
`(f * g)`-weighted integral at the inner radius. -/
theorem circleIntegral_weighted_mul_eq
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    (∮ z in C(lam, r₁), f z • resolvent a z)
        * (∮ w in C(lam, r₂), g w • resolvent a w)
      = (2 * π * Complex.I : ℂ)
        • ∮ z in C(lam, r₁), (f * g) z • resolvent a z := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr₁R : r₁ ≤ R := h12.le.trans hr₂R
  have hf₁ : CircleIntegrable (fun z => f z • resolvent a z) lam r₁ :=
    circleIntegrable_smul_resolvent_of_isolated a hR hf hr₁ hr₁R
  have hf₂ : CircleIntegrable (fun w => g w • resolvent a w) lam r₂ :=
    circleIntegrable_smul_resolvent_of_isolated a hR hg hr₂ hr₂R
  have hD1 : ∀ z ∈ Metric.sphere lam r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • (g w • (f z • resolvent a z)))
        lam r₂ :=
    fun z hz => circleIntegrable_inv_sub_smul_weighted_const hg hr₂ hr₂R
      h12 hz (f z • resolvent a z)
  have hD2 : ∀ z ∈ Metric.sphere lam r₁,
      CircleIntegrable (fun w => (w - z)⁻¹ • (f z • (g w • resolvent a w)))
        lam r₂ :=
    fun z hz => circleIntegrable_piece_two_inner a hR hg hr₂ hr₂R h12 hz
  have hG1 : CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • (g w • (f z • resolvent a z)))
      lam r₁ :=
    circleIntegrable_circleIntegral_piece_one a hR hf hg hr₁ h12 hr₂R
  have hG2 : CircleIntegrable
      (fun z => ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w)))
      lam r₁ :=
    circleIntegrable_circleIntegral_piece_two a hR hf hg hr₁ h12 hr₂R
  calc (∮ z in C(lam, r₁), f z • resolvent a z)
          * (∮ w in C(lam, r₂), g w • resolvent a w)
      = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          (f z • resolvent a z) * (g w • resolvent a w) :=
        circleIntegral_mul_circleIntegral_weighted a hf₁ hf₂ hr₁.le
    _ = ∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
          ((w - z)⁻¹ • (g w • (f z • resolvent a z))
            - (w - z)⁻¹ • (f z • (g w • resolvent a w))) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        refine circleIntegral.integral_congr hr₂.le (fun w hw => ?_)
        exact smul_resolvent_mul_smul_resolvent_eq a
          (mem_resolventSet_of_sphere_of_isolated a hR hr₁ hr₁R hz)
          (mem_resolventSet_of_sphere_of_isolated a hR hr₂ hr₂R hw)
          (ne_of_mem_sphere_of_lt hz hw h12)
    _ = ∮ z in C(lam, r₁), ((∮ w in C(lam, r₂),
            (w - z)⁻¹ • (g w • (f z • resolvent a z)))
          - ∮ w in C(lam, r₂), (w - z)⁻¹ • (f z • (g w • resolvent a w))) := by
        refine circleIntegral.integral_congr hr₁.le (fun z hz => ?_)
        have hfun : (fun w => (w - z)⁻¹ • (g w • (f z • resolvent a z))
              - (w - z)⁻¹ • (f z • (g w • resolvent a w)))
            = (fun w => (w - z)⁻¹ • (g w • (f z • resolvent a z)))
              - (fun w => (w - z)⁻¹ • (f z • (g w • resolvent a w))) :=
          funext fun w => rfl
        rw [hfun]
        exact circleIntegral.integral_sub (hD1 z hz) (hD2 z hz)
    _ = (∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
            (w - z)⁻¹ • (g w • (f z • resolvent a z)))
          - (∮ z in C(lam, r₁), ∮ w in C(lam, r₂),
            (w - z)⁻¹ • (f z • (g w • resolvent a w))) :=
        circleIntegral.integral_sub hG1 hG2
    _ = ((2 * π * Complex.I : ℂ)
            • ∮ z in C(lam, r₁), (f * g) z • resolvent a z) - 0 := by
        rw [circleIntegral_circleIntegral_piece_one_self a hg hr₁ h12 hr₂R,
          circleIntegral_circleIntegral_piece_two_eq_zero a hR hf hg hr₁ h12
            hr₂R]
    _ = (2 * π * Complex.I : ℂ)
          • ∮ z in C(lam, r₁), (f * g) z • resolvent a z := sub_zero _

/-! ## Headline (7): multiplicativity -/

/-- Two-radii multiplicativity: for `0 < r₁ < r₂ ≤ R` under
isolation, `FC f r₁ * FC g r₂ = FC (f * g) r₁`. -/
theorem rieszLocalFC_mul_rieszLocalFC_of_lt
    (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    rieszLocalFC a lam r₁ f * rieszLocalFC a lam r₂ g
      = rieszLocalFC a lam r₁ (f * g) := by
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJJ := circleIntegral_weighted_mul_eq a hR hf hg hr₁ h12 hr₂R
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
        • ∮ z in C(lam, r₁), f z • resolvent a z)
      * ((2 * π * Complex.I : ℂ)⁻¹
        • ∮ w in C(lam, r₂), g w • resolvent a w)
    = (2 * π * Complex.I : ℂ)⁻¹
        • ∮ z in C(lam, r₁), (f * g) z • resolvent a z
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hJJ, smul_smul, hsc]

/-- **Headline (7): multiplicativity of the local calculus.**
`FC (f * g) = FC f * FC g` for `f, g` holomorphic on the closed
disc of the isolation radius. -/
theorem rieszLocalFC_mul (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rieszLocalFC a lam r (f * g)
      = rieszLocalFC a lam r f * rieszLocalFC a lam r g := by
  have hr2 : 0 < r / 2 := by linarith
  have hprod : rieszLocalFC a lam r f * rieszLocalFC a lam r g
      = rieszLocalFC a lam r (f * g) := by
    calc rieszLocalFC a lam r f * rieszLocalFC a lam r g
        = rieszLocalFC a lam (r / 2) f * rieszLocalFC a lam r g :=
          congrArg (· * rieszLocalFC a lam r g)
            (rieszLocalFC_eq_of_le a hR hf hr hr2 hrR (by linarith))
      _ = rieszLocalFC a lam (r / 2) (f * g) :=
          rieszLocalFC_mul_rieszLocalFC_of_lt a hR hf hg hr2
            (by linarith) hrR
      _ = rieszLocalFC a lam r (f * g) :=
          rieszLocalFC_eq_of_le a hR (hf.mul hg) hr2 hr (by linarith) hrR
  exact hprod.symm

/-! ## Headline (5): corner absorption (corollaries of
multiplicativity at `f = 1`) -/

theorem rieszProj_mul_rieszLocalFC (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r * rieszLocalFC a lam r f = rieszLocalFC a lam r f := by
  calc rieszProj a lam r * rieszLocalFC a lam r f
      = rieszLocalFC a lam r (fun _ => (1 : ℂ)) * rieszLocalFC a lam r f := by
        rw [rieszLocalFC_one]
    _ = rieszLocalFC a lam r ((fun _ => (1 : ℂ)) * f) :=
        (rieszLocalFC_mul a hR (differentiableOn_const (1 : ℂ)) hf hr hrR).symm
    _ = rieszLocalFC a lam r f := by
        congr 1
        funext z
        simp

theorem rieszLocalFC_mul_rieszProj (hR : specIsolatedWithin a lam R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall lam R))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rieszLocalFC a lam r f * rieszProj a lam r = rieszLocalFC a lam r f := by
  calc rieszLocalFC a lam r f * rieszProj a lam r
      = rieszLocalFC a lam r f * rieszLocalFC a lam r (fun _ => (1 : ℂ)) := by
        rw [rieszLocalFC_one]
    _ = rieszLocalFC a lam r (f * (fun _ => (1 : ℂ))) :=
        (rieszLocalFC_mul a hR hf (differentiableOn_const (1 : ℂ)) hr hrR).symm
    _ = rieszLocalFC a lam r f := by
        congr 1
        funext z
        simp

end

end ThetLogos
