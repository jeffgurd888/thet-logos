import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import ThetLogos.DiffEntropy
import ThetLogos.ShadowWeightIdentity
import ThetLogos.ShadowMBSeat

/-!
# ThetLogos.ShadowEntropySeat — SE-4: the rectification seat

**Status: SEAT THEOREMS. NO CLAIM. No Millennium statement, no ladder
rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing pack:
`routeb-general-scratch/pack-se-4.md`; governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md`
§3 (the seat's paper values), §4 (this module), §5 (H2 verbatim).
Gates consumed: SE-0 (`ThetLogos.ShadowEntropyPost`: the arena —
`mbDensity`, `shadowWeight`, `partitionZ`, `rectifiedDensity`, and
the registered target `shadowEntropyH2`), SE-1
(`ThetLogos.DiffEntropy`: `diffEntropy` of exactly the registered
signature, the Gaussian integrability kit), SE-2
(`ThetLogos.ShadowWeightIdentity`: the corrected weight identity
`shadow_weight_identity`, whose seat corollary carries three
integrability hypotheses — discharging them at the admissible seats
is Half A of this brick), SE-3 (`ThetLogos.ShadowMBSeat`: the MB
seat's normalization, H1, and the 1-D Gaussian values/moments).

## The memo's registered forms (quoted — these govern)

Memo §3, the partition value in closed form:

`Z = c · (1 + 2aτ)^(−1/2) · exp( b²τ / (2(1 + 2aτ)) )`.

Memo §5 (H2), the seat identity: under `0 < τ`, `0 < c ≤ 1`,
`1 + 2aτ > 0`,

`diffEntropy q − diffEntropy p = −(1/2) · Real.log (1 + 2 * a * τ)`,

with `p := mbDensity τ`, `q := rectifiedDensity τ a b c hZ`.
Half B below discharges the registered Prop in exactly this form:
`shadowEntropyH2_holds : shadowEntropyH2 diffEntropy`.

## What is proved

**Half A — the partition function and admissibility.**
`partitionZ_eq_closed_form` evaluates `partitionZ τ a b c` to the
memo §3 closed form under `0 < τ` and `0 < 1 + 2aτ`;
`partitionZ_pos` gives the `0 < partitionZ` package that
`rectifiedDensity` consumes. The three integrability hypotheses
SE-2's seat corollary carries are discharged at the seat
(`integrable_mbDensity_mul_shadowWeight`,
`integrable_rectifiedDensity_mul_log_mbDensity`,
`integrable_rectifiedDensity_mul_log_shadowWeight`), so
`shadow_weight_identity_seat` is the corrected identity at the seat
with no integrability hypotheses left. The rectified moments the
assembly consumes are computed along the way: the rectified seat is
the Gaussian with `v 0`-variance `τ/(1 + 2aτ)` and `v 0`-mean
`−bτ/(1 + 2aτ)` (`integral_rectifiedDensity_mul_coord`,
`integral_rectifiedDensity_mul_coord_sq_zero`), the other
coordinates keep variance `τ`, and `∫ q = 1`.

**Half B — H2.** The shift is assembled from SE-2's identity:
`log Z` (Half A's closed form) `− E_q[log w]` (the rectified
moments) `+ (E_p − E_q)[log p]` (SE-3's base value and the
rectified second moment). The `b`-dependence cancels between
`log Z` and `E_q[log w]`, and the `c`-dependence cancels between
the `log c` in `log Z` and the `log c` in `E_q[log w]`; both
cancellations are exhibited as named steps in
`diffEntropy_rectifiedDensity_sub` (`step_cancel_c`,
`step_cancel_b`, `step_curvature_balance`). Per K-SE-3, that
cancellation is the exhibited reason no shift comes from `b` or
`c` alone. Per K-SE-2, the value produced is the registered one,
`−(1/2) * Real.log (1 + 2 * a * τ)`, reported as computed.

## Fences

- **NO CLAIM.** Everything here is T1 machine-checked mathematics
  about the chosen densities; the Maxwell–Boltzmann closed forms
  are T4 (textbook); any reading of the seat as physics is T5 and
  is not licensed by anything here.
- **Sibling discipline (T-ENT).** The entropy here is the
  CONTINUOUS differential entropy of SE-1. The finite von Neumann
  entropy of the sibling T-ENT line is a different definition;
  nothing in this module cites it.
- **K-SE-4 (scope guard).** Everything stays inside the memo §3
  arena: exponential-quadratic weights, constant filters,
  admissibility `0 < 1 + 2aτ`.
-/

open MeasureTheory

namespace ThetLogos

/-! ## §1. One-dimensional translation helpers

Lebesgue measure on `ℝ` is invariant under right addition, so a
shifted integrand has the same integral, and shifted integrability
transports. Stated here for `ℝ` (SE-1's versions are for Pi spaces). -/

/-- Integral of a right translate on `ℝ`:
`∫ x, F (x + a) = ∫ x, F x`. -/
lemma integral_add_right_real (F : ℝ → ℝ) (a : ℝ) :
    (∫ x : ℝ, F (x + a)) = ∫ x : ℝ, F x := by
  have hmp : MeasurePreserving (· + a) (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume a
  have hemb : MeasurableEmbedding (· + a : ℝ → ℝ) :=
    (MeasurableEquiv.addRight a).measurableEmbedding
  exact hmp.integral_comp hemb F

/-- Integrability of a right translate on `ℝ`. -/
lemma integrable_add_right_real {F : ℝ → ℝ} (hF : Integrable F volume) (a : ℝ) :
    Integrable (fun x : ℝ => F (x + a)) volume := by
  have hmp : MeasurePreserving (· + a) (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume a
  have h : Integrable (F ∘ (· + a)) volume :=
    hmp.integrable_comp_of_integrable hF
  exact h

/-! ## §2. The shifted 1-D Gaussian kit

At variance parameter `s > 0` (the seat consumes `s = τ/(1 + 2aτ)`)
and shift `μ`, the Gaussian `exp (−(x − μ)²/(2s))` and its first two
moment-weighted forms: values and integrability, all reduced by
translation to SE-3's unshifted 1-D values and SE-1's / the pin's
unshifted integrability facts. -/

/-- The unshifted 1-D first-moment integrand is integrable at
variance `s`: `x ↦ x * exp (−x²/(2s))`. -/
lemma integrable_mul_exp_neg_sq_div_seat (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / (2 * s))) volume := by
  have hb : (0 : ℝ) < 1 / (2 * s) := by positivity
  apply (integrable_mul_exp_neg_mul_sq hb).congr
  filter_upwards with x
  congr 1
  congr 1
  rw [neg_sq_div_eq]

/-- **Shifted 0th moment (value).**
`∫ x, exp (−(x − μ)²/(2s)) = √(2πs)` for `0 < s`. -/
lemma integral_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    ∫ x : ℝ, Real.exp (-((x - μ) ^ 2) / (2 * s)) = Real.sqrt (2 * Real.pi * s) := by
  have key : (∫ x : ℝ, Real.exp (-((x - μ) ^ 2) / (2 * s))) =
      ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * s)) := by
    have h := integral_add_right_real
      (fun y : ℝ => Real.exp (-(y ^ 2) / (2 * s))) (-μ)
    simpa only [sub_eq_add_neg] using h
  rw [key]
  exact integral_exp_neg_sq_div_value s hs

/-- **Shifted 0th moment (integrability).** -/
lemma integrable_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
  apply (integrable_add_right_real (integrable_exp_neg_sq_div s hs) (-μ)).congr
  filter_upwards with x
  rw [sub_eq_add_neg]

/-- **Shifted 1st moment (value).**
`∫ x, x * exp (−(x − μ)²/(2s)) = μ * √(2πs)` for `0 < s`: writing
`x = (x − μ) + μ`, the odd part integrates to `0` (SE-3) and the
constant part gives `μ` times the 0th moment. -/
lemma integral_mul_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    ∫ x : ℝ, x * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      μ * Real.sqrt (2 * Real.pi * s) := by
  have hpt : ∀ x : ℝ, x * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
        μ * Real.exp (-((x - μ) ^ 2) / (2 * s)) := by
    intro x
    ring
  have hint1 : Integrable
      (fun x : ℝ => (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_mul_exp_neg_sq_div_seat s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint2 : Integrable
      (fun x : ℝ => μ * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume :=
    (integrable_exp_neg_sq_div_sub s μ hs).const_mul μ
  have hval1 : ∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)) = 0 := by
    have key : (∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) =
        ∫ x : ℝ, x * Real.exp (-(x ^ 2) / (2 * s)) := by
      have h := integral_add_right_real
        (fun y : ℝ => y * Real.exp (-(y ^ 2) / (2 * s))) (-μ)
      simpa only [sub_eq_add_neg] using h
    rw [key]
    exact integral_mul_exp_neg_sq_div s hs
  calc ∫ x : ℝ, x * Real.exp (-((x - μ) ^ 2) / (2 * s))
      = ∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
          μ * Real.exp (-((x - μ) ^ 2) / (2 * s)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) +
          ∫ x : ℝ, μ * Real.exp (-((x - μ) ^ 2) / (2 * s)) :=
        integral_add hint1 hint2
    _ = μ * Real.sqrt (2 * Real.pi * s) := by
        rw [hval1, integral_const_mul, integral_exp_neg_sq_div_sub s μ hs,
          zero_add]

/-- **Shifted 1st moment (integrability).** -/
lemma integrable_mul_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => x * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
  have hpt : ∀ x : ℝ, x * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
        μ * Real.exp (-((x - μ) ^ 2) / (2 * s)) := by
    intro x
    ring
  have hint1 : Integrable
      (fun x : ℝ => (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_mul_exp_neg_sq_div_seat s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint2 : Integrable
      (fun x : ℝ => μ * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume :=
    (integrable_exp_neg_sq_div_sub s μ hs).const_mul μ
  apply (hint1.add hint2).congr
  filter_upwards with x
  simp only [Pi.add_apply]
  exact (hpt x).symm

/-- **Shifted 2nd moment (value).**
`∫ x, x² * exp (−(x − μ)²/(2s)) = (s + μ²) * √(2πs)` for `0 < s`:
writing `x² = (x − μ)² + 2μ(x − μ) + μ²`, the middle term integrates
to `0` and the other two give SE-3's unshifted 2nd and 0th moments. -/
lemma integral_sq_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      (s + μ ^ 2) * Real.sqrt (2 * Real.pi * s) := by
  have hpt : ∀ x : ℝ, x ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
        (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) +
          μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) := by
    intro x
    ring
  have hint1 : Integrable
      (fun x : ℝ => (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_sq_mul_exp_neg_sq_div s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint2 : Integrable
      (fun x : ℝ => (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_mul_exp_neg_sq_div_seat s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint3 : Integrable
      (fun x : ℝ => μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume :=
    (integrable_exp_neg_sq_div_sub s μ hs).const_mul (μ ^ 2)
  have hval1 : ∫ x : ℝ, (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      s * Real.sqrt (2 * Real.pi * s) := by
    have key : (∫ x : ℝ, (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) =
        ∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / (2 * s)) := by
      have h := integral_add_right_real
        (fun y : ℝ => y ^ 2 * Real.exp (-(y ^ 2) / (2 * s))) (-μ)
      simpa only [sub_eq_add_neg] using h
    rw [key]
    exact integral_sq_mul_exp_neg_sq_div_value s hs
  have hval2 : ∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)) = 0 := by
    have key : (∫ x : ℝ, (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) =
        ∫ x : ℝ, x * Real.exp (-(x ^ 2) / (2 * s)) := by
      have h := integral_add_right_real
        (fun y : ℝ => y * Real.exp (-(y ^ 2) / (2 * s))) (-μ)
      simpa only [sub_eq_add_neg] using h
    rw [key]
    exact integral_mul_exp_neg_sq_div s hs
  have hAB : Integrable (fun x : ℝ =>
      (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
        (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)))) volume := by
    apply (hint1.add (hint2.const_mul (2 * μ))).congr
    filter_upwards with x
    simp only [Pi.add_apply]
  calc ∫ x : ℝ, x ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))
      = ∫ x : ℝ, ((x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
            (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)))) +
          μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x : ℝ, (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
            (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)))) +
          ∫ x : ℝ, μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) :=
        integral_add hAB hint3
    _ = ((∫ x : ℝ, (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) +
            ∫ x : ℝ, (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s)))) +
          ∫ x : ℝ, μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) := by
        rw [integral_add hint1 (hint2.const_mul (2 * μ))]
    _ = (s + μ ^ 2) * Real.sqrt (2 * Real.pi * s) := by
        rw [hval1, integral_const_mul, hval2, integral_const_mul,
          integral_exp_neg_sq_div_sub s μ hs]
        ring

/-- **Shifted 2nd moment (integrability).** -/
lemma integrable_sq_exp_neg_sq_div_sub (s μ : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)))
      volume := by
  have hpt : ∀ x : ℝ, x ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) =
      (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) +
        (2 * μ) * ((x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) +
          μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s)) := by
    intro x
    ring
  have hint1 : Integrable
      (fun x : ℝ => (x - μ) ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_sq_mul_exp_neg_sq_div s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint2 : Integrable
      (fun x : ℝ => (x - μ) * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume := by
    apply (integrable_add_right_real (integrable_mul_exp_neg_sq_div_seat s hs)
      (-μ)).congr
    filter_upwards with x
    rw [sub_eq_add_neg]
  have hint3 : Integrable
      (fun x : ℝ => μ ^ 2 * Real.exp (-((x - μ) ^ 2) / (2 * s))) volume :=
    (integrable_exp_neg_sq_div_sub s μ hs).const_mul (μ ^ 2)
  apply ((hint1.add (hint2.const_mul (2 * μ))).add hint3).congr
  filter_upwards with x
  simp only [Pi.add_apply]
  exact (hpt x).symm

/-! ## §3. The seat's coordinate factors

The unnormalized rectified product `mbDensity τ · shadowWeight a b c`
factors over coordinates. The `v 0` factor is `seatFactor0`, where
the square is completed: at `S := 1 + 2aτ > 0` it is a constant
multiple of the shifted Gaussian of §2 at variance `τ/S` and mean
`−bτ/S`. The other two factors are the plain MB 1-D weights.
`seatFactor` packages the three as one Pi factor. -/

/-- The `v 0` coordinate factor of the rectified product:
`exp (−x²/(2τ) − a·x² − b·x)`. -/
noncomputable def seatFactor0 (τ a b : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * τ) - a * x ^ 2 - b * x)

/-- **Completing the square.** For `0 < τ` and `0 < 1 + 2aτ`,
`seatFactor0 τ a b x = exp (b²τ/(2(1 + 2aτ))) ·
exp (−(x − μ)²/(2s))` with `s = τ/(1 + 2aτ)` and
`μ = −bτ/(1 + 2aτ)`. -/
lemma seatFactor0_eq_shifted (τ a b : ℝ) (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ)
    (x : ℝ) :
    seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
          (2 * (τ / (1 + 2 * a * τ)))) := by
  have hS0 : (1 + 2 * a * τ) ≠ 0 := ne_of_gt hS
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hbridge : Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
        (2 * (τ / (1 + 2 * a * τ)))) =
      Real.exp (-((1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
        (2 * τ)) := by
    congr 1
    field_simp
  rw [hbridge]
  unfold seatFactor0
  rw [← Real.exp_add]
  congr 1
  have f1 : (1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ)) = -b * τ := by
    field_simp
  have f2 : (1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ)) ^ 2 =
      b ^ 2 * τ ^ 2 / (1 + 2 * a * τ) := by
    calc (1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ)) ^ 2
        = ((1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ))) *
            (-b * τ / (1 + 2 * a * τ)) := by ring
      _ = (-b * τ) * (-b * τ / (1 + 2 * a * τ)) := by rw [f1]
      _ = b ^ 2 * τ ^ 2 / (1 + 2 * a * τ) := by
          field_simp
  have hexp : (1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2 =
      (1 + 2 * a * τ) * x ^ 2 - 2 * (-b * τ) * x +
        b ^ 2 * τ ^ 2 / (1 + 2 * a * τ) := by
    have h : (1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2 =
        (1 + 2 * a * τ) * x ^ 2 -
          2 * ((1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ))) * x +
            (1 + 2 * a * τ) * (-b * τ / (1 + 2 * a * τ)) ^ 2 := by ring
    rw [h, f1, f2]
  have f3 : (b ^ 2 * τ ^ 2 / (1 + 2 * a * τ)) / (2 * τ) =
      b ^ 2 * τ / (2 * (1 + 2 * a * τ)) := by
    field_simp
  have f4 : (2 * (-b * τ) * x) / (2 * τ) = -b * x := by
    field_simp
  have hdiv : (1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2 / (2 * τ) =
      (1 + 2 * a * τ) * x ^ 2 / (2 * τ) - 2 * (-b * τ) * x / (2 * τ) +
        b ^ 2 * τ / (2 * (1 + 2 * a * τ)) := by
    rw [hexp, add_div, sub_div, f3]
  have hdiv2 : -((1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
        (2 * τ) =
      -((1 + 2 * a * τ) * x ^ 2 / (2 * τ)) + -b * x -
        b ^ 2 * τ / (2 * (1 + 2 * a * τ)) := by
    calc -((1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2) / (2 * τ)
        = -(((1 + 2 * a * τ) * (x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
            (2 * τ)) := by rw [neg_div]
      _ = -((1 + 2 * a * τ) * x ^ 2 / (2 * τ) -
            2 * (-b * τ) * x / (2 * τ) +
            b ^ 2 * τ / (2 * (1 + 2 * a * τ))) := by rw [hdiv]
      _ = -((1 + 2 * a * τ) * x ^ 2 / (2 * τ)) + -b * x -
            b ^ 2 * τ / (2 * (1 + 2 * a * τ)) := by
          rw [f4]
          ring
  have hI1 : -(x ^ 2) / (2 * τ) - a * x ^ 2 =
      -((1 + 2 * a * τ) * x ^ 2) / (2 * τ) := by
    field_simp
    ring
  rw [hdiv2, hI1]
  ring

/-- The seat variance at the rectified coordinate is positive:
`0 < τ/(1 + 2aτ)`. -/
lemma seatVariance_pos (τ a : ℝ) (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) :
    0 < τ / (1 + 2 * a * τ) :=
  div_pos hτ hS

/-- **The `v 0` factor's 0th moment.**
`∫ x, seatFactor0 τ a b x = exp (b²τ/(2(1 + 2aτ))) · √(2π · τ/(1 + 2aτ))`. -/
lemma integral_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ))) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (seatFactor0_eq_shifted τ a b hτ hS)), integral_const_mul,
    integral_exp_neg_sq_div_sub _ _ (seatVariance_pos τ a hτ hS)]

/-- **The `v 0` factor's 1st moment.**
`∫ x, x · seatFactor0 τ a b x
  = exp (b²τ/(2(1 + 2aτ))) · (μ · √(2π · τ/(1 + 2aτ)))`,
`μ = −bτ/(1 + 2aτ)`. -/
lemma integral_mul_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, x * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        ((-b * τ / (1 + 2 * a * τ)) *
          Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ)))) := by
  have hpt : ∀ x : ℝ, x * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        (x * Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
          (2 * (τ / (1 + 2 * a * τ))))) := by
    intro x
    rw [seatFactor0_eq_shifted τ a b hτ hS x]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_mul_exp_neg_sq_div_sub _ _ (seatVariance_pos τ a hτ hS)]

/-- **The `v 0` factor's 2nd moment.**
`∫ x, x² · seatFactor0 τ a b x
  = exp (b²τ/(2(1 + 2aτ))) · ((τ/(1 + 2aτ) + μ²) · √(2π · τ/(1 + 2aτ)))`,
`μ = −bτ/(1 + 2aτ)`. -/
lemma integral_sq_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, x ^ 2 * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        ((τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2) *
          Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ)))) := by
  have hpt : ∀ x : ℝ, x ^ 2 * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        (x ^ 2 * Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
          (2 * (τ / (1 + 2 * a * τ))))) := by
    intro x
    rw [seatFactor0_eq_shifted τ a b hτ hS x]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_sq_exp_neg_sq_div_sub _ _ (seatVariance_pos τ a hτ hS)]

/-- The `v 0` factor is integrable under admissibility. -/
lemma integrable_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    Integrable (seatFactor0 τ a b) volume := by
  apply ((integrable_exp_neg_sq_div_sub _ _ (seatVariance_pos τ a hτ hS)).const_mul
    (Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))))).congr
  filter_upwards with x
  rw [seatFactor0_eq_shifted τ a b hτ hS x]

/-- The `v 0` factor times the coordinate is integrable under
admissibility. -/
lemma integrable_mul_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    Integrable (fun x : ℝ => x * seatFactor0 τ a b x) volume := by
  have hpt : ∀ x : ℝ, x * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        (x * Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
          (2 * (τ / (1 + 2 * a * τ))))) := by
    intro x
    rw [seatFactor0_eq_shifted τ a b hτ hS x]
    ring
  apply ((integrable_mul_exp_neg_sq_div_sub (τ / (1 + 2 * a * τ))
    (-b * τ / (1 + 2 * a * τ)) (seatVariance_pos τ a hτ hS)).const_mul
    (Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))))).congr
  filter_upwards with x
  exact (hpt x).symm

/-- The `v 0` factor times the squared coordinate is integrable under
admissibility. -/
lemma integrable_sq_seatFactor0 (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    Integrable (fun x : ℝ => x ^ 2 * seatFactor0 τ a b x) volume := by
  have hpt : ∀ x : ℝ, x ^ 2 * seatFactor0 τ a b x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        (x ^ 2 * Real.exp (-((x - (-b * τ / (1 + 2 * a * τ))) ^ 2) /
          (2 * (τ / (1 + 2 * a * τ))))) := by
    intro x
    rw [seatFactor0_eq_shifted τ a b hτ hS x]
    ring
  apply ((integrable_sq_exp_neg_sq_div_sub (τ / (1 + 2 * a * τ))
    (-b * τ / (1 + 2 * a * τ)) (seatVariance_pos τ a hτ hS)).const_mul
    (Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))))).congr
  filter_upwards with x
  exact (hpt x).symm

/-- The Pi factor of the rectified product: coordinate `0` carries
the completed-square factor, the other coordinates the plain MB
1-D weight. -/
noncomputable def seatFactor (τ a b : ℝ) (j : Fin 3) (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * τ)) *
    (if j = 0 then Real.exp (-(a * x ^ 2 + b * x)) else 1)

/-- At coordinate `0`, the Pi factor is `seatFactor0`. -/
lemma seatFactor_zero (τ a b : ℝ) (x : ℝ) :
    seatFactor τ a b 0 x = seatFactor0 τ a b x := by
  unfold seatFactor seatFactor0
  rw [if_pos rfl, ← Real.exp_add]
  congr 1
  ring

/-- At coordinates other than `0`, the Pi factor is the plain MB
1-D weight. -/
lemma seatFactor_of_ne (τ a b : ℝ) {j : Fin 3} (hj : j ≠ 0) (x : ℝ) :
    seatFactor τ a b j x = Real.exp (-(x ^ 2) / (2 * τ)) := by
  unfold seatFactor
  rw [if_neg hj, mul_one]

/-- The Pi factor's product is the MB weight times the shadow
weight's exponential: completing the square is a `v 0`-only
operation, the other coordinates are untouched. -/
lemma seatFactor_prod (τ a b : ℝ) (v : VelocitySpace) :
    ∏ j, seatFactor τ a b j (v j) =
      Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) *
        Real.exp (-(a * (v 0) ^ 2 + b * (v 0))) := by
  have hsplit : seatFactor0 τ a b (v 0) =
      Real.exp (-((v 0) ^ 2) / (2 * τ)) *
        Real.exp (-(a * (v 0) ^ 2 + b * (v 0))) := by
    unfold seatFactor0
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Fin.prod_univ_three, seatFactor_zero, seatFactor_of_ne τ a b
    (show (1 : Fin 3) ≠ 0 by decide), seatFactor_of_ne τ a b
    (show (2 : Fin 3) ≠ 0 by decide), hsplit, exp_neg_sumSq_eq_prod]
  simp only [Fin.prod_univ_three]
  ring

/-- The unnormalized rectified product, factorized:
`mbDensity τ v · shadowWeight a b c v
  = (2πτ)^(−3/2) · c · ∏ j, seatFactor τ a b j (v j)`. -/
lemma mbDensity_mul_shadowWeight_eq (τ a b c : ℝ) (v : VelocitySpace) :
    mbDensity τ v * shadowWeight a b c v =
      (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
        ∏ j, seatFactor τ a b j (v j) := by
  rw [seatFactor_prod]
  unfold mbDensity shadowWeight
  ring

/-! ## §4. Half A — the master factorization and `partitionZ`

Every integral of the rectified product against a coordinate power
factors over the three coordinates (`integral_fintype_prod_eq_prod`
after `volume_pi`), and every such product is integrable under
admissibility: the 1-D factors are §2/§3's shifted/plain Gaussian
pieces. The partition value is the `k = 0` case, evaluated by the
1-D values. -/

/-- The coordinate-power product over the seat:
`∏ j, (v j)^(if j = i then k else 0) = (v i)^k`. -/
lemma prod_coord_pow (v : VelocitySpace) (i : Fin 3) (k : ℕ) :
    ∏ j, (v j) ^ (if j = i then k else 0) = (v i) ^ k := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg hb, pow_zero]
  · simp

/-- **Master integral.** The rectified product against a coordinate
power, factorized:
`∫ v, (mbDensity τ · shadowWeight a b c) v · (v i)^k
  = (2πτ)^(−3/2) · c · ∏ j, ∫ x, x^(if j = i then k else 0) ·
    seatFactor τ a b j x`. -/
lemma integral_mbDensity_mul_shadowWeight_mul_coord_pow (τ a b c : ℝ)
    (i : Fin 3) (k : ℕ) :
    ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v i) ^ k
        ∂(volume : Measure VelocitySpace) =
      (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
        ∏ j, ∫ x : ℝ, x ^ (if j = i then k else 0) * seatFactor τ a b j x := by
  calc ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v i) ^ k
          ∂(volume : Measure VelocitySpace)
      = ∫ v, (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
            ∏ j, ((v j) ^ (if j = i then k else 0) *
              seatFactor τ a b j (v j)) ∂(volume : Measure VelocitySpace) := by
        apply integral_congr_ae
        filter_upwards with v
        calc (mbDensity τ v * shadowWeight a b c v) * (v i) ^ k
            = ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
                ∏ j, seatFactor τ a b j (v j)) * (v i) ^ k := by
              rw [mbDensity_mul_shadowWeight_eq]
          _ = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
                ∏ j, ((v j) ^ (if j = i then k else 0) *
                  seatFactor τ a b j (v j)) := by
              rw [← prod_coord_pow v i k, Finset.prod_mul_distrib]
              ring
    _ = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
          ∏ j, ∫ x : ℝ, x ^ (if j = i then k else 0) *
            seatFactor τ a b j x := by
        rw [integral_const_mul]
        congr 1
        rw [MeasureTheory.volume_pi]
        exact integral_fintype_prod_eq_prod
          (fun (j : Fin 3) (x : ℝ) => x ^ (if j = i then k else 0) *
            seatFactor τ a b j x)

/-- A coordinate power times a Pi factor is integrable, for powers
`k ≤ 2`, under admissibility: at coordinate `0` these are §3's
shifted pieces, at the other coordinates SE-1's / §2's plain
Gaussian pieces. -/
lemma integrable_pow_mul_seatFactor (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) (j : Fin 3) {k : ℕ} (hk : k ≤ 2) :
    Integrable (fun x : ℝ => x ^ k * seatFactor τ a b j x) volume := by
  by_cases hj0 : j = 0
  · subst hj0
    interval_cases k
    · apply (integrable_seatFactor0 τ a b hτ hS).congr
      filter_upwards with x
      rw [seatFactor_zero, pow_zero, one_mul]
    · apply (integrable_mul_seatFactor0 τ a b hτ hS).congr
      filter_upwards with x
      rw [seatFactor_zero, pow_one]
    · apply (integrable_sq_seatFactor0 τ a b hτ hS).congr
      filter_upwards with x
      rw [seatFactor_zero]
  · interval_cases k
    · apply (integrable_exp_neg_sq_div τ hτ).congr
      filter_upwards with x
      rw [seatFactor_of_ne τ a b hj0, pow_zero, one_mul]
    · apply (integrable_mul_exp_neg_sq_div_seat τ hτ).congr
      filter_upwards with x
      rw [seatFactor_of_ne τ a b hj0, pow_one]
    · apply (integrable_sq_mul_exp_neg_sq_div τ hτ).congr
      filter_upwards with x
      rw [seatFactor_of_ne τ a b hj0]

/-- **Master integrability.** The rectified product against a
coordinate power `k ≤ 2` is integrable under admissibility. The
`k = 0` case is SE-2's first stated hypothesis at the seat. -/
lemma integrable_mbDensity_mul_shadowWeight_mul_coord_pow (τ a b c : ℝ)
    (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) (i : Fin 3) {k : ℕ} (hk : k ≤ 2) :
    Integrable (fun v => (mbDensity τ v * shadowWeight a b c v) * (v i) ^ k)
      (volume : Measure VelocitySpace) := by
  have hprod : Integrable (fun v : VelocitySpace =>
      ∏ j, ((v j) ^ (if j = i then k else 0) * seatFactor τ a b j (v j)))
      (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) := by
    apply Integrable.fintype_prod
      (f := fun (j : Fin 3) (x : ℝ) => x ^ (if j = i then k else 0) *
        seatFactor τ a b j x)
    intro j
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl]
      exact integrable_pow_mul_seatFactor τ a b hτ hS j hk
    · rw [if_neg hji]
      apply (integrable_pow_mul_seatFactor τ a b hτ hS j (k := 0)
        (by norm_num)).congr
      filter_upwards with x
      rw [pow_zero, one_mul]
  rw [MeasureTheory.volume_pi]
  apply (hprod.const_mul ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c)).congr
  filter_upwards with v
  rw [mbDensity_mul_shadowWeight_eq, Finset.prod_mul_distrib,
    ← prod_coord_pow v i k]
  ring

/-- **SE-2's first stated hypothesis, discharged at the seat:**
the unnormalized rectified product is integrable under
admissibility. -/
theorem integrable_mbDensity_mul_shadowWeight (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    Integrable (fun v => mbDensity τ v * shadowWeight a b c v)
      (volume : Measure VelocitySpace) := by
  have h := integrable_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c hτ hS
    (0 : Fin 3) (k := 0) (by norm_num)
  apply h.congr
  filter_upwards with v
  simp

/-- The `v 0` factor integral of the partition product, evaluated:
the `j = 0` factor of `∏ j, ∫ x, x^(if j = 0 then 0 else 0) ·
seatFactor τ a b j x` is §3's 0th moment. -/
lemma factor_integral_zero (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, x ^ (if (0 : Fin 3) = 0 then (0 : ℕ) else 0) *
        seatFactor τ a b 0 x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ))) := by
  rw [if_pos rfl]
  have h : (∫ x : ℝ, x ^ (0 : ℕ) * seatFactor τ a b 0 x) =
      ∫ x : ℝ, seatFactor0 τ a b x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_zero, pow_zero, one_mul]
  rw [h, integral_seatFactor0 τ a b hτ hS]

/-- The plain factor integral of the partition product at
coordinates `j ≠ 0`, evaluated: SE-3's 1-D 0th moment. -/
lemma factor_integral_of_ne (τ a b : ℝ) (hτ : 0 < τ) {j : Fin 3}
    (hj : j ≠ 0) :
    ∫ x : ℝ, x ^ (if j = 0 then (0 : ℕ) else 0) * seatFactor τ a b j x =
      Real.sqrt (2 * Real.pi * τ) := by
  rw [if_neg hj]
  have h : (∫ x : ℝ, x ^ (0 : ℕ) * seatFactor τ a b j x) =
      ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_of_ne τ a b hj, pow_zero, one_mul]
  rw [h, integral_exp_neg_sq_div_value τ hτ]

/-- The ratio of the shifted and unshifted Gaussian roots:
`√(2π · τ/(1 + 2aτ)) = √(2πτ)/√(1 + 2aτ)`. -/
lemma sqrt_shifted_ratio (τ a : ℝ) (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) :
    Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ))) =
      Real.sqrt (2 * Real.pi * τ) / Real.sqrt (1 + 2 * a * τ) := by
  rw [show 2 * Real.pi * (τ / (1 + 2 * a * τ)) =
      (2 * Real.pi * τ) / (1 + 2 * a * τ) by ring,
    Real.sqrt_div (by positivity)]

/-- The real power as the reciprocal root:
`(1 + 2aτ)^(−(1/2)) = 1/√(1 + 2aτ)` for `0 < 1 + 2aτ`. -/
lemma rpow_neg_half_eq (a τ : ℝ) (hS : 0 < 1 + 2 * a * τ) :
    (1 + 2 * a * τ) ^ (-(1 : ℝ) / 2) =
      1 / Real.sqrt (1 + 2 * a * τ) := by
  have hexp : (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) := by ring
  rw [hexp, Real.rpow_neg hS.le, Real.sqrt_eq_rpow]
  exact (one_div _).symm

/-- **Half A, item 1 — the partition function in closed form.**
Under admissibility (`0 < τ`, `0 < 1 + 2aτ`),

`partitionZ τ a b c
  = c * (1 + 2aτ)^(−1/2) * exp (τ * b^2 / (2 * (1 + 2aτ)))`,

the memo §3 closed form (whose exponential is written there as
`exp( b²τ / (2(1 + 2aτ)) )` — the same value). Computed from the
factorized integral: the `v 0` factor contributes §3's shifted 0th
moment, the other two coordinates SE-3's normalization, and the
normalization factor cancels the resulting `√(2πτ)^3` by SE-3's
`norm_factor_mul_sqrt_cube`. -/
theorem partitionZ_eq_closed_form (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    partitionZ τ a b c =
      c * (1 + 2 * a * τ) ^ (-(1 : ℝ) / 2) *
        Real.exp (τ * b ^ 2 / (2 * (1 + 2 * a * τ))) := by
  have hW : (∫ v, mbDensity τ v * shadowWeight a b c v
        ∂(volume : Measure VelocitySpace)) =
      ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v 0) ^ 0
        ∂(volume : Measure VelocitySpace) := by
    apply integral_congr_ae
    filter_upwards with v
    simp
  have hsqrt_ne : Real.sqrt (1 + 2 * a * τ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hS)
  have hexp : Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) =
      Real.exp (τ * b ^ 2 / (2 * (1 + 2 * a * τ))) := by
    congr 1
    ring
  unfold partitionZ
  rw [hW, integral_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c 0 0,
    Fin.prod_univ_three, factor_integral_zero τ a b hτ hS,
    factor_integral_of_ne τ a b hτ (show (1 : Fin 3) ≠ 0 by decide),
    factor_integral_of_ne τ a b hτ (show (2 : Fin 3) ≠ 0 by decide),
    sqrt_shifted_ratio τ a hτ hS]
  calc (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
        (Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
          (Real.sqrt (2 * Real.pi * τ) / Real.sqrt (1 + 2 * a * τ)) *
          Real.sqrt (2 * Real.pi * τ) * Real.sqrt (2 * Real.pi * τ))
      = c * Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
          ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
            (Real.sqrt (2 * Real.pi * τ)) ^ 3) /
            Real.sqrt (1 + 2 * a * τ) := by
        field_simp
    _ = c * Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) /
          Real.sqrt (1 + 2 * a * τ) := by
        rw [norm_factor_mul_sqrt_cube τ hτ, mul_one]
    _ = c * (1 + 2 * a * τ) ^ (-(1 : ℝ) / 2) *
          Real.exp (τ * b ^ 2 / (2 * (1 + 2 * a * τ))) := by
        rw [hexp, rpow_neg_half_eq a τ hS]
        field_simp

/-- **Half A, item 3 — positivity of the partition value.**
`0 < partitionZ τ a b c` at admissible seats with `0 < c`: the
`hZ` package `rectifiedDensity` consumes, read off the closed
form. -/
theorem partitionZ_pos (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hS : 0 < 1 + 2 * a * τ) :
    0 < partitionZ τ a b c := by
  rw [partitionZ_eq_closed_form τ a b c hτ hS]
  exact mul_pos (mul_pos hc (Real.rpow_pos_of_pos hS _)) (Real.exp_pos _)

/-- The partition value in factored form — the form the moment
computations consume:
`partitionZ τ a b c = (2πτ)^(−3/2) · c · (exp (b²τ/(2(1 + 2aτ))) ·
√(2π · τ/(1 + 2aτ)) · √(2πτ) · √(2πτ))`. -/
theorem partitionZ_eq_factored (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    partitionZ τ a b c =
      (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * c *
        (Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
          Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ))) *
          Real.sqrt (2 * Real.pi * τ) * Real.sqrt (2 * Real.pi * τ)) := by
  have hW : (∫ v, mbDensity τ v * shadowWeight a b c v
        ∂(volume : Measure VelocitySpace)) =
      ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v 0) ^ 0
        ∂(volume : Measure VelocitySpace) := by
    apply integral_congr_ae
    filter_upwards with v
    simp
  unfold partitionZ
  rw [hW, integral_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c 0 0,
    Fin.prod_univ_three, factor_integral_zero τ a b hτ hS,
    factor_integral_of_ne τ a b hτ (show (1 : Fin 3) ≠ 0 by decide),
    factor_integral_of_ne τ a b hτ (show (2 : Fin 3) ≠ 0 by decide)]

/-! ## §5. The rectified moments

The factor evaluations behind the moments: at the `v 0` coordinate
the shifted factor's first two moments (§3), at the other
coordinates the plain Gaussian moments (SE-3). -/

/-- Factor evaluation: the `v 0` factor against the first power. -/
lemma factor_integral_zero_one (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, x ^ (if (0 : Fin 3) = 0 then (1 : ℕ) else 0) *
        seatFactor τ a b 0 x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        ((-b * τ / (1 + 2 * a * τ)) *
          Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ)))) := by
  rw [if_pos rfl]
  have h : (∫ x : ℝ, x ^ (1 : ℕ) * seatFactor τ a b 0 x) =
      ∫ x : ℝ, x * seatFactor0 τ a b x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_zero, pow_one]
  rw [h, integral_mul_seatFactor0 τ a b hτ hS]

/-- Factor evaluation: the `v 0` factor against the second power. -/
lemma factor_integral_zero_two (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) :
    ∫ x : ℝ, x ^ (if (0 : Fin 3) = 0 then (2 : ℕ) else 0) *
        seatFactor τ a b 0 x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        ((τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2) *
          Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ)))) := by
  rw [if_pos rfl]
  have h : (∫ x : ℝ, x ^ (2 : ℕ) * seatFactor τ a b 0 x) =
      ∫ x : ℝ, x ^ 2 * seatFactor0 τ a b x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_zero]
  rw [h, integral_sq_seatFactor0 τ a b hτ hS]

/-- Factor evaluation: a plain factor at `j ≠ i`, any power — the
exponent collapses to `0` and SE-3's 0th moment remains. -/
lemma factor_integral_ne_pow (τ a b : ℝ) (hτ : 0 < τ) {j i : Fin 3}
    (hji : j ≠ i) (hj0 : j ≠ 0) (m : ℕ) :
    ∫ x : ℝ, x ^ (if j = i then m else 0) * seatFactor τ a b j x =
      Real.sqrt (2 * Real.pi * τ) := by
  rw [if_neg hji]
  have h : (∫ x : ℝ, x ^ (0 : ℕ) * seatFactor τ a b j x) =
      ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_of_ne τ a b hj0, pow_zero, one_mul]
  rw [h, integral_exp_neg_sq_div_value τ hτ]

/-- Factor evaluation: the `v 0` factor at power `0` seen from a
moment at another coordinate — §3's 0th moment. -/
lemma factor_integral_zero_of_ne (τ a b : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) {i : Fin 3} (hi : i ≠ 0) (m : ℕ) :
    ∫ x : ℝ, x ^ (if (0 : Fin 3) = i then m else 0) *
        seatFactor τ a b 0 x =
      Real.exp (b ^ 2 * τ / (2 * (1 + 2 * a * τ))) *
        Real.sqrt (2 * Real.pi * (τ / (1 + 2 * a * τ))) := by
  rw [if_neg (fun h => hi h.symm)]
  have h : (∫ x : ℝ, x ^ (0 : ℕ) * seatFactor τ a b 0 x) =
      ∫ x : ℝ, seatFactor0 τ a b x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_zero, pow_zero, one_mul]
  rw [h, integral_seatFactor0 τ a b hτ hS]

/-- Factor evaluation: the plain factor at its own coordinate
against the second power — SE-3's 1-D second moment. -/
lemma factor_integral_self_two (τ a b : ℝ) (hτ : 0 < τ) {i : Fin 3}
    (hi : i ≠ 0) :
    ∫ x : ℝ, x ^ (if i = i then (2 : ℕ) else 0) * seatFactor τ a b i x =
      τ * Real.sqrt (2 * Real.pi * τ) := by
  rw [if_pos rfl]
  have h : (∫ x : ℝ, x ^ (2 : ℕ) * seatFactor τ a b i x) =
      ∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / (2 * τ)) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [seatFactor_of_ne τ a b hi]
  rw [h, integral_sq_mul_exp_neg_sq_div_value τ hτ]

/-- **Unnormalized first moment at `v 0`.**
`∫ v, (mbDensity τ · shadowWeight a b c) v · (v 0)
  = partitionZ τ a b c · (−bτ/(1 + 2aτ))`. -/
theorem integral_mbDensity_mul_shadowWeight_mul_coord (τ a b c : ℝ)
    (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) :
    ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v 0)
        ∂(volume : Measure VelocitySpace) =
      partitionZ τ a b c * (-b * τ / (1 + 2 * a * τ)) := by
  have hpt : ∀ v : VelocitySpace,
      (mbDensity τ v * shadowWeight a b c v) * (v 0) =
        (mbDensity τ v * shadowWeight a b c v) * (v 0) ^ 1 := by
    intro v
    rw [pow_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c 0 1,
    Fin.prod_univ_three, factor_integral_zero_one τ a b hτ hS,
    factor_integral_ne_pow τ a b hτ (show (1 : Fin 3) ≠ 0 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) 1,
    factor_integral_ne_pow τ a b hτ (show (2 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) 1,
    partitionZ_eq_factored τ a b c hτ hS]
  ring

/-- **Unnormalized second moment at `v 0`.**
`∫ v, (mbDensity τ · shadowWeight a b c) v · (v 0)^2
  = partitionZ τ a b c · (τ/(1 + 2aτ) + (−bτ/(1 + 2aτ))^2)`. -/
theorem integral_mbDensity_mul_shadowWeight_mul_coord_sq_zero (τ a b c : ℝ)
    (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) :
    ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v 0) ^ 2
        ∂(volume : Measure VelocitySpace) =
      partitionZ τ a b c *
        (τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2) := by
  rw [integral_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c 0 2,
    Fin.prod_univ_three, factor_integral_zero_two τ a b hτ hS,
    factor_integral_ne_pow τ a b hτ (show (1 : Fin 3) ≠ 0 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) 2,
    factor_integral_ne_pow τ a b hτ (show (2 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) 2,
    partitionZ_eq_factored τ a b c hτ hS]
  ring

/-- **Unnormalized second moment at the other coordinates.**
For `i ≠ 0`,
`∫ v, (mbDensity τ · shadowWeight a b c) v · (v i)^2
  = partitionZ τ a b c · τ`. -/
theorem integral_mbDensity_mul_shadowWeight_mul_coord_sq_of_ne (τ a b c : ℝ)
    (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ) {i : Fin 3} (hi : i ≠ 0) :
    ∫ v, (mbDensity τ v * shadowWeight a b c v) * (v i) ^ 2
        ∂(volume : Measure VelocitySpace) =
      partitionZ τ a b c * τ := by
  have hval : i.val = 1 ∨ i.val = 2 := by
    have hlt : i.val < 3 := i.2
    have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  rw [integral_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c i 2,
    Fin.prod_univ_three, factor_integral_zero_of_ne τ a b hτ hS hi 2,
    partitionZ_eq_factored τ a b c hτ hS]
  rcases hval with h | h
  · have hi1 : i = 1 := Fin.ext h
    subst hi1
    rw [factor_integral_self_two τ a b hτ (show (1 : Fin 3) ≠ 0 by decide),
      factor_integral_ne_pow τ a b hτ (show (2 : Fin 3) ≠ 1 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) 2]
    ring
  · have hi2 : i = 2 := Fin.ext h
    subst hi2
    rw [factor_integral_ne_pow τ a b hτ (show (1 : Fin 3) ≠ 2 by decide)
        (show (1 : Fin 3) ≠ 0 by decide) 2,
      factor_integral_self_two τ a b hτ (show (2 : Fin 3) ≠ 0 by decide)]
    ring

/-- The rectified density is normalized: `∫ v, rectifiedDensity
τ a b c hZ v = 1` at admissible seats. -/
theorem integral_rectifiedDensity (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    ∫ v, rectifiedDensity τ a b c hZ v ∂(volume : Measure VelocitySpace) =
      1 := by
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v =
      (mbDensity τ v * shadowWeight a b c v) / partitionZ τ a b c := fun v => rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div]
  exact div_self (ne_of_gt hZ)

/-- **Rectified first moment (the seat's mean).**
`∫ v, rectifiedDensity τ a b c hZ v · (v 0) = −bτ/(1 + 2aτ)`. -/
theorem integral_rectifiedDensity_mul_coord (τ a b c : ℝ) (hτ : 0 < τ)
    (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    ∫ v, rectifiedDensity τ a b c hZ v * (v 0)
        ∂(volume : Measure VelocitySpace) =
      -b * τ / (1 + 2 * a * τ) := by
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v * (v 0) =
      ((mbDensity τ v * shadowWeight a b c v) * (v 0)) /
        partitionZ τ a b c := by
    intro v
    unfold rectifiedDensity
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_mbDensity_mul_shadowWeight_mul_coord τ a b c hτ hS,
    mul_div_cancel_left₀ _ (ne_of_gt hZ)]

/-- **Rectified second moment at `v 0`.**
`∫ v, rectifiedDensity τ a b c hZ v · (v 0)^2
  = τ/(1 + 2aτ) + (−bτ/(1 + 2aτ))^2` — variance `τ/(1 + 2aτ)` plus
the squared mean. -/
theorem integral_rectifiedDensity_mul_coord_sq_zero (τ a b c : ℝ)
    (hτ : 0 < τ) (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    ∫ v, rectifiedDensity τ a b c hZ v * (v 0) ^ 2
        ∂(volume : Measure VelocitySpace) =
      τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2 := by
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v * (v 0) ^ 2 =
      ((mbDensity τ v * shadowWeight a b c v) * (v 0) ^ 2) /
        partitionZ τ a b c := by
    intro v
    unfold rectifiedDensity
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_mbDensity_mul_shadowWeight_mul_coord_sq_zero τ a b c hτ hS,
    mul_div_cancel_left₀ _ (ne_of_gt hZ)]

/-- **Rectified second moment at the other coordinates.** For
`i ≠ 0`, `∫ v, rectifiedDensity τ a b c hZ v · (v i)^2 = τ`:
rectification does not touch those coordinates' variance. -/
theorem integral_rectifiedDensity_mul_coord_sq_of_ne (τ a b c : ℝ)
    (hτ : 0 < τ) (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) {i : Fin 3} (hi : i ≠ 0) :
    ∫ v, rectifiedDensity τ a b c hZ v * (v i) ^ 2
        ∂(volume : Measure VelocitySpace) = τ := by
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v * (v i) ^ 2 =
      ((mbDensity τ v * shadowWeight a b c v) * (v i) ^ 2) /
        partitionZ τ a b c := by
    intro v
    unfold rectifiedDensity
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_mbDensity_mul_shadowWeight_mul_coord_sq_of_ne τ a b c hτ hS hi,
    mul_div_cancel_left₀ _ (ne_of_gt hZ)]

/-! ## §6. Half A, item 2 — SE-2's stated hypotheses, discharged

The three integrability facts SE-2's seat corollary carries as
hypotheses are proved at the admissible seats from the Gaussian
domination the closed-form computation already develops: the
rectified density is a constant multiple of the rectified product,
whose coordinate powers are integrable (§4), and both logarithms
are affine in the coordinates' powers (`log_mbDensity` of SE-1;
`log_shadowWeight` below). -/

/-- The logarithm of the shadow weight is affine in the `v 0`
coordinate: `log (shadowWeight a b c v)
  = log c − (a·(v 0)^2 + b·(v 0))` for `0 < c`. -/
lemma log_shadowWeight (a b c : ℝ) (hc : 0 < c) (v : VelocitySpace) :
    Real.log (shadowWeight a b c v) =
      Real.log c - (a * (v 0) ^ 2 + b * (v 0)) := by
  unfold shadowWeight
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)), Real.log_exp,
    sub_eq_add_neg]

/-- The rectified density itself is integrable at admissible seats
(a constant multiple of the integrable rectified product). -/
lemma integrable_rectifiedDensity (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    Integrable (rectifiedDensity τ a b c hZ)
      (volume : Measure VelocitySpace) := by
  apply ((integrable_mbDensity_mul_shadowWeight τ a b c hτ hS).const_mul
    (partitionZ τ a b c)⁻¹).congr
  filter_upwards with v
  show (partitionZ τ a b c)⁻¹ * (mbDensity τ v * shadowWeight a b c v) =
    rectifiedDensity τ a b c hZ v
  unfold rectifiedDensity
  rw [div_eq_mul_inv]
  ring

/-- The rectified density against a coordinate power `k ≤ 2` is
integrable at admissible seats. -/
lemma integrable_rectifiedDensity_mul_coord_pow (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) (i : Fin 3)
    {k : ℕ} (hk : k ≤ 2) :
    Integrable (fun v => rectifiedDensity τ a b c hZ v * (v i) ^ k)
      (volume : Measure VelocitySpace) := by
  apply ((integrable_mbDensity_mul_shadowWeight_mul_coord_pow τ a b c hτ hS i
    hk).const_mul (partitionZ τ a b c)⁻¹).congr
  filter_upwards with v
  show (partitionZ τ a b c)⁻¹ * ((mbDensity τ v * shadowWeight a b c v) *
      (v i) ^ k) = rectifiedDensity τ a b c hZ v * (v i) ^ k
  unfold rectifiedDensity
  rw [div_eq_mul_inv]
  ring

/-- **SE-2's second stated hypothesis, discharged:**
`rectifiedDensity · log (mbDensity τ)` is integrable at admissible
seats — `log p` is affine in the squared norm (SE-1), and the
rectified second moment is integrable (§4/§5). -/
theorem integrable_rectifiedDensity_mul_log_mbDensity (τ a b c : ℝ)
    (hτ : 0 < τ) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    Integrable (fun v => rectifiedDensity τ a b c hZ v *
        Real.log (mbDensity τ v)) (volume : Measure VelocitySpace) := by
  have hq : Integrable (rectifiedDensity τ a b c hZ)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity τ a b c hτ hS hZ
  have hsum : Integrable (fun v => rectifiedDensity τ a b c hZ v *
      (∑ i, (v i) ^ 2)) (volume : Measure VelocitySpace) := by
    have h : Integrable (fun v => ∑ i, rectifiedDensity τ a b c hZ v *
        (v i) ^ 2) (volume : Measure VelocitySpace) :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ i
          (by norm_num : (2 : ℕ) ≤ 2))
    apply h.congr
    filter_upwards with v
    rw [Finset.mul_sum]
  apply ((hq.const_mul (Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)))).sub
    (hsum.const_mul (1 / (2 * τ)))).congr
  filter_upwards with v
  simp only [Pi.sub_apply]
  rw [log_mbDensity τ hτ v]
  ring

/-- **SE-2's third stated hypothesis, discharged:**
`rectifiedDensity · log (shadowWeight a b c)` is integrable at
admissible seats — `log w` is affine in the `v 0` coordinate's
powers (`log_shadowWeight`), and the rectified moments are
integrable (§4/§5). -/
theorem integrable_rectifiedDensity_mul_log_shadowWeight (τ a b c : ℝ)
    (hτ : 0 < τ) (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    Integrable (fun v => rectifiedDensity τ a b c hZ v *
        Real.log (shadowWeight a b c v)) (volume : Measure VelocitySpace) := by
  have hq : Integrable (rectifiedDensity τ a b c hZ)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity τ a b c hτ hS hZ
  have hsq : Integrable (fun v => rectifiedDensity τ a b c hZ v * (v 0) ^ 2)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ 0
      (by norm_num : (2 : ℕ) ≤ 2)
  have hone : Integrable (fun v => rectifiedDensity τ a b c hZ v * (v 0) ^ 1)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ 0
      (by norm_num : (1 : ℕ) ≤ 2)
  apply (((hq.const_mul (Real.log c)).sub (hsq.const_mul a)).sub
    (hone.const_mul b)).congr
  filter_upwards with v
  simp only [Pi.sub_apply]
  rw [log_shadowWeight a b c hc v]
  ring

/-- **Half A closed — the corrected weight identity at the seat,
unconditional.** SE-2's `shadow_weight_identity` at the
Maxwell–Boltzmann / shadow-weight seat, with all three of its
integrability hypotheses discharged by the lemmas above under
admissibility. This converts the seat corollary from conditional
to usable. -/
theorem shadow_weight_identity_seat (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    diffEntropy (rectifiedDensity τ a b c hZ) - diffEntropy (mbDensity τ) =
      Real.log (partitionZ τ a b c) -
        expectationDensity (rectifiedDensity τ a b c hZ)
          (fun v => Real.log (shadowWeight a b c v)) +
          (expectationDensity (mbDensity τ) (fun v => Real.log (mbDensity τ v)) -
            expectationDensity (rectifiedDensity τ a b c hZ)
              (fun v => Real.log (mbDensity τ v))) :=
  shadow_weight_identity τ a b c hτ hc hZ
    (integrable_mbDensity_mul_shadowWeight τ a b c hτ hS)
    (integrable_rectifiedDensity_mul_log_mbDensity τ a b c hτ hS hZ)
    (integrable_rectifiedDensity_mul_log_shadowWeight τ a b c hτ hc hS hZ)

/-- **Rectified total second moment.**
`∫ v, rectifiedDensity τ a b c hZ v · (∑ i, (v i)^2)
  = τ/(1 + 2aτ) + (−bτ/(1 + 2aτ))^2 + 2τ`: the `v 0` variance plus
squared mean, plus `τ` from each untouched coordinate. -/
theorem integral_rectifiedDensity_mul_sumSq (τ a b c : ℝ) (hτ : 0 < τ)
    (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    ∫ v, rectifiedDensity τ a b c hZ v * (∑ i, (v i) ^ 2)
        ∂(volume : Measure VelocitySpace) =
      τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2 + 2 * τ := by
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v *
      (∑ i, (v i) ^ 2) =
      ∑ i, rectifiedDensity τ a b c hZ v * (v i) ^ 2 := by
    intro v
    rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ i
        (by norm_num : (2 : ℕ) ≤ 2)),
    Fin.sum_univ_three,
    integral_rectifiedDensity_mul_coord_sq_zero τ a b c hτ hc hS hZ,
    integral_rectifiedDensity_mul_coord_sq_of_ne τ a b c hτ hc hS hZ
      (show (1 : Fin 3) ≠ 0 by decide),
    integral_rectifiedDensity_mul_coord_sq_of_ne τ a b c hτ hc hS hZ
      (show (2 : Fin 3) ≠ 0 by decide)]
  ring

/-- The rectified density against the total squared norm is
integrable at admissible seats. -/
lemma integrable_rectifiedDensity_mul_sumSq (τ a b c : ℝ) (hτ : 0 < τ)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    Integrable (fun v => rectifiedDensity τ a b c hZ v *
      (∑ i, (v i) ^ 2)) (volume : Measure VelocitySpace) := by
  have h : Integrable (fun v => ∑ i, rectifiedDensity τ a b c hZ v *
      (v i) ^ 2) (volume : Measure VelocitySpace) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ i
        (by norm_num : (2 : ℕ) ≤ 2))
  apply h.congr
  filter_upwards with v
  rw [Finset.mul_sum]

/-! ## §7. Half B — H2, the shift identity

Assembly route (the pack's): SE-2's corrected identity at the seat
(`shadow_weight_identity_seat`, §6) — `log Z` from Half A's closed
form, `E_q[log w]` from the rectified moments of §5, and the cross
term `(E_p − E_q)[log p]` from SE-3's base value and the rectified
total second moment. The three expectation values are computed
first; the cancellation of the `b`- and `c`-dependence is then
exhibited as named steps in the assembly. -/

/-- **`E_q[log w]`, computed.** Against the rectified density,
`E_q[log (shadowWeight a b c)]
  = log c − a·(τ/(1 + 2aτ) + μ²) − b·μ`, `μ = −bτ/(1 + 2aτ)`:
`log w` is affine in `(v 0)^2` and `v 0` (`log_shadowWeight`), and
the rectified moments are §5's. -/
theorem expectationDensity_rectifiedDensity_log_shadowWeight (τ a b c : ℝ)
    (hτ : 0 < τ) (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    expectationDensity (rectifiedDensity τ a b c hZ)
        (fun v => Real.log (shadowWeight a b c v)) =
      Real.log c - a * (τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2) -
        b * (-b * τ / (1 + 2 * a * τ)) := by
  have hq : Integrable (rectifiedDensity τ a b c hZ)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity τ a b c hτ hS hZ
  have hsq : Integrable (fun v => rectifiedDensity τ a b c hZ v * (v 0) ^ 2)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ 0
      (by norm_num : (2 : ℕ) ≤ 2)
  have hone : Integrable (fun v => rectifiedDensity τ a b c hZ v * (v 0))
      (volume : Measure VelocitySpace) := by
    apply (integrable_rectifiedDensity_mul_coord_pow τ a b c hτ hS hZ 0
      (by norm_num : (1 : ℕ) ≤ 2)).congr
    filter_upwards with v
    rw [pow_one]
  have hAB : Integrable (fun v => Real.log c * rectifiedDensity τ a b c hZ v -
      a * (rectifiedDensity τ a b c hZ v * (v 0) ^ 2))
      (volume : Measure VelocitySpace) :=
    (hq.const_mul _).sub (hsq.const_mul a)
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v *
      Real.log (shadowWeight a b c v) =
      Real.log c * rectifiedDensity τ a b c hZ v -
        a * (rectifiedDensity τ a b c hZ v * (v 0) ^ 2) -
          b * (rectifiedDensity τ a b c hZ v * (v 0)) := by
    intro v
    rw [log_shadowWeight a b c hc v]
    ring
  unfold expectationDensity
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub hAB (hone.const_mul b),
    integral_sub (hq.const_mul _) (hsq.const_mul a),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_rectifiedDensity τ a b c hτ hc hS hZ,
    integral_rectifiedDensity_mul_coord_sq_zero τ a b c hτ hc hS hZ,
    integral_rectifiedDensity_mul_coord τ a b c hτ hc hS hZ]
  ring

/-- **`E_p[log p]`, SE-3's value in `log C` form.**
`E_p[log (mbDensity τ)] = log ((2πτ)^(−3/2)) − 3/2`. -/
theorem expectationDensity_mbDensity_log_mbDensity (τ : ℝ) (hτ : 0 < τ) :
    expectationDensity (mbDensity τ) (fun v => Real.log (mbDensity τ v)) =
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) - 3 / 2 := by
  have h : expectationDensity (mbDensity τ)
        (fun v => Real.log (mbDensity τ v)) =
      -(3 / 2 : ℝ) * Real.log (2 * Real.pi * τ) - 3 / 2 :=
    integral_mbDensity_mul_log_value τ hτ
  rw [h, Real.log_rpow (by positivity : (0 : ℝ) < 2 * Real.pi * τ)]
  ring

/-- **`E_q[log p]`, computed.** Against the rectified density,
`E_q[log (mbDensity τ)]
  = log ((2πτ)^(−3/2)) − (τ/(1 + 2aτ) + μ² + 2τ)/(2τ)`:
`log p` is affine in the squared norm (SE-1), and the rectified
total second moment is §6's. -/
theorem expectationDensity_rectifiedDensity_log_mbDensity (τ a b c : ℝ)
    (hτ : 0 < τ) (hc : 0 < c) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    expectationDensity (rectifiedDensity τ a b c hZ)
        (fun v => Real.log (mbDensity τ v)) =
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) -
        (τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2 + 2 * τ) /
          (2 * τ) := by
  have hq : Integrable (rectifiedDensity τ a b c hZ)
      (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity τ a b c hτ hS hZ
  have hsum : Integrable (fun v => rectifiedDensity τ a b c hZ v *
      (∑ i, (v i) ^ 2)) (volume : Measure VelocitySpace) :=
    integrable_rectifiedDensity_mul_sumSq τ a b c hτ hS hZ
  have hA : Integrable (fun v =>
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) *
          rectifiedDensity τ a b c hZ v -
        (1 / (2 * τ)) * (rectifiedDensity τ a b c hZ v * (∑ i, (v i) ^ 2)))
      (volume : Measure VelocitySpace) :=
    (hq.const_mul _).sub (hsum.const_mul _)
  have hpt : ∀ v : VelocitySpace, rectifiedDensity τ a b c hZ v *
      Real.log (mbDensity τ v) =
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) *
          rectifiedDensity τ a b c hZ v -
        (1 / (2 * τ)) * (rectifiedDensity τ a b c hZ v *
          (∑ i, (v i) ^ 2)) := by
    intro v
    rw [log_mbDensity τ hτ v]
    ring
  unfold expectationDensity
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (hq.const_mul _) (hsum.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_rectifiedDensity τ a b c hτ hc hS hZ,
    integral_rectifiedDensity_mul_sumSq τ a b c hτ hc hS hZ]
  ring

/-- **`log Z`, from Half A's closed form.**
`log (partitionZ τ a b c)
  = log c − (1/2)·log (1 + 2aτ) + b^2·τ/(2(1 + 2aτ))`. The three
summands are the three places the assembly's cancellations act:
`log c` against `E_q[log w]`'s `log c`, the shift term itself,
and the `b^2` term against `E_q[log w]`'s moment terms. -/
theorem log_partitionZ (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hS : 0 < 1 + 2 * a * τ) :
    Real.log (partitionZ τ a b c) =
      Real.log c - (1 / 2 : ℝ) * Real.log (1 + 2 * a * τ) +
        b ^ 2 * τ / (2 * (1 + 2 * a * τ)) := by
  have h1 : c * (1 + 2 * a * τ) ^ (-(1 : ℝ) / 2) ≠ 0 :=
    mul_ne_zero (ne_of_gt hc) (ne_of_gt (Real.rpow_pos_of_pos hS _))
  have h2 : Real.exp (τ * b ^ 2 / (2 * (1 + 2 * a * τ))) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  rw [partitionZ_eq_closed_form τ a b c hτ hS, Real.log_mul h1 h2,
    Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.rpow_pos_of_pos hS _)),
    Real.log_rpow hS, Real.log_exp]
  ring

/-- **The cross term, evaluated.** `(E_p − E_q)[log p]
  = −3/2 + (τ/(1 + 2aτ) + μ² + 2τ)/(2τ)`: the `log C` of the base
density cancels between the two expectations — the first
cancellation of the assembly, recorded here. -/
theorem cross_term_value (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hS : 0 < 1 + 2 * a * τ) (hZ : 0 < partitionZ τ a b c) :
    expectationDensity (mbDensity τ) (fun v => Real.log (mbDensity τ v)) -
        expectationDensity (rectifiedDensity τ a b c hZ)
          (fun v => Real.log (mbDensity τ v)) =
      -3 / 2 + (τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2 +
        2 * τ) / (2 * τ) := by
  rw [expectationDensity_mbDensity_log_mbDensity τ hτ,
    expectationDensity_rectifiedDensity_log_mbDensity τ a b c hτ hc hS hZ]
  ring

/-- **Half B — H2, the seat identity (memo §5, verbatim).** Under
admissibility (`0 < τ`, `0 < c ≤ 1`, `0 < 1 + 2aτ`) and the
packaged `0 < Z` witness,

`diffEntropy (rectifiedDensity τ a b c hZ) − diffEntropy (mbDensity τ)
  = −(1/2) · log (1 + 2aτ)`.

Assembly: SE-2's corrected identity at the seat
(`shadow_weight_identity_seat`) with `log Z`
(`log_partitionZ`), `E_q[log w]`
(`expectationDensity_rectifiedDensity_log_shadowWeight`), and the
cross term (`cross_term_value`) substituted. The remaining scalar
identity is exactly the three named cancellation steps:

- `step_cancel_c`: the filter's `log c` in `log Z` cancels the
  `log c` in `E_q[log w]` — the constant filter `c` contributes
  nothing (K-SE-3: no shift from `c` alone; this step is the
  exhibited reason at this seat);
- `step_cancel_b`: the `b^2τ/(2(1 + 2aτ))` of `log Z` cancels the
  mean-carrying terms of `E_q[log w]` and the cross term —
  `b·μ + μ²·(a + 1/(2τ))` with `μ = −bτ/(1 + 2aτ)` — the asymmetry
  `b` contributes nothing (K-SE-3: no shift from `b` alone; this
  step is the exhibited reason at this seat, and the mechanism
  SE-5's H3b verdict rests on);
- `step_curvature_balance`: the curvature terms balance the
  constants: `a·(τ/(1 + 2aτ)) + (τ/(1 + 2aτ))/(2τ) = 1/2` against
  the cross term's `−3/2 + 1`.

What survives the three cancellations is `−(1/2)·log (1 + 2aτ)`
and nothing else — the value the computation produces is the
registered one (K-SE-2). -/
theorem diffEntropy_rectifiedDensity_sub (τ a b c : ℝ) (hτ : 0 < τ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : 0 < 1 + 2 * a * τ)
    (hZ : 0 < partitionZ τ a b c) :
    diffEntropy (rectifiedDensity τ a b c hZ) - diffEntropy (mbDensity τ) =
      -(1 / 2 : ℝ) * Real.log (1 + 2 * a * τ) := by
  have hS0 : (1 + 2 * a * τ) ≠ 0 := ne_of_gt hS
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have step_cancel_c : Real.log c - Real.log c = 0 := sub_self _
  have step_cancel_b : b ^ 2 * τ / (2 * (1 + 2 * a * τ)) +
        a * (-b * τ / (1 + 2 * a * τ)) ^ 2 +
        (-b * τ / (1 + 2 * a * τ)) ^ 2 / (2 * τ) +
        b * (-b * τ / (1 + 2 * a * τ)) = 0 := by
    field_simp
    ring
  have step_curvature_balance : a * (τ / (1 + 2 * a * τ)) +
        (τ / (1 + 2 * a * τ)) / (2 * τ) - 3 / 2 + (2 * τ) / (2 * τ) = 0 := by
    have e1 : (τ / (1 + 2 * a * τ)) / (2 * τ) =
        1 / (2 * (1 + 2 * a * τ)) := by
      field_simp
    have e2 : (2 * τ) / (2 * τ) = 1 :=
      div_self (mul_ne_zero (by norm_num) hτ0)
    have e3 : a * (τ / (1 + 2 * a * τ)) + 1 / (2 * (1 + 2 * a * τ)) =
        1 / 2 := by
      have h1 : a * (τ / (1 + 2 * a * τ)) =
          (2 * a * τ) / (2 * (1 + 2 * a * τ)) := by
        field_simp
      rw [h1, ← add_div, show (2 * a * τ + 1) = 1 + 2 * a * τ by ring,
        div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hS0)]
      ring
    rw [e1, e2]
    linarith [e3]
  have hsplit : (τ / (1 + 2 * a * τ) + (-b * τ / (1 + 2 * a * τ)) ^ 2 +
        2 * τ) / (2 * τ) =
      (τ / (1 + 2 * a * τ)) / (2 * τ) +
        (-b * τ / (1 + 2 * a * τ)) ^ 2 / (2 * τ) + (2 * τ) / (2 * τ) := by
    rw [add_div, add_div]
  rw [shadow_weight_identity_seat τ a b c hτ hc hS hZ,
    log_partitionZ τ a b c hτ hc hS,
    expectationDensity_rectifiedDensity_log_shadowWeight τ a b c hτ hc hS hZ,
    cross_term_value τ a b c hτ hc hS hZ, hsplit]
  linear_combination step_cancel_c + step_cancel_b + step_curvature_balance

/-- **H2 discharged.** SE-0 registered `shadowEntropyH2` against
an explicit signature parameter; substituting SE-1's `diffEntropy`
for that parameter (the substitution the SE-0/SE-1 headers name),
the registered target holds: this is `shadowEntropyH2 diffEntropy`
itself, proved by `diffEntropy_rectifiedDensity_sub` under exactly
the registered hypotheses (`0 < τ`, `0 < c ≤ 1`, `0 < 1 + 2aτ`, and
the packaged `0 < Z` witness, which `partitionZ_pos` supplies at
every admissible seat). -/
theorem shadowEntropyH2_holds : shadowEntropyH2 diffEntropy := by
  intro τ a b c hτ hc hc1 hS hZ
  exact diffEntropy_rectifiedDensity_sub τ a b c hτ hc hc1 hS hZ

end ThetLogos
