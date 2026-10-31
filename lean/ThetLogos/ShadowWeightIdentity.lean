import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ThetLogos.DiffEntropy

/-!
# ThetLogos.ShadowWeightIdentity — SE-2: the corrected weight identity

**Status: IDENTITY BRICK. NO CLAIM. No Millennium statement, no ladder
rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing pack:
`routeb-general-scratch/pack-se-2.md`; governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md` §2.
Gate SE-1 is landed (`ThetLogos.DiffEntropy`: `diffEntropy`,
`diffEntropyOn`, translation invariance, product additivity,
`integrable_mbDensity_mul_log`), and SE-0 registered the arena
(`mbDensity`, `shadowWeight`, `partitionZ`, `rectifiedDensity`).

## The identity built here (memo §2's corrected form)

The first-quoted candidate identity handed to scoping was FALSE and
was killed at scoping (memo §2): it omits the cross term
`(E_p − E_q)[log p]`. This brick builds ONLY the corrected form.
For a probability density `p`, a weight `w`, `Z = ∫ p·w` with
`0 < Z`, and the normalized weighted density `q = p·w/Z`:

`h(q) − h(p) = log Z − E_q[log w] + (E_p − E_q)[log p]
             = −D(q‖p) + (E_p − E_q)[log p]`,

with `D(q‖p) = E_q[log w] − log Z` the KL term. The KL route is
defined in this module at the level of density integrals
(`klDivDensity`, `weightKLDiv`): the pin's measure-level `klDiv`
(`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`) is
ENNReal-valued between measures and does not unfold to the real
density-integral form the seat consumes, so it is recorded here as
a cross-check reference only and is not used.

## K-SE-3 fence, on the face

Nothing in this module asserts or implies an entropy shift from the
linear coefficient `b` or the constant filter `c` alone. In the
identity above, `b` and `c` enter only inside `log w`, `log Z`, and
the cross term `(E_p − E_q)[log p]`, in the combination the identity
exhibits; the seat statement that their total contribution is
exactly `0` is H3b, SE-5's verdict brick, not a claim of this one.

## Integrability discipline

Every identity carries its integrability hypotheses explicitly:
integrability of `p·w`, of `q·log p`, and of `q·log w` (and, where
used, of `p·log p`). At the Maxwell–Boltzmann / shadow-weight seat
(§4) the base density's `p·log p` integrability is SE-1's landed
`integrable_mbDensity_mul_log`; the rectified density's
log-integrability hypotheses are carried as named hypotheses of the
seat corollary — they are what SE-4 discharges at its Gaussian seats
(the rectified law there is Gaussian in the `v 0` direction exactly
when the arena admissibility `0 < 1 + 2aτ` holds) — and are not
assumed silently here.

## Sibling discipline

This module's entropy is SE's own continuous differential entropy
(`ThetLogos.DiffEntropy`). It does not import or cite the finite
entropy object of the sibling T-ENT line.

-/

open MeasureTheory

namespace ThetLogos

/-! ## §1. Expectations, the weighted density, and the KL forms -/

/-- Expectation of `f` against a density `p` on velocity space:
`expectationDensity p f = ∫ v, p v * f v` against Lebesgue volume. -/
noncomputable def expectationDensity (p f : VelocitySpace → ℝ) : ℝ :=
  ∫ v, p v * f v ∂(volume : Measure VelocitySpace)

/-- The normalized weighted density: `weightedDensity p w Z v =
p v * w v / Z`. Entropy is only ever applied to this normalized
form, never to the unnormalized product `p·w`. -/
noncomputable def weightedDensity (p w : VelocitySpace → ℝ) (Z : ℝ)
    (v : VelocitySpace) : ℝ :=
  p v * w v / Z

/-- The finite KL form for densities against volume, at the level of
density integrals: `klDivDensity q p = ∫ v, q v * log (q v / p v)`.
Defined in this module because the corpus owns no real-valued
density-level KL notion at this seat (the pin's `klDiv` is
measure-level and ENNReal-valued; see the module header). -/
noncomputable def klDivDensity (q p : VelocitySpace → ℝ) : ℝ :=
  ∫ v, q v * Real.log (q v / p v) ∂(volume : Measure VelocitySpace)

/-- The weight form of the KL term (memo §2):
`weightKLDiv p w Z = E_q[log w] − log Z` for
`q = weightedDensity p w Z`. Theorem `klDivDensity_weighted_eq`
below identifies it with `klDivDensity q p`. -/
noncomputable def weightKLDiv (p w : VelocitySpace → ℝ) (Z : ℝ) : ℝ :=
  expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) -
    Real.log Z

/-! ## §2. Positivity, normalization, and the log of the weighted density -/

/-- The shadow weight is strictly positive wherever the constant
filter value is: `0 < c → 0 < shadowWeight a b c v`. -/
lemma shadowWeight_pos (a b c : ℝ) (hc : 0 < c) (v : VelocitySpace) :
    0 < shadowWeight a b c v :=
  mul_pos hc (Real.exp_pos _)

/-- The weighted density is strictly positive for strictly positive
`p`, `w` and `0 < Z`. -/
lemma weightedDensity_pos (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z) (v : VelocitySpace) :
    0 < weightedDensity p w Z v :=
  div_pos (mul_pos (hp v) (hw v)) hZ

/-- The weighted density is integrable when the unnormalized product
is: it is a constant multiple of `p·w`. -/
lemma integrable_weightedDensity (p w : VelocitySpace → ℝ) (Z : ℝ)
    (h : Integrable (fun v => p v * w v) (volume : Measure VelocitySpace)) :
    Integrable (weightedDensity p w Z) (volume : Measure VelocitySpace) := by
  apply (h.const_mul Z⁻¹).congr
  filter_upwards with v
  unfold weightedDensity
  rw [div_eq_mul_inv, mul_comm]

/-- Normalization of the weighted density: if `Z = ∫ p·w` and
`Z ≠ 0`, then `∫ weightedDensity p w Z = 1`. -/
lemma integral_weightedDensity (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hZeq : Z = ∫ v, p v * w v ∂(volume : Measure VelocitySpace))
    (hZ : Z ≠ 0) :
    ∫ v, weightedDensity p w Z v ∂(volume : Measure VelocitySpace) = 1 := by
  have h : (∫ v, weightedDensity p w Z v ∂(volume : Measure VelocitySpace))
      = Z⁻¹ * ∫ v, p v * w v ∂(volume : Measure VelocitySpace) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    unfold weightedDensity
    rw [div_eq_mul_inv, mul_comm]
  rw [h, ← hZeq, inv_mul_cancel₀ hZ]

/-- The logarithm of the weighted density splits affinely:
`log (weightedDensity p w Z v) = log (p v) + log (w v) − log Z`,
for strictly positive `p`, `w` and `0 < Z`. This affine structure of
`log w` for the arena's weight family is the mechanism of the whole
identity. -/
lemma log_weightedDensity (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z) (v : VelocitySpace) :
    Real.log (weightedDensity p w Z v) =
      Real.log (p v) + Real.log (w v) - Real.log Z := by
  unfold weightedDensity
  rw [Real.log_div (mul_ne_zero (ne_of_gt (hp v)) (ne_of_gt (hw v)))
    (ne_of_gt hZ), Real.log_mul (ne_of_gt (hp v)) (ne_of_gt (hw v))]

end ThetLogos

namespace ThetLogos

/-! ## §3. The corrected weight identity and its KL form -/

/-- The entropy integrand of the weighted density, decomposed:
`∫ q·log q = E_q[log p] + E_q[log w] − log Z` for
`q = weightedDensity p w Z`, under strict positivity, `0 < Z`,
`Z = ∫ p·w`, and integrability of `p·w`, `q·log p`, `q·log w`. -/
theorem integral_weightedDensity_mul_log (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z)
    (hZeq : Z = ∫ v, p v * w v ∂(volume : Measure VelocitySpace))
    (hpw : Integrable (fun v => p v * w v) (volume : Measure VelocitySpace))
    (hqlogp : Integrable
      (fun v => weightedDensity p w Z v * Real.log (p v))
      (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => weightedDensity p w Z v * Real.log (w v))
      (volume : Measure VelocitySpace)) :
    (∫ v, weightedDensity p w Z v * Real.log (weightedDensity p w Z v)
        ∂(volume : Measure VelocitySpace)) =
      expectationDensity (weightedDensity p w Z) (fun v => Real.log (p v)) +
        expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) -
          Real.log Z := by
  have hq : Integrable (weightedDensity p w Z) (volume : Measure VelocitySpace) :=
    integrable_weightedDensity p w Z hpw
  have hthird : Integrable
      (fun v => Real.log Z * weightedDensity p w Z v)
      (volume : Measure VelocitySpace) := hq.const_mul _
  have hAB : Integrable
      (fun v => weightedDensity p w Z v * Real.log (p v) +
        weightedDensity p w Z v * Real.log (w v))
      (volume : Measure VelocitySpace) := hqlogp.add hqlogw
  have hnorm : ∫ v, weightedDensity p w Z v ∂(volume : Measure VelocitySpace) = 1 :=
    integral_weightedDensity p w Z hZeq (ne_of_gt hZ)
  have hpoint : ∀ v : VelocitySpace,
      weightedDensity p w Z v * Real.log (weightedDensity p w Z v) =
        (weightedDensity p w Z v * Real.log (p v) +
          weightedDensity p w Z v * Real.log (w v)) -
            Real.log Z * weightedDensity p w Z v := by
    intro v
    rw [log_weightedDensity p w Z hp hw hZ v]
    ring
  calc (∫ v, weightedDensity p w Z v * Real.log (weightedDensity p w Z v)
          ∂(volume : Measure VelocitySpace))
      = ∫ v, (weightedDensity p w Z v * Real.log (p v) +
            weightedDensity p w Z v * Real.log (w v)) -
              Real.log Z * weightedDensity p w Z v
          ∂(volume : Measure VelocitySpace) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ v, weightedDensity p w Z v * Real.log (p v)
            ∂(volume : Measure VelocitySpace)) +
          (∫ v, weightedDensity p w Z v * Real.log (w v)
            ∂(volume : Measure VelocitySpace)) -
          ∫ v, Real.log Z * weightedDensity p w Z v
            ∂(volume : Measure VelocitySpace) := by
        rw [integral_sub hAB hthird, integral_add hqlogp hqlogw]
    _ = expectationDensity (weightedDensity p w Z) (fun v => Real.log (p v)) +
          expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) -
            Real.log Z := by
        rw [integral_const_mul, hnorm, mul_one]
        rfl

/-- **The corrected weight identity (memo §2, SE-2 item 1).**
For a probability density `p` (strictly positive, normalized, with
`p·log p` integrable), a strictly positive weight `w`, and
`Z = ∫ p·w` with `0 < Z`, the weighted density
`q = weightedDensity p w Z` satisfies

`diffEntropy q − diffEntropy p
  = log Z − E_q[log w] + (E_p − E_q)[log p]`.

This is memo §2's corrected form; the killed candidate identity is
the same display with the cross term `(E_p − E_q)[log p]` deleted,
and it is not stated or used anywhere in this module. -/
theorem diffEntropy_weightedDensity_sub (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z)
    (hZeq : Z = ∫ v, p v * w v ∂(volume : Measure VelocitySpace))
    (hpw : Integrable (fun v => p v * w v) (volume : Measure VelocitySpace))
    (_hplogp : Integrable (fun v => p v * Real.log (p v))
      (volume : Measure VelocitySpace))
    (hqlogp : Integrable
      (fun v => weightedDensity p w Z v * Real.log (p v))
      (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => weightedDensity p w Z v * Real.log (w v))
      (volume : Measure VelocitySpace)) :
    diffEntropy (weightedDensity p w Z) - diffEntropy p =
      Real.log Z -
        expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) +
          (expectationDensity p (fun v => Real.log (p v)) -
            expectationDensity (weightedDensity p w Z)
              (fun v => Real.log (p v))) := by
  have hmain := integral_weightedDensity_mul_log p w Z hp hw hZ hZeq hpw
    hqlogp hqlogw
  have hdiffp : diffEntropy p =
      -expectationDensity p (fun v => Real.log (p v)) := rfl
  have hdiffq : diffEntropy (weightedDensity p w Z) =
      -(expectationDensity (weightedDensity p w Z) (fun v => Real.log (p v)) +
        expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) -
          Real.log Z) := by
    unfold diffEntropy
    rw [hmain]
  rw [hdiffq, hdiffp]
  ring

/-- The weight KL term is the density-level KL divergence:
`weightKLDiv p w Z = klDivDensity (weightedDensity p w Z) p`,
under the same positivity, normalization-of-`Z`, and integrability
hypotheses as the main identity (minus `p·log p`, which this
identification does not consume). Pointwise,
`q v / p v = w v / Z`, so `log (q v / p v) = log (w v) − log Z`,
and the constant term integrates against `∫ q = 1`. -/
theorem klDivDensity_weighted_eq (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z)
    (hZeq : Z = ∫ v, p v * w v ∂(volume : Measure VelocitySpace))
    (hpw : Integrable (fun v => p v * w v) (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => weightedDensity p w Z v * Real.log (w v))
      (volume : Measure VelocitySpace)) :
    klDivDensity (weightedDensity p w Z) p = weightKLDiv p w Z := by
  have hq : Integrable (weightedDensity p w Z) (volume : Measure VelocitySpace) :=
    integrable_weightedDensity p w Z hpw
  have hnorm : ∫ v, weightedDensity p w Z v ∂(volume : Measure VelocitySpace) = 1 :=
    integral_weightedDensity p w Z hZeq (ne_of_gt hZ)
  have hpoint : ∀ v : VelocitySpace,
      weightedDensity p w Z v * Real.log (weightedDensity p w Z v / p v) =
        weightedDensity p w Z v * Real.log (w v) -
          Real.log Z * weightedDensity p w Z v := by
    intro v
    have hdiv : weightedDensity p w Z v / p v = w v / Z := by
      unfold weightedDensity
      rw [div_div, mul_comm Z (p v), mul_div_mul_left _ _ (ne_of_gt (hp v))]
    rw [hdiv, Real.log_div (ne_of_gt (hw v)) (ne_of_gt hZ)]
    ring
  calc (∫ v, weightedDensity p w Z v * Real.log (weightedDensity p w Z v / p v)
          ∂(volume : Measure VelocitySpace))
      = ∫ v, weightedDensity p w Z v * Real.log (w v) -
            Real.log Z * weightedDensity p w Z v
          ∂(volume : Measure VelocitySpace) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ v, weightedDensity p w Z v * Real.log (w v)
            ∂(volume : Measure VelocitySpace)) -
          ∫ v, Real.log Z * weightedDensity p w Z v
            ∂(volume : Measure VelocitySpace) :=
        integral_sub hqlogw (hq.const_mul _)
    _ = (∫ v, weightedDensity p w Z v * Real.log (w v)
            ∂(volume : Measure VelocitySpace)) - Real.log Z := by
        rw [integral_const_mul, hnorm, mul_one]
    _ = weightKLDiv p w Z := rfl

/-- **The KL form of the corrected weight identity (SE-2 item 2).**
Under the main identity's hypotheses,

`diffEntropy q − diffEntropy p
  = −klDivDensity q p + (E_p − E_q)[log p]`,

for `q = weightedDensity p w Z` — memo §2's display
`−D(q‖p) + (E_p − E_q)[log p]` with `D` the density-level KL form
defined in this module. -/
theorem diffEntropy_weightedDensity_sub_kl (p w : VelocitySpace → ℝ) (Z : ℝ)
    (hp : ∀ v, 0 < p v) (hw : ∀ v, 0 < w v) (hZ : 0 < Z)
    (hZeq : Z = ∫ v, p v * w v ∂(volume : Measure VelocitySpace))
    (hpw : Integrable (fun v => p v * w v) (volume : Measure VelocitySpace))
    (hplogp : Integrable (fun v => p v * Real.log (p v))
      (volume : Measure VelocitySpace))
    (hqlogp : Integrable
      (fun v => weightedDensity p w Z v * Real.log (p v))
      (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => weightedDensity p w Z v * Real.log (w v))
      (volume : Measure VelocitySpace)) :
    diffEntropy (weightedDensity p w Z) - diffEntropy p =
      -klDivDensity (weightedDensity p w Z) p +
        (expectationDensity p (fun v => Real.log (p v)) -
          expectationDensity (weightedDensity p w Z)
            (fun v => Real.log (p v))) := by
  have h1 := diffEntropy_weightedDensity_sub p w Z hp hw hZ hZeq hpw hplogp
    hqlogp hqlogw
  have h2 := klDivDensity_weighted_eq p w Z hp hw hZ hZeq hpw hqlogw
  calc diffEntropy (weightedDensity p w Z) - diffEntropy p
      = Real.log Z -
          expectationDensity (weightedDensity p w Z) (fun v => Real.log (w v)) +
            (expectationDensity p (fun v => Real.log (p v)) -
              expectationDensity (weightedDensity p w Z)
                (fun v => Real.log (p v))) := h1
    _ = -klDivDensity (weightedDensity p w Z) p +
          (expectationDensity p (fun v => Real.log (p v)) -
            expectationDensity (weightedDensity p w Z)
              (fun v => Real.log (p v))) := by
        rw [h2]
        unfold weightKLDiv
        ring

end ThetLogos

namespace ThetLogos

/-! ## §4. The seat form: Maxwell–Boltzmann base, shadow weight

The arena instantiation SE-4 consumes: `p = mbDensity τ`,
`w = shadowWeight a b c`, `Z = partitionZ τ a b c`, and
`q = rectifiedDensity τ a b c hZ`, which is pointwise the weighted
density of §1. The base density's positivity is SE-1's
`mbDensity_pos` and its `p·log p` integrability is SE-1's landed
`integrable_mbDensity_mul_log`; the weight's positivity is
`shadowWeight_pos` above. Carried explicitly as hypotheses (not
assumed, not proved here — discharging them at the Gaussian seat is
SE-4's work): integrability of the unnormalized product
`mbDensity τ · shadowWeight a b c`, of
`rectifiedDensity · log (mbDensity τ)`, and of
`rectifiedDensity · log (shadowWeight a b c)`. The last of these is
the rectified weight's log-integrability: pointwise
`log (shadowWeight a b c v) = log c − (a·(v 0)² + b·(v 0))`, a
quadratic polynomial in the `v 0` component. -/

/-- **The corrected weight identity at the seat (SE-2, seat form).**
For `0 < τ`, `0 < c`, the packaged `0 < Z` witness
`hZ : 0 < partitionZ τ a b c`, and the three explicit integrability
hypotheses named in the section header,

`diffEntropy q − diffEntropy (mbDensity τ)
  = log Z − E_q[log w] + (E_p − E_q)[log p]`

with `p = mbDensity τ`, `w = shadowWeight a b c`,
`Z = partitionZ τ a b c`, `q = rectifiedDensity τ a b c hZ`.
Per the K-SE-3 fence on this module's face, this display asserts no
shift from `b` or `c` alone: both enter only inside `log w`,
`log Z`, and the cross term, in the exhibited combination. -/
theorem shadow_weight_identity (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hZ : 0 < partitionZ τ a b c)
    (hpw : Integrable (fun v => mbDensity τ v * shadowWeight a b c v)
      (volume : Measure VelocitySpace))
    (hqlogp : Integrable
      (fun v => rectifiedDensity τ a b c hZ v * Real.log (mbDensity τ v))
      (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => rectifiedDensity τ a b c hZ v * Real.log (shadowWeight a b c v))
      (volume : Measure VelocitySpace)) :
    diffEntropy (rectifiedDensity τ a b c hZ) - diffEntropy (mbDensity τ) =
      Real.log (partitionZ τ a b c) -
        expectationDensity (rectifiedDensity τ a b c hZ)
          (fun v => Real.log (shadowWeight a b c v)) +
          (expectationDensity (mbDensity τ) (fun v => Real.log (mbDensity τ v)) -
            expectationDensity (rectifiedDensity τ a b c hZ)
              (fun v => Real.log (mbDensity τ v))) :=
  diffEntropy_weightedDensity_sub (mbDensity τ) (shadowWeight a b c)
    (partitionZ τ a b c)
    (fun v => mbDensity_pos τ hτ v)
    (fun v => shadowWeight_pos a b c hc v)
    hZ rfl hpw (integrable_mbDensity_mul_log τ hτ) hqlogp hqlogw

/-- **The KL form at the seat.** Under the same hypotheses as
`shadow_weight_identity`,

`diffEntropy q − diffEntropy (mbDensity τ)
  = −klDivDensity q (mbDensity τ) + (E_p − E_q)[log p]`. -/
theorem shadow_weight_identity_kl (τ a b c : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hZ : 0 < partitionZ τ a b c)
    (hpw : Integrable (fun v => mbDensity τ v * shadowWeight a b c v)
      (volume : Measure VelocitySpace))
    (hqlogp : Integrable
      (fun v => rectifiedDensity τ a b c hZ v * Real.log (mbDensity τ v))
      (volume : Measure VelocitySpace))
    (hqlogw : Integrable
      (fun v => rectifiedDensity τ a b c hZ v * Real.log (shadowWeight a b c v))
      (volume : Measure VelocitySpace)) :
    diffEntropy (rectifiedDensity τ a b c hZ) - diffEntropy (mbDensity τ) =
      -klDivDensity (rectifiedDensity τ a b c hZ) (mbDensity τ) +
        (expectationDensity (mbDensity τ) (fun v => Real.log (mbDensity τ v)) -
          expectationDensity (rectifiedDensity τ a b c hZ)
            (fun v => Real.log (mbDensity τ v))) :=
  diffEntropy_weightedDensity_sub_kl (mbDensity τ) (shadowWeight a b c)
    (partitionZ τ a b c)
    (fun v => mbDensity_pos τ hτ v)
    (fun v => shadowWeight_pos a b c hc v)
    hZ rfl hpw (integrable_mbDensity_mul_log τ hτ) hqlogp hqlogw

end ThetLogos
