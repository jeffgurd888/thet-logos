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
import ThetLogos.ShadowEntropyPost

/-!
# ThetLogos.DiffEntropy — SE-1: differential entropy, the definition brick

**Status: DEFINITION + KIT. NO CLAIM. No Millennium statement, no ladder
rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing pack:
`routeb-general-scratch/pack-se-1.md`; governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md` §4 (SE-1).
Gate SE-0 is landed (`ThetLogos.ShadowEntropyPost`, which registered the
§5 target `Prop`s against an explicit signature parameter
`diffEntropy : (VelocitySpace → ℝ) → ℝ`). This module supplies the real
function with exactly that signature, consuming SE-0's `VelocitySpace`
abbrev (not redefining it).

## What is defined, and the convention on its face

`diffEntropy p = −∫ v, p v * Real.log (p v) ∂(volume)`: the negative
Bochner integral of `p · log p` against the Pi Lebesgue volume on
`VelocitySpace = Fin 3 → ℝ`, with log base `e` (`Real.log`) — the memo's
convention. This is CONTINUOUS differential entropy over a Lebesgue
space; the finite von Neumann entropy of the sibling T-ENT line is a
different definition, and neither line cites or gates the other.

Where `p` is not a density, or `p · log p` is not integrable, the
Bochner integral is `0` by the integral's own convention, so
`diffEntropy p = 0` there. No theorem in this module leans on that
convention silently: every lemma below carries its integrability
hypotheses explicitly.

## Kit landed here

* Translation invariance (`diffEntropy_sub_translate`), via
  measure-preservation of translation on the Pi Lebesgue space.
* Product additivity over a disjoint-sum Pi split
  (`diffEntropyOn_sum_prod`): for strictly positive densities `p` on
  `Fin m → ℝ` and `q` on `Fin n → ℝ`, each normalized and with
  `p · log p`, `q · log q` integrable, the product density on
  `(Fin m ⊕ Fin n) → ℝ`, `v ↦ p (v ∘ Sum.inl) * q (v ∘ Sum.inr)`, has
  entropy the sum of the two entropies. The `2 + 1` split of the
  velocity seat is named as a corollary.
* Gaussian log-integrability at the velocity seat
  (`integrable_mbDensity_mul_log`): for `0 < τ`, the function
  `v ↦ mbDensity τ v * Real.log (mbDensity τ v)` is integrable — the
  lemma SE-3 consumes. (Normalization and entropy VALUES are SE-3's
  brick, not this one.)

## Fences

- **K-SE-1 (vacuity guard).** `diffEntropy` above is the actual
  integral expression — not a constant function, and not a renaming of
  an existing entropy notion: the pin owns no differential-entropy
  definition at this signature (memo §1(1), verified at scoping).
- **K-SE-S.** Overruns on this line are stalls / re-prices, never kills.
- **NO CLAIM.** Everything here is T1 machine-checked mathematics
  about chosen density functions; any reading of the seat as physics
  is T5 and is not licensed by anything here.
-/

open MeasureTheory

namespace ThetLogos

/-! ## §1. The definition -/

/-- Differential entropy over a general finite Pi space `ι → ℝ`:
`diffEntropyOn p = −∫ v, p v * Real.log (p v) ∂(volume)`, against the
Pi Lebesgue volume. The generalization that product additivity is
stated over; the exported seat definition `diffEntropy` below is this
at `ι = Fin 3` and has exactly the SE-0 pin's signature. Where
`p · log p` is not integrable the integral is `0` by convention (see
the module header); theorems carry integrability explicitly. -/
noncomputable def diffEntropyOn {ι : Type*} [Fintype ι] (p : (ι → ℝ) → ℝ) : ℝ :=
  -∫ v, p v * Real.log (p v) ∂(volume : Measure (ι → ℝ))

/-- **The SE-1 definition.** Differential entropy of a density `p` on
velocity space: `diffEntropy p = −∫ v, p v * Real.log (p v)`, against
the Pi Lebesgue volume on `VelocitySpace = Fin 3 → ℝ`, log base `e`.
Signature, verbatim as registered by SE-0:
`diffEntropy : (VelocitySpace → ℝ) → ℝ`. -/
noncomputable def diffEntropy (p : VelocitySpace → ℝ) : ℝ :=
  -∫ v, p v * Real.log (p v) ∂(volume : Measure VelocitySpace)

/-- The exported seat definition is the general Pi definition at
`Fin 3`, by unfolding both. -/
lemma diffEntropy_eq_diffEntropyOn (p : VelocitySpace → ℝ) :
    diffEntropy p = diffEntropyOn p := rfl

/-! ## §2. Translation invariance

The Pi Lebesgue volume is translation invariant; the entropy
integrand of a translated density is the translate of the integrand,
so the integral — hence the entropy — is unchanged. -/

/-- Integral of a translate: for any `F : (ι → ℝ) → ℝ` and fixed
`a : ι → ℝ`, `∫ v, F (v + a) ∂volume = ∫ v, F v ∂volume`. Route:
`MeasurePreserving.integral_comp` for right addition, with the
measurable embedding supplied by the measurable equiv `· + a`. -/
lemma integral_add_right_eq (ι : Type*) [Fintype ι] (F : (ι → ℝ) → ℝ) (a : ι → ℝ) :
    (∫ v, F (v + a) ∂(volume : Measure (ι → ℝ))) = ∫ v, F v ∂volume := by
  have hmp : MeasurePreserving (· + a) (volume : Measure (ι → ℝ)) volume :=
    measurePreserving_add_right volume a
  have hemb : MeasurableEmbedding (· + a : (ι → ℝ) → (ι → ℝ)) :=
    (MeasurableEquiv.addRight a).measurableEmbedding
  exact hmp.integral_comp hemb F

/-- Integral of a difference-translate: `∫ v, F (v - a) = ∫ v, F v`,
from the addition form at `-a`. -/
lemma integral_sub_right_eq (ι : Type*) [Fintype ι] (F : (ι → ℝ) → ℝ) (a : ι → ℝ) :
    (∫ v, F (v - a) ∂(volume : Measure (ι → ℝ))) = ∫ v, F v ∂volume := by
  have h := integral_add_right_eq ι F (-a)
  simpa only [sub_eq_add_neg] using h

/-- Translation invariance of `diffEntropyOn`: shifting a density by
a fixed vector does not change its differential entropy. Stated with
no integrability hypothesis: if `p · log p` is not integrable both
sides are `0` by the Bochner convention, and if it is, the integrals
agree by `integral_sub_right_eq`. -/
theorem diffEntropyOn_sub_translate {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ℝ) (a : ι → ℝ) :
    diffEntropyOn (fun v => p (v - a)) = diffEntropyOn p := by
  unfold diffEntropyOn
  congr 1
  exact integral_sub_right_eq ι (fun v => p v * Real.log (p v)) a

/-- **Translation invariance at the velocity seat (SE-1 item 2).**
For a density `p` on `VelocitySpace` and a fixed shift `a`,
`diffEntropy (fun v => p (v - a)) = diffEntropy p`. -/
theorem diffEntropy_sub_translate (p : VelocitySpace → ℝ) (a : VelocitySpace) :
    diffEntropy (fun v => p (v - a)) = diffEntropy p := by
  rw [diffEntropy_eq_diffEntropyOn, diffEntropy_eq_diffEntropyOn]
  exact diffEntropyOn_sub_translate p a

/-! ## §3. Product additivity

The Pi space over a disjoint sum `ι ⊕ κ` is measurably the product of
the two Pi spaces (`MeasurableEquiv.sumPiEquivProdPi`, measure
preserving for the Pi Lebesgue volumes). Under that identification
the product density's integrand splits, via `Real.log_mul`, into the
two cross terms, whose product integrals factor by Fubini
(`integral_prod_mul`) and collapse under the normalizations
`∫ p = ∫ q = 1`. -/

/-- The entropy integrand of a sum-split product density, computed
through the product identification: its integral is the sum of the
two entropy integrands' integrals. The hypotheses are exactly the
ones the computation consumes: strict positivity (for
`Real.log_mul`), both normalizations, integrability of both
densities, and integrability of both `· * log ·` integrands. -/
lemma integral_sum_prod_mul_log {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : (ι → ℝ) → ℝ) (q : (κ → ℝ) → ℝ)
    (hp_pos : ∀ v, 0 < p v) (hq_pos : ∀ v, 0 < q v)
    (hp_int : Integrable p (volume : Measure (ι → ℝ)))
    (hq_int : Integrable q (volume : Measure (κ → ℝ)))
    (hp_log_int : Integrable (fun v => p v * Real.log (p v)) (volume : Measure (ι → ℝ)))
    (hq_log_int : Integrable (fun v => q v * Real.log (q v)) (volume : Measure (κ → ℝ)))
    (hp_norm : ∫ v, p v ∂(volume : Measure (ι → ℝ)) = 1)
    (hq_norm : ∫ v, q v ∂(volume : Measure (κ → ℝ)) = 1) :
    (∫ v : (ι ⊕ κ) → ℝ, (p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) *
        Real.log (p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) ∂volume) =
      (∫ v, p v * Real.log (p v) ∂(volume : Measure (ι → ℝ))) +
        ∫ v, q v * Real.log (q v) ∂(volume : Measure (κ → ℝ)) := by
  classical
  set e : ((ι ⊕ κ) → ℝ) ≃ᵐ ((ι → ℝ) × (κ → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ) with he
  have hmp : MeasurePreserving e (volume : Measure ((ι ⊕ κ) → ℝ)) volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  -- Transport the integral to the product space.
  have htransport :
      (∫ z : (ι → ℝ) × (κ → ℝ), (p z.1 * q z.2) * Real.log (p z.1 * q z.2)
          ∂(volume : Measure ((ι → ℝ) × (κ → ℝ)))) =
        ∫ v : (ι ⊕ κ) → ℝ, (p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) *
          Real.log (p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) ∂volume := by
    have h := hmp.integral_comp'
      (fun z : (ι → ℝ) × (κ → ℝ) => (p z.1 * q z.2) * Real.log (p z.1 * q z.2))
    rw [← h]
    apply integral_congr_ae
    filter_upwards with v
    have h1 : (e v).1 = v ∘ Sum.inl := by
      funext i
      rfl
    have h2 : (e v).2 = v ∘ Sum.inr := by
      funext j
      rfl
    rw [h1, h2]
  rw [← htransport]
  -- Split the logarithm and factor the two cross terms.
  have hsplit : ∀ z : (ι → ℝ) × (κ → ℝ),
      (p z.1 * q z.2) * Real.log (p z.1 * q z.2) =
        (p z.1 * Real.log (p z.1)) * q z.2 + p z.1 * (q z.2 * Real.log (q z.2)) := by
    intro z
    rw [Real.log_mul (ne_of_gt (hp_pos z.1)) (ne_of_gt (hq_pos z.2))]
    ring
  have hA : Integrable (fun z : (ι → ℝ) × (κ → ℝ) =>
      (p z.1 * Real.log (p z.1)) * q z.2)
      ((volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ))) :=
    hp_log_int.mul_prod hq_int
  have hB : Integrable (fun z : (ι → ℝ) × (κ → ℝ) =>
      p z.1 * (q z.2 * Real.log (q z.2)))
      ((volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ))) :=
    hp_int.mul_prod hq_log_int
  show (∫ z : (ι → ℝ) × (κ → ℝ), (p z.1 * q z.2) * Real.log (p z.1 * q z.2)
      ∂((volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ)))) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add hA hB,
    integral_prod_mul (fun v => p v * Real.log (p v)) q,
    integral_prod_mul p (fun v => q v * Real.log (q v)), hp_norm, hq_norm,
    mul_one, one_mul]

/-- **Product additivity (SE-1 item 3).** For strictly positive
densities `p` on `Fin m → ℝ` and `q` on `Fin n → ℝ` — here stated for
general finite index types `ι, κ` — each normalized (`∫ p = ∫ q = 1`),
each integrable, and with `p * log p`, `q * log q` integrable, the
product density on the sum Pi space has entropy the sum of the two
entropies:
`diffEntropyOn (fun v => p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) =
diffEntropyOn p + diffEntropyOn q`. -/
theorem diffEntropyOn_sum_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : (ι → ℝ) → ℝ) (q : (κ → ℝ) → ℝ)
    (hp_pos : ∀ v, 0 < p v) (hq_pos : ∀ v, 0 < q v)
    (hp_int : Integrable p (volume : Measure (ι → ℝ)))
    (hq_int : Integrable q (volume : Measure (κ → ℝ)))
    (hp_log_int : Integrable (fun v => p v * Real.log (p v)) (volume : Measure (ι → ℝ)))
    (hq_log_int : Integrable (fun v => q v * Real.log (q v)) (volume : Measure (κ → ℝ)))
    (hp_norm : ∫ v, p v ∂(volume : Measure (ι → ℝ)) = 1)
    (hq_norm : ∫ v, q v ∂(volume : Measure (κ → ℝ)) = 1) :
    diffEntropyOn (fun v : (ι ⊕ κ) → ℝ => p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) =
      diffEntropyOn p + diffEntropyOn q := by
  unfold diffEntropyOn
  rw [integral_sum_prod_mul_log p q hp_pos hq_pos hp_int hq_int hp_log_int hq_log_int
    hp_norm hq_norm]
  ring

/-- The velocity-seat split `3 = 2 + 1`, named: product additivity for
a density on `Fin 2 → ℝ` times a density on `Fin 1 → ℝ`, giving a
density on `(Fin 2 ⊕ Fin 1) → ℝ`. Same hypotheses as
`diffEntropyOn_sum_prod`, instantiated. -/
theorem diffEntropyOn_fin_two_one_prod
    (p : (Fin 2 → ℝ) → ℝ) (q : (Fin 1 → ℝ) → ℝ)
    (hp_pos : ∀ v, 0 < p v) (hq_pos : ∀ v, 0 < q v)
    (hp_int : Integrable p (volume : Measure (Fin 2 → ℝ)))
    (hq_int : Integrable q (volume : Measure (Fin 1 → ℝ)))
    (hp_log_int : Integrable (fun v => p v * Real.log (p v)) (volume : Measure (Fin 2 → ℝ)))
    (hq_log_int : Integrable (fun v => q v * Real.log (q v)) (volume : Measure (Fin 1 → ℝ)))
    (hp_norm : ∫ v, p v ∂(volume : Measure (Fin 2 → ℝ)) = 1)
    (hq_norm : ∫ v, q v ∂(volume : Measure (Fin 1 → ℝ)) = 1) :
    diffEntropyOn (fun v : (Fin 2 ⊕ Fin 1) → ℝ => p (v ∘ Sum.inl) * q (v ∘ Sum.inr)) =
      diffEntropyOn p + diffEntropyOn q :=
  diffEntropyOn_sum_prod p q hp_pos hq_pos hp_int hq_int hp_log_int hq_log_int
    hp_norm hq_norm

/-- Translation invariance, addition form: shifting by `a` (rather
than `-a`) also preserves `diffEntropyOn`. -/
theorem diffEntropyOn_add_translate {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ℝ) (a : ι → ℝ) :
    diffEntropyOn (fun v => p (v + a)) = diffEntropyOn p := by
  unfold diffEntropyOn
  congr 1
  exact integral_add_right_eq ι (fun v => p v * Real.log (p v)) a

/-- Translation invariance at the velocity seat, addition form. -/
theorem diffEntropy_add_translate (p : VelocitySpace → ℝ) (a : VelocitySpace) :
    diffEntropy (fun v => p (v + a)) = diffEntropy p := by
  rw [diffEntropy_eq_diffEntropyOn, diffEntropy_eq_diffEntropyOn]
  exact diffEntropyOn_add_translate p a

/-! ## §4. Gaussian log-integrability

For `mbDensity τ` (`0 < τ`), `log (mbDensity τ v)` is an affine
function of the squared norm `∑ i, (v i)^2`, so `mbDensity * log
mbDensity` is a constant multiple of the Gaussian weight minus a
constant multiple of (Gaussian weight × squared norm). Both pieces
are integrable over the Pi space: the weight is a product of 1-D
Gaussian weights (`Integrable.fintype_prod` over
`integrable_exp_neg_mul_sq`), and the squared-norm piece is a finite
sum of such products with one squared 1-D factor
(`integrable_rpow_mul_exp_neg_mul_sq` at `s = 2`). -/

/-- The 1-D Gaussian weight in the seat's normalization:
`x ↦ exp (−x²/(2τ))` is integrable on `ℝ` for `0 < τ`. -/
lemma integrable_exp_neg_sq_div (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / (2 * τ))) volume := by
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  apply (integrable_exp_neg_mul_sq hb).congr
  filter_upwards with x
  congr 1
  ring

/-- The 1-D squared Gaussian factor: `x ↦ x² * exp (−x²/(2τ))` is
integrable on `ℝ` for `0 < τ` (the `s = 2` case of
`integrable_rpow_mul_exp_neg_mul_sq`). -/
lemma integrable_sq_mul_exp_neg_sq_div (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / (2 * τ))) volume := by
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num)
  apply h.congr
  filter_upwards with x
  rw [Real.rpow_two]
  congr 1
  congr 1
  ring

/-- The Pi Gaussian weight as a product of 1-D weights:
`exp (−(∑ i, (v i)^2)/(2τ)) = ∏ i, exp (−(v i)^2/(2τ))`. -/
lemma exp_neg_sumSq_eq_prod {ι : Type*} [Fintype ι] (τ : ℝ) (v : ι → ℝ) :
    Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) =
      ∏ i, Real.exp (-((v i) ^ 2) / (2 * τ)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib, Finset.sum_div]

/-- The Pi Gaussian weight is integrable over any finite Pi space
`ι → ℝ`, for `0 < τ`: it is a product of integrable 1-D weights. -/
lemma integrable_exp_neg_sumSq {ι : Type*} [Fintype ι] (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun v : ι → ℝ => Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ))) volume := by
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  have hprod : Integrable
      (fun v : ι → ℝ => ∏ i, Real.exp (-(1 / (2 * τ)) * (v i) ^ 2))
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hb)
  show Integrable _ (Measure.pi fun _ : ι => (volume : Measure ℝ))
  apply hprod.congr
  filter_upwards with v
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring

/-- The Pi Gaussian weight times the squared norm is integrable over
any finite Pi space `ι → ℝ`, for `0 < τ`: the squared norm is a finite
sum of coordinates squared, and each summand is a product of 1-D
factors — one squared Gaussian factor, the rest plain Gaussian
weights. -/
lemma integrable_exp_neg_sumSq_mul_sumSq {ι : Type*} [Fintype ι] (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun v : ι → ℝ =>
      Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) * (∑ i, (v i) ^ 2)) volume := by
  classical
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  have h1exp : Integrable (fun x : ℝ => Real.exp (-(1 / (2 * τ)) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  have h1sq : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(1 / (2 * τ)) * x ^ 2))
      volume := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num)
    apply h.congr
    filter_upwards with x
    rw [Real.rpow_two]
  have hterm : ∀ i : ι, Integrable (fun v : ι → ℝ =>
      Real.exp (-(∑ j, (v j) ^ 2) / (2 * τ)) * (v i) ^ 2) volume := by
    intro i
    have hprod : Integrable
        (fun v : ι → ℝ => ∏ j, ((v j) ^ (if j = i then 2 else 0) *
          Real.exp (-(1 / (2 * τ)) * (v j) ^ 2)))
        (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
      apply Integrable.fintype_prod
        (f := fun j x => x ^ (if j = i then 2 else 0) *
          Real.exp (-(1 / (2 * τ)) * x ^ 2))
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using h1sq
      · simpa [hji] using h1exp
    show Integrable _ (Measure.pi fun _ : ι => (volume : Measure ℝ))
    apply hprod.congr
    filter_upwards with v
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    have hsum : (∑ j, -(1 / (2 * τ)) * (v j) ^ 2) =
        -(∑ j, (v j) ^ 2) / (2 * τ) := by
      rw [← Finset.mul_sum]
      ring
    rw [hsum, mul_comm (∏ j, (v j) ^ (if j = i then 2 else 0)) _]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp only [hb, ite_false, pow_zero]
    · simp
  have hsum_int : Integrable (fun v : ι → ℝ =>
      ∑ i, Real.exp (-(∑ j, (v j) ^ 2) / (2 * τ)) * (v i) ^ 2) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  apply hsum_int.congr
  filter_upwards with v
  rw [Finset.mul_sum]

/-- The Maxwell–Boltzmann density is strictly positive for `0 < τ`:
both the real-power normalization factor and the exponential are
positive. -/
lemma mbDensity_pos (τ : ℝ) (hτ : 0 < τ) (v : VelocitySpace) :
    0 < mbDensity τ v := by
  unfold mbDensity
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact Real.exp_pos _

/-- The logarithm of the Maxwell–Boltzmann density is affine in the
squared norm: `log (mbDensity τ v) = log C − (∑ i, (v i)^2)/(2τ)`,
where `C = (2πτ)^(−3/2)`. -/
lemma log_mbDensity (τ : ℝ) (hτ : 0 < τ) (v : VelocitySpace) :
    Real.log (mbDensity τ v) =
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) -
        (∑ i, (v i) ^ 2) / (2 * τ) := by
  unfold mbDensity
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))
    (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  ring

/-- The Maxwell–Boltzmann density itself is integrable for `0 < τ`
(a constant multiple of the Pi Gaussian weight). -/
lemma integrable_mbDensity (τ : ℝ) (hτ : 0 < τ) :
    Integrable (mbDensity τ) volume := by
  have h := (integrable_exp_neg_sumSq (ι := Fin 3) τ hτ).const_mul
    ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2))
  apply h.congr
  filter_upwards with v
  rfl

/-- **Gaussian log-integrability at the velocity seat (SE-1 item 4).**
For `0 < τ`, the entropy integrand of the Maxwell–Boltzmann density
is integrable: `Integrable (fun v => mbDensity τ v * Real.log
(mbDensity τ v))`. This is the lemma SE-3 consumes. Proof: by
`log_mbDensity` the integrand is `log C • mbDensity − (C/(2τ)) •
(weight × squared norm)`, a difference of two integrable functions. -/
theorem integrable_mbDensity_mul_log (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun v => mbDensity τ v * Real.log (mbDensity τ v)) volume := by
  have hC : Integrable (fun v : VelocitySpace =>
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) * mbDensity τ v) volume :=
    (integrable_mbDensity τ hτ).const_mul _
  have hS : Integrable (fun v : VelocitySpace =>
      ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) / (2 * τ) *
        (Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) * (∑ i, (v i) ^ 2))) volume :=
    (integrable_exp_neg_sumSq_mul_sumSq τ hτ).const_mul _
  apply (hC.sub hS).congr
  filter_upwards with v
  rw [log_mbDensity τ hτ v]
  simp only [Pi.sub_apply]
  unfold mbDensity
  ring

/-- The standard Gaussian seat, named: at `τ = 1` the
Maxwell–Boltzmann entropy integrand is integrable. -/
theorem integrable_mbDensity_one_mul_log :
    Integrable (fun v => mbDensity 1 v * Real.log (mbDensity 1 v)) volume :=
  integrable_mbDensity_mul_log 1 one_pos

end ThetLogos
