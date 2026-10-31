import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import ThetLogos.DiffEntropy

/-!
# ThetLogos.ShadowMBSeat — SE-3: the Maxwell–Boltzmann seat

**Status: SEAT VALUES COMPUTED. NO CLAIM. No Millennium statement, no
ladder rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing pack:
`routeb-general-scratch/pack-se-3.md`; governing memo:
`routeb-general-scratch/scoping-shadow-entropy-2026-10-31.md` §3, §5.
Gates consumed: SE-0 (`ThetLogos.ShadowEntropyPost`: the `mbDensity`
definition and the registered target `shadowEntropyH1`, stated there
against an explicit signature parameter) and SE-1
(`ThetLogos.DiffEntropy`: the real `diffEntropy` of exactly that
signature, `log_mbDensity`, `integrable_mbDensity`,
`integrable_mbDensity_mul_log`, `integrable_exp_neg_sq_div`,
`integrable_sq_mul_exp_neg_sq_div`, `exp_neg_sumSq_eq_prod`).
Substitution, stated explicitly per the pack: everywhere below,
SE-0's signature parameter is filled by SE-1's `diffEntropy`; the
closing theorem of §4 is `shadowEntropyH1 diffEntropy` itself.

## What is proved

1. **Normalization** (`integral_mbDensity`): `∫ v, mbDensity τ v = 1`
   for `0 < τ`.
2. **H1** (`diffEntropy_mbDensity`, and `shadowEntropyH1_holds`
   discharging the registered target): for `0 < τ`,
   `diffEntropy (mbDensity τ) = (3/2) * Real.log (2 * π * Real.exp 1 * τ)`.
3. **Seat raw materials for SE-4/SE-5** (item 3 of the pack, landed,
   not partial): the coordinate moments
   `∫ v, mbDensity τ v * (v i)^2 = τ` and `∫ v, mbDensity τ v * (v 0) = 0`,
   and the total second moment `∫ v, mbDensity τ v * (∑ i, (v i)^2) = 3τ`
   that H1's assembly consumes.

## The Gaussian route (pin facts, named)

Nothing is entered: every value is computed from the pin.

- 0th moment: `integral_gaussian` (Mathlib's
  `∫ x, exp (-b * x^2) = √(π / b)`) at `b = 1/(2τ)`.
- 2nd moment: the pin's Gamma–Mellin fact
  `integral_rpow_mul_exp_neg_mul_rpow` over `Ioi 0` at `p = q = 2`,
  doubled over the whole line by the even-integrand fact
  `integral_comp_abs`, with `Real.Gamma (3/2) = (1/2) * √π` from
  `Real.Gamma_add_one` and `Real.Gamma_one_half_eq`. (The pin carries
  this direct moment fact, so the parameter-derivative fallback in
  the pack was not needed.)
- 1st moment: `0` by odd symmetry — `Measure.measurePreserving_neg`
  plus pointwise negation of the integrand; the integrability is the
  pin's `integrable_mul_exp_neg_mul_sq`.
- The 3-D integrals factor over coordinates by
  `integral_fintype_prod_volume_eq_prod` after
  `exp_neg_sumSq_eq_prod` (SE-1) writes the Pi Gaussian weight as a
  product of 1-D weights.

## Fences

- **NO CLAIM.** Everything here is T1 machine-checked mathematics
  about the chosen density `mbDensity`; the Maxwell–Boltzmann closed
  forms are T4 (textbook); any reading of the seat as physics is T5
  and is not licensed by anything here.
- **Sibling discipline (T-ENT).** The entropy here is the CONTINUOUS
  differential entropy of SE-1. The finite von Neumann entropy of the
  sibling T-ENT line is a different definition; nothing in this
  module cites it.
- **K-SE-4 (scope guard).** Everything stays inside the memo §3
  arena: the MB seat at `VelocitySpace = Fin 3 → ℝ`, `τ > 0`.
-/

open MeasureTheory

namespace ThetLogos

/-! ## §1. The 1-D Gaussian facts in seat normalization

Throughout, `b = 1/(2τ)`; the seat's exponent `-(x^2)/(2τ)` is
`-b * x^2` by one `field_simp`/`ring` step, recorded once here as a
pointwise rewrite and reused. -/

/-- Pointwise exponent rewrite: `-(x^2)/(2τ) = -(1/(2τ)) * x^2`. -/
lemma neg_sq_div_eq (x τ : ℝ) :
    -(x ^ 2) / (2 * τ) = -(1 / (2 * τ)) * x ^ 2 := by
  rw [one_div, div_eq_mul_inv]
  ring

/-- **1-D 0th moment.** `∫ x, exp (-(x^2)/(2τ)) = √(2πτ)` for
`0 < τ`, from the pin's `integral_gaussian` at `b = 1/(2τ)`. -/
lemma integral_exp_neg_sq_div_value (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ)) = Real.sqrt (2 * Real.pi * τ) := by
  have e : ∀ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ)) =
      Real.exp (-(1 / (2 * τ)) * x ^ 2) :=
    fun x => by rw [neg_sq_div_eq]
  calc ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ))
      = ∫ x : ℝ, Real.exp (-(1 / (2 * τ)) * x ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = Real.sqrt (Real.pi / (1 / (2 * τ))) := integral_gaussian _
    _ = Real.sqrt (2 * Real.pi * τ) := by
        congr 1
        have hτ' : τ ≠ 0 := ne_of_gt hτ
        field_simp

/-- **1-D 1st moment.** `∫ x, x * exp (-(x^2)/(2τ)) = 0` for
`0 < τ`, by odd symmetry under the measure-preserving negation. -/
lemma integral_mul_exp_neg_sq_div (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : ℝ, x * Real.exp (-(x ^ 2) / (2 * τ)) = 0 := by
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  have e : ∀ x : ℝ, x * Real.exp (-(x ^ 2) / (2 * τ)) =
      x * Real.exp (-(1 / (2 * τ)) * x ^ 2) :=
    fun x => by rw [neg_sq_div_eq]
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  set f : ℝ → ℝ := fun x => x * Real.exp (-(1 / (2 * τ)) * x ^ 2) with hf
  have hneg : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding f
  have hodd : (∫ x : ℝ, f (-x)) = -∫ x : ℝ, f x := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hf, neg_sq]
    ring
  have key : (∫ x : ℝ, f x) = -∫ x : ℝ, f x := by rw [← hodd, hneg]
  linarith

/-- `Real.Gamma (3/2) = (1/2) * √π`, from `Real.Gamma_add_one` and
`Real.Gamma_one_half_eq`. -/
lemma gamma_three_halves : Real.Gamma (3 / 2 : ℝ) = (1 / 2) * Real.sqrt Real.pi := by
  have h : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]

/-- The rpow normalization factor at exponent `-(3/2)`:
`(1/(2τ))^(-(3/2)) = (2τ) * √(2τ)` for `0 < τ`. -/
lemma inv_rpow_neg_three_halves (τ : ℝ) (hτ : 0 < τ) :
    (1 / (2 * τ)) ^ (-(3 : ℝ) / 2) = (2 * τ) * Real.sqrt (2 * τ) := by
  have hpos : (0 : ℝ) ≤ 2 * τ := by positivity
  have h32 : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  rw [one_div, Real.inv_rpow hpos, ← Real.rpow_neg hpos]
  have e : -(-(3 : ℝ) / 2) = 3 / 2 := by ring
  rw [e, h32, Real.rpow_add (by positivity), Real.rpow_one, Real.sqrt_eq_rpow]

/-- **1-D 2nd moment.** `∫ x, x^2 * exp (-(x^2)/(2τ)) = τ * √(2πτ)`
for `0 < τ`, computed from the pin's Gamma–Mellin fact
`integral_rpow_mul_exp_neg_mul_rpow` at `p = q = 2` over `Ioi 0`,
doubled over the line by `integral_comp_abs` (the integrand is
even), with `Real.Gamma (3/2) = (1/2) * √π`. -/
lemma integral_sq_mul_exp_neg_sq_div_value (τ : ℝ) (hτ : 0 < τ) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / (2 * τ)) =
      τ * Real.sqrt (2 * Real.pi * τ) := by
  have hb : (0 : ℝ) < 1 / (2 * τ) := by positivity
  -- The Ioi half-line value, in rpow form.
  have hIoi : ∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 : ℝ) * Real.exp (-(1 / (2 * τ)) * x ^ (2 : ℝ)) =
      (1 / (2 * τ)) ^ (-(3 : ℝ) / 2) * (1 / 2) * ((1 / 2) * Real.sqrt Real.pi) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 : ℝ))
      (b := 1 / (2 * τ)) two_pos (by norm_num) hb
    have e1 : ((2 : ℝ) + 1) / 2 = 3 / 2 := by norm_num
    have e2 : -((2 : ℝ) + 1) / 2 = -(3 : ℝ) / 2 := by ring
    rw [e1, e2, gamma_three_halves] at h
    exact h
  -- Convert the half-line integral to the seat's nat-pow form.
  have hIoi' : ∫ x in Set.Ioi (0 : ℝ),
      x ^ 2 * Real.exp (-(1 / (2 * τ)) * x ^ 2) =
      (1 / (2 * τ)) ^ (-(3 : ℝ) / 2) * (1 / 2) * ((1 / 2) * Real.sqrt Real.pi) := by
    rw [← hIoi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [Real.rpow_two]
  -- Double over the whole line: the integrand is even.
  have hwhole : ∫ x : ℝ, x ^ 2 * Real.exp (-(1 / (2 * τ)) * x ^ 2) =
      2 * ((1 / (2 * τ)) ^ (-(3 : ℝ) / 2) * (1 / 2) * ((1 / 2) * Real.sqrt Real.pi)) := by
    have h := integral_comp_abs
      (f := fun t : ℝ => t ^ 2 * Real.exp (-(1 / (2 * τ)) * t ^ 2))
    rw [hIoi'] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with x
    rw [sq_abs]
  -- Assemble: rewrite the seat exponent and the rpow factor.
  have e : ∀ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / (2 * τ)) =
      x ^ 2 * Real.exp (-(1 / (2 * τ)) * x ^ 2) :=
    fun x => by rw [neg_sq_div_eq]
  rw [integral_congr_ae (Filter.Eventually.of_forall e), hwhole,
    inv_rpow_neg_three_halves τ hτ]
  have hsqrt : Real.sqrt (2 * Real.pi * τ) = Real.sqrt (2 * τ) * Real.sqrt Real.pi := by
    rw [show 2 * Real.pi * τ = (2 * τ) * Real.pi by ring,
      Real.sqrt_mul (by positivity)]
  rw [hsqrt]
  ring

/-! ## §2. The Pi factorization: normalization and moments -/

/-- The normalization factor against the cubed Gaussian root:
`(2πτ)^(−3/2) * √(2πτ)^3 = 1` for `0 < τ`, computed from
`Real.rpow_add` and `Real.sq_sqrt` — the value is the rpow
computation, not an assumption. -/
lemma norm_factor_mul_sqrt_cube (τ : ℝ) (hτ : 0 < τ) :
    (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * (Real.sqrt (2 * Real.pi * τ)) ^ 3 = 1 := by
  have hy : (0 : ℝ) < 2 * Real.pi * τ := by positivity
  have hsqrt3 : (Real.sqrt (2 * Real.pi * τ)) ^ 3 =
      (2 * Real.pi * τ) * Real.sqrt (2 * Real.pi * τ) := by
    have h : (Real.sqrt (2 * Real.pi * τ)) ^ 3 =
        (Real.sqrt (2 * Real.pi * τ)) ^ 2 * Real.sqrt (2 * Real.pi * τ) := by ring
    rw [h, Real.sq_sqrt hy.le]
  have hrpow32 : (2 * Real.pi * τ) ^ ((3 : ℝ) / 2) =
      (2 * Real.pi * τ) * Real.sqrt (2 * Real.pi * τ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hsqrt3, ← hrpow32, ← Real.rpow_add hy,
    show (-(3 : ℝ) / 2) + 3 / 2 = 0 by ring, Real.rpow_zero]

/-- The Pi Gaussian weight integrates to the product of the 1-D
values: over a finite Pi space of cardinality `n`,
`∫ v, exp (−(∑ i, (v i)^2)/(2τ)) = √(2πτ)^n`. Route:
`exp_neg_sumSq_eq_prod` (SE-1), then the pin's product-integral
fact `integral_fintype_prod_eq_prod` over `Measure.pi`, then the
1-D value of §1 at every coordinate. -/
lemma integral_exp_neg_sumSq_value {ι : Type*} [Fintype ι] (τ : ℝ) (hτ : 0 < τ) :
    ∫ v : ι → ℝ, Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) =
      (Real.sqrt (2 * Real.pi * τ)) ^ (Fintype.card ι) := by
  calc ∫ v : ι → ℝ, Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ))
      = ∫ v : ι → ℝ, ∏ i, Real.exp (-((v i) ^ 2) / (2 * τ)) :=
        integral_congr_ae (Filter.Eventually.of_forall (exp_neg_sumSq_eq_prod τ))
    _ = ∏ i, ∫ x : ℝ, Real.exp (-(x ^ 2) / (2 * τ)) := by
        rw [MeasureTheory.volume_pi]
        exact integral_fintype_prod_eq_prod
          (fun (i : ι) (x : ℝ) => Real.exp (-(x ^ 2) / (2 * τ)))
    _ = ∏ _i : ι, Real.sqrt (2 * Real.pi * τ) :=
        Finset.prod_congr rfl (fun i _ => integral_exp_neg_sq_div_value τ hτ)
    _ = (Real.sqrt (2 * Real.pi * τ)) ^ (Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ]

/-- **Item 1 — normalization.** `∫ v, mbDensity τ v = 1` for
`0 < τ`: the density is the constant `(2πτ)^(−3/2)` times the Pi
Gaussian weight, whose integral is `√(2πτ)^3` by
`integral_exp_neg_sumSq_value`, and the product is `1` by
`norm_factor_mul_sqrt_cube`. -/
theorem integral_mbDensity (τ : ℝ) (hτ : 0 < τ) :
    ∫ v, mbDensity τ v ∂(volume : Measure VelocitySpace) = 1 := by
  calc ∫ v, mbDensity τ v ∂(volume : Measure VelocitySpace)
      = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
          ∫ v, Real.exp (-(∑ i, (v i) ^ 2) / (2 * τ)) ∂(volume : Measure VelocitySpace) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with v
        rfl
    _ = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * (Real.sqrt (2 * Real.pi * τ)) ^ 3 := by
        rw [integral_exp_neg_sumSq_value τ hτ, Fintype.card_fin]
    _ = 1 := norm_factor_mul_sqrt_cube τ hτ

/-- Pointwise factorization of the density against a coordinate
power: `mbDensity τ v * (v i)^k` is the normalization constant
times the product over coordinates of `x^(if j = i then k else 0)`
times the 1-D Gaussian weight. -/
lemma mbDensity_mul_coord_pow_eq (τ : ℝ) (i : Fin 3) (k : ℕ) (v : VelocitySpace) :
    mbDensity τ v * (v i) ^ k =
      (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
        ∏ j, ((v j) ^ (if j = i then k else 0) *
          Real.exp (-((v j) ^ 2) / (2 * τ))) := by
  have hpow : ∏ j, (v j) ^ (if j = i then k else 0) = (v i) ^ k := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg hb, pow_zero]
    · simp
  rw [Finset.prod_mul_distrib, ← exp_neg_sumSq_eq_prod, hpow]
  unfold mbDensity
  ring

/-- The factorized integral of the density against a coordinate
power, as the normalization constant times the product of the 1-D
factor integrals. -/
lemma integral_mbDensity_mul_coord_pow (τ : ℝ) (i : Fin 3) (k : ℕ) :
    ∫ v, mbDensity τ v * (v i) ^ k ∂(volume : Measure VelocitySpace) =
      (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
        ∏ j, ∫ x : ℝ, x ^ (if j = i then k else 0) *
          Real.exp (-(x ^ 2) / (2 * τ)) := by
  calc ∫ v, mbDensity τ v * (v i) ^ k ∂(volume : Measure VelocitySpace)
      = ∫ v, (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, ((v j) ^ (if j = i then k else 0) *
            Real.exp (-((v j) ^ 2) / (2 * τ))) ∂(volume : Measure VelocitySpace) :=
        integral_congr_ae (Filter.Eventually.of_forall (mbDensity_mul_coord_pow_eq τ i k))
    _ = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
          ∫ v, ∏ j, ((v j) ^ (if j = i then k else 0) *
            Real.exp (-((v j) ^ 2) / (2 * τ))) ∂(volume : Measure VelocitySpace) :=
        integral_const_mul _ _
    _ = (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, ∫ x : ℝ, x ^ (if j = i then k else 0) *
            Real.exp (-(x ^ 2) / (2 * τ)) := by
        congr 1
        rw [MeasureTheory.volume_pi]
        exact integral_fintype_prod_eq_prod
          (fun (j : Fin 3) (x : ℝ) => x ^ (if j = i then k else 0) *
            Real.exp (-(x ^ 2) / (2 * τ)))

/-- **Item 3 (first raw material) — the coordinate second moment.**
`∫ v, mbDensity τ v * (v i)^2 = τ` for `0 < τ` and every coordinate
`i`: the factorized product is the 1-D second moment `τ√(2πτ)`
times two 1-D 0th moments `√(2πτ)`, and the normalization factor
cancels the resulting `√(2πτ)^3`. -/
theorem integral_mbDensity_mul_coord_sq (τ : ℝ) (hτ : 0 < τ) (i : Fin 3) :
    ∫ v, mbDensity τ v * (v i) ^ 2 ∂(volume : Measure VelocitySpace) = τ := by
  have herase : ∏ j ∈ Finset.univ.erase i, (∫ x : ℝ, x ^ (if j = i then 2 else 0) *
        Real.exp (-(x ^ 2) / (2 * τ))) = (Real.sqrt (2 * Real.pi * τ)) ^ 2 := by
    have h1 : ∀ j ∈ Finset.univ.erase i, (∫ x : ℝ, x ^ (if j = i then 2 else 0) *
        Real.exp (-(x ^ 2) / (2 * τ))) = Real.sqrt (2 * Real.pi * τ) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [if_neg hji]
      simp only [pow_zero, one_mul]
      exact integral_exp_neg_sq_div_value τ hτ
    have hcard : (Finset.univ.erase i).card = 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    rw [Finset.prod_congr rfl h1, Finset.prod_const, hcard]
  have hprod : ∏ j, ∫ x : ℝ, x ^ (if j = i then 2 else 0) *
        Real.exp (-(x ^ 2) / (2 * τ)) =
      (∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / (2 * τ))) *
        (Real.sqrt (2 * Real.pi * τ)) ^ 2 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), herase]
    congr 1
    rw [if_pos rfl]
  rw [integral_mbDensity_mul_coord_pow τ i 2, hprod,
    integral_sq_mul_exp_neg_sq_div_value τ hτ]
  have key : (2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
      (τ * Real.sqrt (2 * Real.pi * τ) * (Real.sqrt (2 * Real.pi * τ)) ^ 2) =
      τ * ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2) * (Real.sqrt (2 * Real.pi * τ)) ^ 3) := by
    ring
  rw [key, norm_factor_mul_sqrt_cube τ hτ, mul_one]

/-- The rectified seat's coordinate: `∫ v, mbDensity τ v * (v 0)^2 = τ`. -/
theorem integral_mbDensity_mul_coord_sq_zero (τ : ℝ) (hτ : 0 < τ) :
    ∫ v, mbDensity τ v * (v 0) ^ 2 ∂(volume : Measure VelocitySpace) = τ :=
  integral_mbDensity_mul_coord_sq τ hτ 0

/-- **Item 3 (second raw material) — the coordinate first moment.**
`∫ v, mbDensity τ v * (v 0) = 0` for `0 < τ`: in the factorized
product, the `j = 0` factor is the 1-D first moment, which is `0`
by odd symmetry (§1). -/
theorem integral_mbDensity_mul_coord (τ : ℝ) (hτ : 0 < τ) :
    ∫ v, mbDensity τ v * (v 0) ∂(volume : Measure VelocitySpace) = 0 := by
  have hfactor : ∫ x : ℝ, x ^ (if (0 : Fin 3) = 0 then (1 : ℕ) else 0) *
      Real.exp (-(x ^ 2) / (2 * τ)) = 0 := by
    rw [if_pos rfl]
    simp only [pow_one]
    exact integral_mul_exp_neg_sq_div τ hτ
  have h := integral_mbDensity_mul_coord_pow τ (0 : Fin 3) 1
  simp only [pow_one] at h
  rw [h, Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) hfactor, mul_zero]

/-- The density times a squared coordinate is integrable for
`0 < τ` (the factorized product of §1's 1-D integrable pieces). -/
lemma integrable_mbDensity_mul_coord_sq (τ : ℝ) (hτ : 0 < τ) (i : Fin 3) :
    Integrable (fun v => mbDensity τ v * (v i) ^ 2) (volume : Measure VelocitySpace) := by
  have hprod : Integrable (fun v : VelocitySpace =>
      ∏ j, ((v j) ^ (if j = i then 2 else 0) *
        Real.exp (-(1 / (2 * τ)) * (v j) ^ 2)))
      (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) := by
    apply Integrable.fintype_prod
      (f := fun (j : Fin 3) (x : ℝ) => x ^ (if j = i then 2 else 0) *
        Real.exp (-(1 / (2 * τ)) * x ^ 2))
    intro j
    by_cases hji : j = i
    · subst hji
      apply (integrable_sq_mul_exp_neg_sq_div τ hτ).congr
      filter_upwards with x
      rw [if_pos rfl, neg_sq_div_eq]
    · apply (integrable_exp_neg_sq_div τ hτ).congr
      filter_upwards with x
      rw [if_neg hji, pow_zero, one_mul, neg_sq_div_eq]
  rw [MeasureTheory.volume_pi]
  apply (hprod.const_mul ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2))).congr
  filter_upwards with v
  rw [mbDensity_mul_coord_pow_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [neg_sq_div_eq]

/-- **The total second moment.** `∫ v, mbDensity τ v * (∑ i, (v i)^2)
= 3τ` for `0 < τ`: the integral of the finite sum is the sum of the
three coordinate second moments, each `τ`. This is the expectation
H1's assembly consumes. -/
lemma integral_mbDensity_mul_sumSq (τ : ℝ) (hτ : 0 < τ) :
    ∫ v, mbDensity τ v * (∑ i, (v i) ^ 2) ∂(volume : Measure VelocitySpace) =
      3 * τ := by
  have hpt : ∀ v : VelocitySpace, mbDensity τ v * (∑ i, (v i) ^ 2) =
      ∑ i, mbDensity τ v * (v i) ^ 2 := fun v => by rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum Finset.univ
      (fun i _ => integrable_mbDensity_mul_coord_sq τ hτ i)]
  have hsum : ∑ i : Fin 3, (∫ v, mbDensity τ v * (v i) ^ 2
      ∂(volume : Measure VelocitySpace)) = ∑ _i : Fin 3, τ :=
    Finset.sum_congr rfl (fun i _ => integral_mbDensity_mul_coord_sq τ hτ i)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [nsmul_eq_mul]

/-! ## §3. H1: the entropy value

The entropy route of the pack: `−∫ p log p = −E[log p]`; `log p`
is affine in the squared norm (SE-1's `log_mbDensity`); the total
second moment is `3τ` (§2); assembly is
`(3/2)·log(2πτ) + 3/2 = (3/2)·log(2πeτ)`. -/

/-- The integrated entropy integrand:
`∫ v, mbDensity τ v * log (mbDensity τ v) = −(3/2)·log(2πτ) − 3/2`
for `0 < τ`. -/
lemma integral_mbDensity_mul_log_value (τ : ℝ) (hτ : 0 < τ) :
    ∫ v, mbDensity τ v * Real.log (mbDensity τ v)
        ∂(volume : Measure VelocitySpace) =
      -(3 / 2 : ℝ) * Real.log (2 * Real.pi * τ) - 3 / 2 := by
  have hpt : ∀ v : VelocitySpace, mbDensity τ v * Real.log (mbDensity τ v) =
      Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) * mbDensity τ v -
        (1 / (2 * τ)) * (mbDensity τ v * (∑ i, (v i) ^ 2)) := by
    intro v
    rw [log_mbDensity τ hτ v]
    ring
  have hintS : Integrable (fun v => mbDensity τ v * (∑ i, (v i) ^ 2))
      (volume : Measure VelocitySpace) := by
    have hsum : Integrable (fun v => ∑ i, mbDensity τ v * (v i) ^ 2)
        (volume : Measure VelocitySpace) :=
      integrable_finsetSum Finset.univ
        (fun i _ => integrable_mbDensity_mul_coord_sq τ hτ i)
    apply hsum.congr
    filter_upwards with v
    rw [Finset.mul_sum]
  have hlogC : Real.log ((2 * Real.pi * τ) ^ (-(3 : ℝ) / 2)) =
      -(3 / 2 : ℝ) * Real.log (2 * Real.pi * τ) := by
    rw [Real.log_rpow (by positivity : (0 : ℝ) < 2 * Real.pi * τ)]
    ring
  have h3 : (1 / (2 * τ)) * (3 * τ) = 3 / 2 := by
    have h2τ : (2 : ℝ) * τ ≠ 0 := ne_of_gt (by positivity)
    rw [one_div, inv_mul_eq_div, div_eq_div_iff h2τ (by norm_num)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub ((integrable_mbDensity τ hτ).const_mul _) (hintS.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_mbDensity τ hτ, integral_mbDensity_mul_sumSq τ hτ, hlogC, h3]
  ring

/-- **Item 2 — H1, the entropy value.** For `0 < τ`,
`diffEntropy (mbDensity τ) = (3/2) * log (2πeτ)`, with SE-1's
`diffEntropy` and `e = Real.exp 1`. Computed by the entropy route:
negate `integral_mbDensity_mul_log_value` and fold
`log (2πeτ) = log (2πτ) + 1`. -/
theorem diffEntropy_mbDensity (τ : ℝ) (hτ : 0 < τ) :
    diffEntropy (mbDensity τ) =
      (3 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * τ) := by
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * τ) =
      Real.log (2 * Real.pi * τ) + 1 := by
    rw [show 2 * Real.pi * Real.exp 1 * τ = (2 * Real.pi * τ) * Real.exp 1 by ring,
      Real.log_mul (by positivity : (2 * Real.pi * τ) ≠ 0)
        (ne_of_gt (Real.exp_pos 1)),
      Real.log_exp]
  unfold diffEntropy
  rw [integral_mbDensity_mul_log_value τ hτ, hlog]
  ring

/-- **H1 discharged.** SE-0 registered `shadowEntropyH1` against an
explicit signature parameter `diffEntropy : (VelocitySpace → ℝ) → ℝ`;
substituting SE-1's `diffEntropy` for that parameter (the
substitution the SE-0/SE-1 headers name), the registered target
holds: this is `shadowEntropyH1 diffEntropy` itself, proved by
`diffEntropy_mbDensity`. -/
theorem shadowEntropyH1_holds : shadowEntropyH1 diffEntropy :=
  fun τ hτ => diffEntropy_mbDensity τ hτ

end ThetLogos
