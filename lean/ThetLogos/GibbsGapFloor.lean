import Mathlib

/-!
# GAPFLOOR-1 (DRAFT) — the finite Gibbs gap floor

Parent enrollment #3 (2026-11-12 00:53 EST, Zero:
"build it"), from the parent's 00:51 scope. The
finite Boltzmann pricing of a gap: at a finite seat
with ground energy `m` and a gap `Δ > 0` above it,
the total Gibbs weight of the excited states is at
most `(number of excited states) · exp (−β·Δ)`, and
the same bound holds for the normalized Gibbs
probability of the excited set, because the shifted
partition sum is `≥ 1` from the ground term alone.

## Header fence

Finite Gibbs combinatorics. This is the
Boltzmann-pricing of a gap floor — it is NOT the
Yang–Mills mass gap, and nothing here touches,
prices, or moves Dial 3 (= 0, untouched). A theorem
about finite exponential sums at any finite seat.
Dial-ineligible; NO CLAIM; dials 0/4.

## Vocabulary note (the enrollment's reuse check)

The tree's Gibbs vocabulary was checked first
(2026-11-12): `GibbsSpan.gibbsWeightsE` is the
unshifted weight `exp (−(β * E j + logZ))` at the
`Fin N` seat with an explicit `logZ` parameter;
`gibbsSum_pos` is positivity of the unshifted sum;
`FiniteEntropy.entropyW` is the entropy functional
at a general `Fintype` seat; `FlowKernel`'s
`kms_iff_gibbs` is an (unproved) Prop, not weight
vocabulary. The pinned statement shape of this
brick — a general `Fintype ι` seat and SHIFTED
weights `exp (−β * (E i − m))` summed over the
excited set — matches none of those forms exactly,
so the brick states its sums directly in the pinned
shape. (At the `Fin N` seat the shifted weight is
`gibbsWeightsE β (fun i => E i − m) 0 i`; the
general-seat, Finset-summed form is what is pinned.)
Names coined in this brick (all reported to the
parent): the module name `GibbsGapFloor`, and
`gapExcitedSet`, `gibbsGapFloor_min`,
`gibbsGapFloor_unnorm`,
`gibbsGapFloor_partition_ge_one`,
`gibbsGapFloor_prob`.

## Seat discipline (hypotheses = the pinned seat)

`m` enters through the gap hypothesis itself:
`∀ i, E i ≠ m → m + Δ ≤ E i` with `0 < Δ` FORCES
`m` to be the minimum of `E` (any state below `m`
would satisfy the gap inequality and hence lie
above `m` — `gibbsGapFloor_min` proves exactly
this), and attainment (`∃ i₀, E i₀ = m`) is the one
further seat fact the normalized form consumes.
No hypothesis is carried that a proof does not use.
-/

namespace ThetLogos

/-- The excited set of `E` at reference level `m`:
the states whose energy is not `m`. -/
noncomputable def gapExcitedSet {ι : Type*} [Fintype ι] (E : ι → ℝ) (m : ℝ) :
    Finset ι :=
  Finset.univ.filter (fun i => E i ≠ m)

/-- The gap condition makes `m` the minimum: with
`0 < Δ`, any state with `E i ≠ m` has
`m + Δ ≤ E i`, so no state lies below `m`. -/
theorem gibbsGapFloor_min {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (m Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ i, E i ≠ m → m + Δ ≤ E i) :
    ∀ i, m ≤ E i := by
  intro i
  by_contra h
  push_neg at h
  have hne : E i ≠ m := ne_of_lt h
  have := hgap i hne
  linarith

/-- GAPFLOOR-1 (1) — the unnormalized shifted
excited weight bound, termwise: at `β ≥ 0`, the
total shifted weight of the excited states is at
most the number of excited states times
`exp (−β·Δ)`. -/
theorem gibbsGapFloor_unnorm {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (m Δ β : ℝ) (hβ : 0 ≤ β) (hΔ : 0 < Δ)
    (hgap : ∀ i, E i ≠ m → m + Δ ≤ E i) :
    ∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m)))
      ≤ (gapExcitedSet E m).card * Real.exp (-(β * Δ)) := by
  have hterm : ∀ i ∈ gapExcitedSet E m,
      Real.exp (-(β * (E i - m))) ≤ Real.exp (-(β * Δ)) := by
    intro i hi
    have hi' : E i ≠ m := by
      have := Finset.mem_filter.mp hi
      exact this.2
    have hge := hgap i hi'
    apply Real.exp_le_exp.mpr
    have h1 : Δ ≤ E i - m := by linarith
    have h2 : β * Δ ≤ β * (E i - m) :=
      mul_le_mul_of_nonneg_left h1 hβ
    linarith
  calc ∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m)))
      ≤ (gapExcitedSet E m).card • Real.exp (-(β * Δ)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (gapExcitedSet E m).card * Real.exp (-(β * Δ)) := by
        rw [nsmul_eq_mul]

/-- The shifted partition sum is `≥ 1`: the ground
term alone contributes `exp 0 = 1` and every term is
positive. Attainment is the only seat fact used. -/
theorem gibbsGapFloor_partition_ge_one {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (m β : ℝ) (i₀ : ι) (h₀ : E i₀ = m) :
    1 ≤ ∑ i, Real.exp (-(β * (E i - m))) := by
  have hterm : Real.exp (-(β * (E i₀ - m))) = 1 := by
    rw [h₀, sub_self, mul_zero, neg_zero, Real.exp_zero]
  have hle : Real.exp (-(β * (E i₀ - m)))
      ≤ ∑ i, Real.exp (-(β * (E i - m))) :=
    Finset.single_le_sum (f := fun i => Real.exp (-(β * (E i - m))))
      (fun i _ => le_of_lt (Real.exp_pos _))
      (Finset.mem_univ i₀)
  rwa [hterm] at hle

/-- GAPFLOOR-1 (2) — the normalized form: with
`Z = ∑ i, exp (−β * (E i − m))` (so `Z ≥ 1` by the
ground term), the Gibbs probability of the excited
set — its shifted weight divided by `Z` — obeys
the same floor: at most `(number of excited
states) · exp (−β·Δ)`. -/
theorem gibbsGapFloor_prob {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (m Δ β : ℝ) (hβ : 0 ≤ β) (hΔ : 0 < Δ)
    (hgap : ∀ i, E i ≠ m → m + Δ ≤ E i)
    (i₀ : ι) (h₀ : E i₀ = m) :
    (∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m))))
        / (∑ i, Real.exp (-(β * (E i - m))))
      ≤ (gapExcitedSet E m).card * Real.exp (-(β * Δ)) := by
  have hZ : (1 : ℝ) ≤ ∑ i, Real.exp (-(β * (E i - m))) :=
    gibbsGapFloor_partition_ge_one E m β i₀ h₀
  have hnum_nonneg :
      0 ≤ ∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m))) :=
    Finset.sum_nonneg (fun i _ => le_of_lt (Real.exp_pos _))
  have hdiv : (∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m))))
        / (∑ i, Real.exp (-(β * (E i - m))))
      ≤ ∑ i ∈ gapExcitedSet E m, Real.exp (-(β * (E i - m))) :=
    div_le_self hnum_nonneg hZ
  exact le_trans hdiv (gibbsGapFloor_unnorm E m Δ β hβ hΔ hgap)

end ThetLogos
