import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import ThetLogos.SolidBodyPolhode
import ThetLogos.SolidBodyPortrait

/-!
# ThetLogos.SolidBodyPeriodQuad — N1: the quadrature period, defined and finite

Stage N1 of the nonlinear rigid-body program (scoping memo
`nonlinear-rigid-scoping-2026-10-26.md` §1), built on the N0
package `SolidBodyPolhode` and the portrait brick
`SolidBodyPortrait`. Fixed body, frozen coefficients, abstract
body only.

## ⚠ Honesty fence — read first

The period defined here is the **quadrature period**: the return
time read off the first integrals by quadrature. That this number
*is* the return time of actual Euler trajectories is stage **N4**
(deferred; L hypothesis-fed / L+ full) and is **not** proved here —
the identification is classical T4. Every use of the word "period"
in this file means the quadrature period.

## What is proved (T1, from definitions/hypotheses; classical core T4)

For a body with `0 < I₁ < I₂ < I₃`, momentum scale `Λ`, and energy
`E` in either open band (top: `Λ/I₂ < 2E < Λ/I₁`; bottom:
`Λ/I₃ < 2E < Λ/I₂`):

* the quadrature period `periodQuad b Λ E` is defined as
  `(2/c) · ∫₀^uMax (u · m1SqOfU · m3SqOfU)^(−1/2) du` with the
  explicit Euler rate constant `c = quadCoeff b = (I₃−I₁)/(I₁I₃)`
  (derivation: `Ṁ₁ = c·M₀·M₂` from the foundation's `eulerRHS_one`,
  quarter-orbit `∫ dM₁/(c·M₀·M₂)`, substitution `u = M₁²`,
  four quarters);
* the quadrature integrand is interval-integrable on
  `0..uMax` in **both** bands
  (`periodQuad_intervalIntegrable_top`,
  `periodQuad_intervalIntegrable_bot`), so `periodQuad` is a
  genuine finite real number there, not a junk value. The endpoint
  singularities are of integrable `−1/2`-power type: at `u = 0`
  from the substitution, at `u = uMax` from the simple root of the
  vanishing affine factor (N0: the other factor is strictly
  positive there, by the portrait brick's band endpoint values).

## Fences

Frozen coefficients throughout; no dynamics, no divergence (that
is stage N2), no identification with trajectory return times
(stage N4). Abstract body only. NO CLAIM. Parts of any official
(Clay) statement closed by this file: 0.
-/

open MeasureTheory

namespace ThetLogos

/-! ## The rate constant and the quadrature period -/

/-- The Euler rate constant of the middle component:
`Ṁ₁ = quadCoeff b · M₀ · M₂` along trajectories, i.e.
`c = (I₃ − I₁)/(I₁·I₃)`. -/
noncomputable def quadCoeff (b : SolidBody) : ℝ :=
  (b.I3 - b.I1) / (b.I1 * b.I3)

theorem quadCoeff_pos (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) : 0 < quadCoeff b :=
  div_pos (sub_pos.mpr (lt_trans h12 h23)) (mul_pos b.I1_pos b.I3_pos)

/-- The quadrature integrand: `(u · M₁²-form · M₃²-form)^(−1/2)`
in the coordinate `u = M₂²` (middle component squared), built from
N0's affine forms. -/
noncomputable def quadIntegrand (b : SolidBody) (Λ E u : ℝ) : ℝ :=
  (u * m1SqOfU b Λ E u * m3SqOfU b Λ E u) ^ (-(1 / 2 : ℝ))

/-- The **quadrature period** at momentum scale `Λ` and energy
`E`: `(2/c)` times the quadrature integral over the feasible
`u`-range `0..uMax`. (Four quarter-orbits, each contributing
`∫ du/(2c·√(u·M₁²·M₃²))`.) Outside the regular bands this is a
formal value; finiteness in the bands is the content of the two
theorems below. -/
noncomputable def periodQuad (b : SolidBody) (Λ E : ℝ) : ℝ :=
  (2 / quadCoeff b) * ∫ u in (0 : ℝ)..(uMax b Λ E), quadIntegrand b Λ E u

/-! ## The analytic core: one affine factor vanishes at `U`, the
other stays `≥ β > 0` -/

/-- Auxiliary integrability: for affine factors `sA·(U − u)`
(vanishing at the right endpoint) and `sB·(rB − u)` (bounded
below by `β > 0` on `[0, U]`), the function
`u ↦ (u · sA(U−u) · sB(rB−u))^(−1/2)` is interval-integrable on
`0..U`. Split at `U/2`: on the left half it is `u^(−1/2)` times a
bounded continuous factor; on the right half it is
`(U−u)^(−1/2)` times a bounded continuous factor. -/
theorem intervalIntegrable_inv_sqrt_vanish
    {sA sB rB U β : ℝ} (hsA : 0 < sA) (hsB : 0 < sB) (hU : 0 < U)
    (hβ : 0 < β) (hB : ∀ u ∈ Set.Icc (0 : ℝ) U, β ≤ sB * (rB - u)) :
    IntervalIntegrable
      (fun u => (u * (sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
      volume 0 U := by
  have hmpos : (0 : ℝ) < U / 2 := by linarith
  have hmU : U / 2 < U := by linarith
  -- The non-vanishing product `A · B` and its positivity on `[0, U]`.
  have hABpos : ∀ u ∈ Set.Icc (0 : ℝ) U,
      0 < (sA * (U - u)) * (sB * (rB - u)) ∨ u = U := by
    intro u hu
    by_cases huU : u = U
    · exact Or.inr huU
    · left
      have hAu : 0 < sA * (U - u) :=
        mul_pos hsA (sub_pos.mpr (lt_of_le_of_ne hu.2 huU))
      have hBu : 0 < sB * (rB - u) := lt_of_lt_of_le hβ (hB u hu)
      exact mul_pos hAu hBu
  -- Left half: `f = u^(−1/2) · ψL` on `Ι 0 (U/2)`.
  have hleft : IntervalIntegrable
      (fun u => (u * (sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
      volume 0 (U / 2) := by
    have hψcont : ContinuousOn
        (fun u => ((sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
        (Set.Icc 0 (U / 2)) := by
      apply ContinuousOn.rpow_const _ (fun u hu => Or.inl ?_)
      · exact ((by fun_prop : Continuous fun u : ℝ =>
          (sA * (U - u)) * (sB * (rB - u)))).continuousOn
      · have huU : u ∈ Set.Icc (0 : ℝ) U :=
          Set.Icc_subset_Icc le_rfl hmU.le hu
        rcases hABpos u huU with h | h
        · exact h.ne'
        · exfalso; rw [h] at hu; exact not_le_of_gt hmU hu.2
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψcont
    have hsub : Set.uIoc 0 (U / 2) ⊆ Set.Icc (0 : ℝ) (U / 2) := by
      rw [← Set.uIcc_of_le hmpos.le]; exact Set.uIoc_subset_uIcc
    have hψaesm : AEStronglyMeasurable
        (fun u => ((sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
        (volume.restrict (Set.uIoc 0 (U / 2))) :=
      (hψcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
    have hψbound : ∀ᵐ u ∂(volume.restrict (Set.uIoc 0 (U / 2))),
        ‖((sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ))‖ ≤ C :=
      ae_restrict_of_forall_mem measurableSet_uIoc
        (fun u hu => hC u (hsub hu))
    have hint : Integrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
        (volume.restrict (Set.uIoc 0 (U / 2))) :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := 0) (b := U / 2) (by norm_num : (-1 : ℝ) < -(1 / 2))).def'
    have hprod : IntervalIntegrable
        (fun u => u ^ (-(1 / 2 : ℝ)) *
          ((sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
        volume 0 (U / 2) :=
      intervalIntegrable_iff.mpr (hint.mul_bdd hψaesm hψbound)
    refine hprod.congr (fun u hu => ?_)
    have hu0 : 0 ≤ u := by
      have : u ∈ Set.Ioc 0 (U / 2) := by
        rwa [Set.uIoc_of_le hmpos.le] at hu
      exact this.1.le
    have hAB : 0 ≤ (sA * (U - u)) * (sB * (rB - u)) := by
      have huU : u ∈ Set.Icc (0 : ℝ) U := ⟨hu0, le_trans (by
        have : u ∈ Set.Ioc 0 (U / 2) := by
          rwa [Set.uIoc_of_le hmpos.le] at hu
        exact this.2) hmU.le⟩
      rcases hABpos u huU with h | h
      · exact h.le
      · rw [h]; simp
    rw [show u * (sA * (U - u)) * (sB * (rB - u))
          = u * ((sA * (U - u)) * (sB * (rB - u))) by ring,
      Real.mul_rpow hu0 hAB]
  -- Right half: `f = (U−u)^(−1/2) · ψR` on `Ι (U/2) U`.
  have hright : IntervalIntegrable
      (fun u => (u * (sA * (U - u)) * (sB * (rB - u))) ^ (-(1 / 2 : ℝ)))
      volume (U / 2) U := by
    have hψcont : ContinuousOn
        (fun u => (sA * (u * (sB * (rB - u)))) ^ (-(1 / 2 : ℝ)))
        (Set.Icc (U / 2) U) := by
      apply ContinuousOn.rpow_const _ (fun u hu => Or.inl ?_)
      · exact ((by fun_prop : Continuous fun u : ℝ =>
          sA * (u * (sB * (rB - u))))).continuousOn
      · have hBu : 0 < sB * (rB - u) :=
          lt_of_lt_of_le hβ (hB u ⟨le_trans hmpos.le hu.1, hu.2⟩)
        exact (mul_pos hsA (mul_pos (lt_of_lt_of_le hmpos hu.1) hBu)).ne'
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψcont
    have hsub : Set.uIoc (U / 2) U ⊆ Set.Icc (U / 2) U := by
      rw [← Set.uIcc_of_le hmU.le]
      exact Set.uIoc_subset_uIcc
    have hψaesm : AEStronglyMeasurable
        (fun u => (sA * (u * (sB * (rB - u)))) ^ (-(1 / 2 : ℝ)))
        (volume.restrict (Set.uIoc (U / 2) U)) :=
      (hψcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
    have hψbound : ∀ᵐ u ∂(volume.restrict (Set.uIoc (U / 2) U)),
        ‖(sA * (u * (sB * (rB - u)))) ^ (-(1 / 2 : ℝ))‖ ≤ C :=
      ae_restrict_of_forall_mem measurableSet_uIoc
        (fun u hu => hC u (hsub hu))
    have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
        volume 0 (U / 2) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp : IntervalIntegrable (fun u : ℝ => (U - u) ^ (-(1 / 2 : ℝ)))
        volume (U / 2) U := by
      have h := (hbase.comp_sub_left U).symm
      -- `h` is over the reflected endpoints; orient it.
      rwa [show U - 0 = U by ring, show U - U / 2 = U / 2 by ring] at h
    have hint : Integrable (fun u : ℝ => (U - u) ^ (-(1 / 2 : ℝ)))
        (volume.restrict (Set.uIoc (U / 2) U)) := hcomp.def'
    have hprod : IntervalIntegrable
        (fun u => (U - u) ^ (-(1 / 2 : ℝ)) *
          (sA * (u * (sB * (rB - u)))) ^ (-(1 / 2 : ℝ)))
        volume (U / 2) U :=
      intervalIntegrable_iff.mpr (hint.mul_bdd hψaesm hψbound)
    refine hprod.congr (fun u hu => ?_)
    have huI : u ∈ Set.Ioc (U / 2) U := by
      rwa [Set.uIoc_of_le hmU.le] at hu
    have hUu : 0 ≤ U - u := sub_nonneg.mpr huI.2
    have hψnn : 0 ≤ sA * (u * (sB * (rB - u))) :=
      mul_nonneg hsA.le (mul_nonneg (le_trans hmpos.le huI.1.le)
        (lt_of_lt_of_le hβ (hB u ⟨le_trans hmpos.le huI.1.le, huI.2⟩)).le)
    rw [show u * (sA * (U - u)) * (sB * (rB - u))
          = (U - u) * (sA * (u * (sB * (rB - u)))) by ring,
      Real.mul_rpow hUu hψnn]
  exact hleft.trans hright

/-! ## Finiteness in the two bands -/

/-- **Finiteness, top band.** For `E` in the top band
(`Λ/I₂ < 2E < Λ/I₁`), the quadrature integrand is
interval-integrable on `0..uMax`, so the quadrature period is a
genuine finite real. The vanishing factor is `m3SqOfU` (its root
`uRoot3` is `uMax`); the other factor `m1SqOfU` stays above its
positive endpoint value there. -/
theorem periodQuad_intervalIntegrable_top (b : SolidBody)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (hband : inTopBand b Λ E) :
    IntervalIntegrable (quadIntegrand b Λ E) volume 0 (uMax b Λ E) := by
  rw [uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband]
  have hβ : 0 < (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) :=
    mul_pos (div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12))
      (sub_pos.mpr hband.1)
  have hs3 := slope3_pos b h12 h23
  have hU : 0 < uRoot3 b Λ E := by
    have h0 : 0 < slope3 b * (uRoot3 b Λ E - 0) := by
      have h := m3SqOfU_zero_pos_of_topBand b h12 h23 Λ E hband
      rwa [m3SqOfU_eq_slope3_mul b h12 h23] at h
    by_contra hcon
    push Not at hcon
    exact absurd h0 (not_lt.mpr
      (mul_nonpos_of_nonneg_of_nonpos hs3.le (by linarith)))
  have hB : ∀ u ∈ Set.Icc (0 : ℝ) (uRoot3 b Λ E),
      (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2)
        ≤ slope1 b * (uRoot1 b Λ E - u) := by
    intro u hu
    have hge : slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
        ≤ slope1 b * (uRoot1 b Λ E - u) :=
      mul_le_mul_of_nonneg_left (by linarith [hu.2])
        (slope1_pos b h12 h23).le
    have heq : slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
        = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) := by
      have h1 : m1SqOfU b Λ E (uMax b Λ E)
          = slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E) := by
        rw [uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband,
          m1SqOfU_eq_slope1_mul b h12 h23]
      rw [← h1]; exact (endpoint_at_uMax_top b h12 h23 Λ E hband).2
    linarith [hge, heq]
  have haux := intervalIntegrable_inv_sqrt_vanish hs3
    (slope1_pos b h12 h23) hU hβ hB
  refine haux.congr (fun u _ => ?_)
  unfold quadIntegrand
  rw [m1SqOfU_eq_slope1_mul b h12 h23, m3SqOfU_eq_slope3_mul b h12 h23]
  congr 1
  ring

/-- **Finiteness, bottom band.** For `E` in the bottom band
(`Λ/I₃ < 2E < Λ/I₂`), the quadrature integrand is
interval-integrable on `0..uMax`, so the quadrature period is a
genuine finite real. The vanishing factor is `m1SqOfU` (its root
`uRoot1` is `uMax`); the other factor `m3SqOfU` stays above its
positive endpoint value there. -/
theorem periodQuad_intervalIntegrable_bot (b : SolidBody)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (hband : inBotBand b Λ E) :
    IntervalIntegrable (quadIntegrand b Λ E) volume 0 (uMax b Λ E) := by
  rw [uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband]
  have hβ : 0 < (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) :=
    mul_pos (div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23))
      (sub_pos.mpr hband.2)
  have hs1 := slope1_pos b h12 h23
  have hU : 0 < uRoot1 b Λ E := by
    have h0 : 0 < slope1 b * (uRoot1 b Λ E - 0) := by
      have h := m1SqOfU_zero_pos_of_botBand b h12 h23 Λ E hband
      rwa [m1SqOfU_eq_slope1_mul b h12 h23] at h
    by_contra hcon
    push Not at hcon
    exact absurd h0 (not_lt.mpr
      (mul_nonpos_of_nonneg_of_nonpos hs1.le (by linarith)))
  have hB : ∀ u ∈ Set.Icc (0 : ℝ) (uRoot1 b Λ E),
      (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E)
        ≤ slope3 b * (uRoot3 b Λ E - u) := by
    intro u hu
    have hge : slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
        ≤ slope3 b * (uRoot3 b Λ E - u) :=
      mul_le_mul_of_nonneg_left (by linarith [hu.2])
        (slope3_pos b h12 h23).le
    have heq : slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
        = (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) := by
      have h1 : m3SqOfU b Λ E (uMax b Λ E)
          = slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E) := by
        rw [uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband,
          m3SqOfU_eq_slope3_mul b h12 h23]
      rw [← h1]; exact (endpoint_at_uMax_bot b h12 h23 Λ E hband).2
    linarith [hge, heq]
  have haux := intervalIntegrable_inv_sqrt_vanish hs1
    (slope3_pos b h12 h23) hU hβ hB
  refine haux.congr (fun u _ => ?_)
  unfold quadIntegrand
  rw [m1SqOfU_eq_slope1_mul b h12 h23, m3SqOfU_eq_slope3_mul b h12 h23]

end ThetLogos
