import ThetLogos.PlaneAvgKernel
import ThetLogos.LatticeGramSeries

/-!
# ThetLogos.PlaneAvgKernelCircle — (H-PF) for `K̄` at the U(1) seat

This module composes two landed results:

* Route C's U(1) Osterwalder–Schrader positivity in
  `LatticeGramSeries.lean`, replayed once at the bounded
  AE-strongly-measurable domain that the integrated Gram criterion
  itself consumes; and
* the plane-averaged-kernel reduction identity in
  `PlaneAvgKernel.lean`.

The conclusion is the diagonal pairing positivity of the
plane-averaged kernel `K̄_β` at `G = Circle`, the defining
representation, `d = 1`, for even `N` and `β ≥ 0`.

Fences: fixed finite volume and fixed `(β, N)`; nothing is uniform
in `N`; there is no continuum statement; Stage 1b-B positivity at
general `(G, ρ)` is not asserted. **NO CLAIM**: this module closes
**0** parts of the Clay Yang–Mills statement, and 0 parts of any
other official statement.

This module is not in the root import list of the library (the
corpus pattern for recent bricks); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- **Route C at the measurable bounded domain.** This is the
hypothesis-relaxation companion to `osForm_circle_nonneg`: Route
C's proof consumes continuity of the strict-half factor only to
obtain AE strong measurability for the integrated Gram criterion,
while its two marginal identities are already stated for arbitrary
`f`. Replaying that final application with `hfA` supplied directly
therefore gives the same positivity on the identity's admissible
domain. -/
theorem osForm_circle_nonneg_aestrongly (hN : Even N) (β : ℝ)
    (hβ : 0 ≤ β)
    (F : Config (Fin 4 → ZMod N) Circle → ℂ)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (osForm (haarProb Circle) circleRep β F F).re
      ∧ (osForm (haarProb Circle) circleRep β F F).im = 0 := by
  have hwR : Summable fun n : ↥(zeroFinset (N := N)) → ℤ => wR β n := by
    rw [show (fun n : ↥(zeroFinset (N := N)) → ℤ => wR β n)
        = fun n => ∏ x : ↥(zeroFinset (N := N)),
            (Real.exp (-β) * besselI β (n x)) from
      funext fun n => rfl]
    exact summable_prod_subtype zeroFinset
      (fun p n => Real.exp (-β) * besselI β n)
      (fun a _ => (summable_besselI_int β).mul_left (Real.exp (-β)))
      (fun a _ n => mul_nonneg (Real.exp_pos _).le
        (besselI_nonneg hβ n))
  have hsum : Summable fun n : ↥(zeroFinset (N := N)) → ℤ =>
      Real.sqrt (wR β n) * Real.sqrt (wR β n) := by
    have e : (fun n : ↥(zeroFinset (N := N)) → ℤ =>
        Real.sqrt (wR β n) * Real.sqrt (wR β n))
        = fun n => wR β n :=
      funext fun n => Real.mul_self_sqrt (wR_nonneg hβ n)
    rwa [e]
  refine osForm_nonneg_of_gram_integrated
    (μG := haarProb Circle) (ρ := circleRep) (d := 1)
    (ι := ↥(zeroFinset (N := N)) → ℤ)
    circleRep_continuous hN (by norm_num) β F f hF
    hfA Cf hfB
    (featA β) (featB hN β) (featXi β)
    (fun n => (featA_continuous β n).aestronglyMeasurable)
    (fun n => (featB_continuous hN β n).aestronglyMeasurable)
    (fun n => Real.sqrt (wR β n)) (fun n => Real.sqrt (wR β n))
    (fun n => Real.sqrt_nonneg _)
    (fun n y => featA_norm_le hβ n y)
    (fun n u => featB_norm_le hN hβ n u)
    hsum dA dB dA_nonneg dB_nonneg ?_ ?_ ?_
  · exact fun y u => gram_identity_circle hN hβ y u
  · exact fun n => marginalA hN β n f
  · exact fun n => marginalB hN β n f

/-- **(H-PF) for the plane-averaged kernel at U(1).** At the U(1)
seat, the diagonal pairing of `K̄_β` on every bounded
AE-strongly-measurable strict-half observable is a nonnegative
real. The proof is the reduction identity read backwards through
the positive partition scalar: the pairing equals
`Z • osForm`, with `Z > 0`, and Route C supplies the sign of the
OS form. -/
theorem planeAvgKernel_circle_pairing_nonneg
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (∫ r, (starRingEnd ℂ) (f r.2)
          * (planeAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
             * f r.1)
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))).re
    ∧ (∫ r, (starRingEnd ℂ) (f r.2)
          * (planeAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
             * f r.1)
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))).im
        = 0 := by
  classical
  let F : Config (Fin 4 → ZMod N) Circle → ℂ :=
    fun U => f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)
  have hF : ∀ U, F U
      = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1) := fun U => rfl
  have hOS : 0 ≤ (osForm (haarProb Circle) circleRep β F F).re
      ∧ (osForm (haarProb Circle) circleRep β F F).im = 0 :=
    osForm_circle_nonneg_aestrongly hN β hβ F f hF hfA Cf hfB
  have hZ : 0 < gibbsPartition (torusShift N) (haarProb Circle)
      circleRep β :=
    gibbsPartition_pos (torusShift N) (haarProb Circle) circleRep
      circleRep_continuous (by norm_num) β
  have hId := osForm_eq_planeAvgKernel
    (μG := haarProb Circle) (ρ := circleRep) (d := 1)
    circleRep_continuous hN (by norm_num) β F f hF hfA ⟨Cf, hfB⟩
  have hQ : (∫ r, (starRingEnd ℂ) (f r.2)
        * (planeAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
           * f r.1)
      ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle)))
      = (gibbsPartition (torusShift N) (haarProb Circle) circleRep β : ℂ)
        * osForm (haarProb Circle) circleRep β F F := by
    have hZne : (gibbsPartition (torusShift N) (haarProb Circle)
        circleRep β : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hZ.ne'
    calc (∫ r, (starRingEnd ℂ) (f r.2)
            * (planeAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
               * f r.1)
          ∂((Measure.pi fun _ : ↥(posLinks (N := N))
              => haarProb Circle).prod
            (Measure.pi fun _ : ↥(posLinks (N := N))
              => haarProb Circle)))
        = (gibbsPartition (torusShift N) (haarProb Circle) circleRep β : ℂ)
          * (((gibbsPartition (torusShift N) (haarProb Circle)
              circleRep β : ℂ))⁻¹
            * ∫ r, (starRingEnd ℂ) (f r.2)
                * (planeAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
                   * f r.1)
              ∂((Measure.pi fun _ : ↥(posLinks (N := N))
                  => haarProb Circle).prod
                (Measure.pi fun _ : ↥(posLinks (N := N))
                  => haarProb Circle))) := by
          rw [mul_inv_cancel_left₀ hZne]
    _ = (gibbsPartition (torusShift N) (haarProb Circle) circleRep β : ℂ)
          * osForm (haarProb Circle) circleRep β F F := by
          rw [hId]
  rw [hQ]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hOS.2]
    simp only [zero_mul, sub_zero]
    exact mul_nonneg hZ.le hOS.1
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp [hOS.2]

end ThetLogos
