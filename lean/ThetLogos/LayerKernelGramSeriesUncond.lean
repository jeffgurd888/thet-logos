/-
# R2-a — the unconditional discharge of the Route B T1 criterion:
# WALL (priced, at full rank)

Brick **R2-a** of the Q3 closable set
(`~/workspace/your_files/q3-closable-scope-2026-11-08.md`, §1 R2
item 2 and §4 item 1): the iterated `integral_tsum` swap for the
layer pairing at an arbitrary gauge-invariant observable, removing
the observable-regularity hypothesis from the landed conditional
discharge `LayerGramSeriesCert.layerKernelPos_of_integrable_obs`
(`LayerKernelGramSeriesCriterion.lean`).

## Verdict: WALL — the scoped shape is false, not merely unproved

The frozen target was: prove the pairing identity
`pairing = ((∑' j, w j * ‖Z j‖² : ℝ) : ℂ)` for **all** `F` by the
Bochner junk-value convention, then assemble
`LayerGramSeriesCert ⇒ LayerKernelPos` unconditionally.

**FACE DISCIPLINE (what the target would have bought):** this
removes a named hypothesis from a landed headline; it buys NO
existence of a certificate anywhere new — a criterion with no
certificate to feed it discharges nothing.

The junk-value extension FAILS, on both sides independently.
The pairing identity is **not** a consequence of the certificate
axioms (`kernel_eq`, measurability, sup bounds, domination) on a
probability space.  Two abstract countermodels (paper, T5 —
`X = A ⊔ B`, `mA, mB > 0`; `F = 1` on `A`, `F = h` on `B` with
`h` measurable and `∫_B |h| = ∞`; `ι = {1,2}`, `w = 1`, features
constant on each region):

* **Model 1 (pairing survives, series side junk-zero).**
  `Φ(A) = (1,1)`, `Φ(B) = (1,-1)`: the Gram kernel has
  `K_AA = K_BB = 2`, `K_AB = K_BA = 0`.  Every
  `B j = conj (Φ j) * F` is non-integrable (its `B`-part is `±h`),
  so every `Z j = 0` by `integral_undef` and the series side is
  `0`.  But the inner integrals are genuine — the cross term
  `K_AB = 0` kills the non-integrable piece — giving inner
  `2 * mA` on `A`, `0` on `B`, and pairing `2 * mA² ≠ 0`.
* **Model 2 (series side survives, pairing junk-zero).**
  `Φ(A) = (1,1)`, `Φ(B) = (0,1)`: Gram kernel
  `[[2,1],[1,1]]`, all entries positive.  `Φ 1` is supported on
  `A`, so `B 1` is integrable, `Z 1 = mA`, series side `mA² ≠ 0`.
  But for `u ∈ A` the inner integrand's `B`-piece is
  `K_AB * h = h`, non-integrable, so the whole inner Bochner
  integral is junk `0`; likewise for `u ∈ B`; pairing `= 0`.

Exact obstructions, pinpointed:

(a) The landed proof's scalar `L = ∫ ‖F‖` cannot be replaced by
    its junk value: `‖Z j‖ ≤ bound j * L` is false when `L` is
    junk `0` yet `Z j ≠ 0` (Model 2, `j = 1` — a feature can
    annihilate exactly the non-integrable part of `F`).
(b) `Z j = 0` for all `j` does not force the pairing to `0`
    (Model 1): region-local genuine contributions survive
    through cross-term cancellation in the kernel, invisible
    to the per-`j` integrals.
(c) Pairing `= 0` by junk inner integrals does not force the
    series side to `0` (Model 2).
(d) The pin's swap lemmas are inapplicable in both models and
    no weaker pin lemma can rescue the scoped shape, because
    the conclusion itself is false there: in
    Mathlib v4.35.0-rc3, `MeasureTheory.integral_tsum`
    (`DominatedConvergence.lean`) requires
    `AEStronglyMeasurable` of every summand and
    `∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞`, and
    `hasSum_integral_of_summable_integral_norm` requires
    `Integrable` of every summand; here the summands
    `c j • (conj (Φ j) * F)` fail integrability and the
    lintegral sum is `∞` in both models.

**What a proof would now require:** fine structure of
`layerKernel` beyond `kernel_eq` — its stratum-integral
definition — i.e. a different, larger brick, not the scoped
standalone analytic lemma.  Per the brick's instructions no
hypothesis was added to force the headline through (that would
re-create the seam under a new name).  The conditional discharge
on `LayerKernelGramSeriesCriterion`'s face stands untouched and
remains the statement of record.  **No kill is armed on this
brick; this is a priced wall, reported at full rank.**

## What this module proves

Only the true per-`j` junk component of the attempted argument,
at T1: if the `j`-th Gram integrand is non-integrable, its Gram
observation is the junk value `0` (`integral_undef`).  Model 1
shows this fact, while true, does **not** assemble into the
pairing identity.

NO CLAIM; dials 0/4; Dial 3 = 0.
-/

import ThetLogos.LayerKernelGramSeriesCriterion

open MeasureTheory
open scoped Matrix ENNReal NNReal Nat

namespace ThetLogos

section GramSeriesUncondSection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (β : ℝ) {ι : Type*} [Countable ι]

namespace LayerGramSeriesCert

variable (cert : LayerGramSeriesCert (N := N) (ι := ι) μG ρ β)
variable (F : (LayerLink N → G) → ℂ)

/-- **The per-`j` junk fact (true component of the R2-a
attempt).**  If the `j`-th Gram integrand
`u ↦ conj (Φ j u) * F u` is not integrable against the product
Haar probability measure, the Gram observation `Z j` is the
Bochner junk value `0`.  This is `integral_undef` read through
the definition of `gramSeriesObs`.  It does NOT extend to the
pairing identity: see this module's face (Model 1) for a
configuration where every `Z j` is junk `0` yet the pairing is
nonzero. -/
theorem gramSeriesObs_eq_zero_of_not_integrable (j : ι)
    (h : ¬ Integrable
      (fun u => (starRingEnd ℂ) (cert.feat j u) * F u)
      (Measure.pi fun _ : LayerLink N => μG)) :
    gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j = 0 :=
  integral_undef h

/-- **The per-`j` series term at a junk observation.**  Under
the same non-integrability, the `j`-th term of the Gram series
`w j * ‖Z j‖²` vanishes — again a true per-`j` fact that does
not assemble: in Model 1 of this module's face *every* term
vanishes while the pairing is `2 * mA² ≠ 0`, because the
pairing's genuine contributions are region-local and cancel
across `j` in the kernel before any per-`j` integral is
taken. -/
theorem gram_term_eq_zero_of_not_integrable (j : ι)
    (h : ¬ Integrable
      (fun u => (starRingEnd ℂ) (cert.feat j u) * F u)
      (Measure.pi fun _ : LayerLink N => μG)) :
    cert.w j
      * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2
      = 0 := by
  rw [gramSeriesObs_eq_zero_of_not_integrable
    (μG := μG) (ρ := ρ) (β := β) cert F j h]
  simp

end LayerGramSeriesCert

end GramSeriesUncondSection

end ThetLogos
