/-
# S3-0 (companion): the U(1)-seat regression instances

Companion to `Span3GapPins` (brick S3-0 of the Span-3 first
pier). The general-`(G, ρ)` Props of that module, specialized
to the circle seat `(haarProb Circle, circleRep)` (so `d = 1`,
`hd = zero_lt_one`), agree with the landed U(1) Props of
`LatticeUniformGap.lean`. The agreement is definitional —
each `↔` below is `Iff.rfl` — which is the regression
discipline of this brick: the lift did not change the
statements at the seat they were lifted from.

This is a separate module because of the pre-existing tree
defect recorded in `Span3GapPins`' header (the duplicate
declaration `ThetLogos.reflSite_eq_torusShift_zero` in
`LatticeGramSeries` and `PlaneCrossingFactor`): the regression
needs the `LatticeUniformGap` chain, the factorization pin in
`Span3MarginPin` needs the `PolymerPartition` chain, and no
single environment can hold both chains.

**STATEMENTS ONLY**, under the same fences as `Span3GapPins`:
proof-grade distance toward the continuum is ZERO, NO CLAIM,
parts 0, dials 0/4.
-/

import ThetLogos.Span3GapPins
import ThetLogos.LatticeUniformGap

namespace ThetLogos

open MeasureTheory

section Span3U1Regression

variable {N : ℕ} [NeZero N]

/-- Regression: `GapBound` at the U(1) seat *is* `GapBoundU1`,
definitionally. -/
theorem gapBound_iff_gapBoundU1 (β : ℝ) (hN2 : 2 ≤ N) (δ : ℝ) :
    GapBound (haarProb Circle) circleRep circleRep_continuous
        β hN2 δ ↔ GapBoundU1 β hN2 δ :=
  Iff.rfl

/-- Regression: `GapPackage` at the U(1) seat *is*
`GapPackageU1`, definitionally. -/
theorem gapPackage_iff_gapPackageU1 (β : ℝ) (hN2 : 2 ≤ N) :
    GapPackage (haarProb Circle) circleRep circleRep_continuous
        zero_lt_one β hN2 ↔ GapPackageU1 β hN2 :=
  Iff.rfl

/-- Regression: the admissibility class at general `(G, ρ)`
*is* `AdmissibleTrajectoryU1` — it never depended on the
seat. -/
theorem admissibleTrajectory_iff_admissibleTrajectoryU1
    (βt : ℕ → ℝ) :
    AdmissibleTrajectory βt ↔ AdmissibleTrajectoryU1 βt :=
  Iff.rfl

/-- Regression: `UniformVolumeGap` at the U(1) seat *is*
`UniformVolumeGapU1`, definitionally. -/
theorem uniformVolumeGap_iff_uniformVolumeGapU1 (β : ℝ) :
    UniformVolumeGap (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β ↔
      UniformVolumeGapU1 β :=
  Iff.rfl

/-- Regression: `UniformTrajectoryGap` at the U(1) seat *is*
`UniformTrajectoryGapU1`, definitionally. -/
theorem uniformTrajectoryGap_iff_uniformTrajectoryGapU1 :
    UniformTrajectoryGap (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one ↔
      UniformTrajectoryGapU1 :=
  Iff.rfl

/-- Regression: the stated β = 0 uniform instance at the U(1)
seat *is* the same consequent-shape over `GapBoundU1`,
definitionally. (Its per-instance content at the seat is the
landed `gapBoundU1_zero`.) -/
theorem uniformGapBoundZero_iff :
    UniformGapBoundZero (haarProb Circle) circleRep
        circleRep_continuous ↔
      (∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N),
          GapBoundU1 0 hN2 δ) :=
  Iff.rfl

end Span3U1Regression

end ThetLogos
