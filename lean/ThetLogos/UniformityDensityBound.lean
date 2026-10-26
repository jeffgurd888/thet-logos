/-
# ThetLogos.UniformityDensityBound — Brick U-0: the
pointwise kernel floor

Brick U-0 (Q0 in the scoping), from
`routeb-general-scratch/uniformity-attack-scoping-2026-10-26.md`
§5, priced S there. The scoping's finding: the landed
per-instance U(1) gap is assembled with no explicit modulus
in `(β, N)` — positivity of `δ = 1 - sSup R` is obtained
qualitatively, by contradiction with vacuum simplicity at
`hr_lt`, and HDen's explicit density bounds are consumed
only through compactness. This brick lands the one missing
quantitative companion the scoping identified: the
pointwise **lower** bound on the HDen kernel `kReal`,
mirroring the landed upper bound `kReal_le`
(`LatticeHdenSeat`).

## What is proved

* **`jDensity_toReal_ge`**: the lower companion to the
  landed `jDensity_toReal_le` — the two-slice density read
  as a real number is at least `exp (-2 * actionBound β)`,
  from `jDensity_ge` by `ENNReal.toReal_mono`.
* **`kReal_ge` (U-0)**: for all real `β`, `2 ≤ N`, and
  every product point `p`,
  `exp (-6 * actionBound β) ≤ kReal μG ρ hN2 β p`,
  pointwise, with no a.e. weakening and no seat
  restriction. Assembled from `jDensity_ge` and
  `sliceDensity_le` through the already-landed real
  windows (`sliceDensity_toReal_mem`), by the division
  estimate dual to `kReal_le`.
* **`hdKernel_re_ge`**: the same floor for the real value
  of the candidate `HDen` kernel `hdKernel`.

## Fences — read before citing

This brick is a **density bound only**. It states and
implies **no spectral gap and no uniformity**: no
`GapBoundU1`, no `(U-vol)`, no `(U-traj)` is asserted or
follows from this module alone. The Doeblin candidate this
floor would feed is the modulus
`δ₀(β, N) = exp (-6 * actionBound β)` — at `β > 0` that
is `exp (-192 * β * N ^ 4)`, which **decays exponentially
in `N`** at every fixed `β > 0`, so its infimum over `N`
is `0` and it yields **no (U-vol) regime** (scoping §2).
Coupling the floor to a gap is the separate, unbuilt
brick Q1 of the scoping; a genuine uniformity theorem
remains L+ / research program (scoping §3, Q2).

**NO CLAIM** — parts of any Clay statement closed by
this module: 0. Dials: 0/4. Uniformity across `N` remains
OPEN.
-/

import ThetLogos.LatticeHdenSeat

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The two-slice density, read as a real number, is
bounded below by `exp (-2 * actionBound β)`: the lower
companion to the landed `jDensity_toReal_le`, from
`jDensity_ge` by monotonicity of `ENNReal.toReal`. -/
theorem jDensity_toReal_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    Real.exp (-2 * actionBound (N := N) β)
      ≤ (jDensity μG ρ hN2 β p).toReal := by
  have hne : jDensity μG ρ hN2 β p ≠ ⊤ :=
    ne_top_of_le_ne_top (densityHi_ne_top (N := N) β)
      (jDensity_le μG ρ hρcont hd hN2 β p)
  calc Real.exp (-2 * actionBound (N := N) β)
      = (densityLo (N := N) β).toReal :=
        (ENNReal.toReal_ofReal (Real.exp_nonneg _)).symm
    _ ≤ (jDensity μG ρ hN2 β p).toReal :=
        ENNReal.toReal_mono hne
          (jDensity_ge μG ρ hρcont hd hN2 β p)

/-- **Brick U-0 — the kernel floor.** The candidate `HDen`
density `kReal`, read pointwise, is bounded below by
`exp (-6 * actionBound β)`: the numerator `jDensity` is
at least `exp (-2 * actionBound β)`
(`jDensity_toReal_ge`) and each marginal density in the
denominator is at most `exp (2 * actionBound β)` (the
upper half of `sliceDensity_toReal_mem`, from
`sliceDensity_le`). The exact dual of the landed
`kReal_le`. A density bound only — no gap, no uniformity
is stated; see the module header. -/
theorem kReal_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    Real.exp (-6 * actionBound (N := N) β)
      ≤ kReal μG ρ hN2 β p := by
  have h1 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.1).2
  have h2 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.2).2
  have hl1 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.1).1
  have hl2 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.2).1
  have hpos : 0 < (sliceDensity (N := N) μG ρ β p.1).toReal
      * (sliceDensity (N := N) μG ρ β p.2).toReal :=
    mul_pos (lt_of_lt_of_le (Real.exp_pos _) hl1)
      (lt_of_lt_of_le (Real.exp_pos _) hl2)
  rw [show kReal μG ρ hN2 β p
      = (jDensity μG ρ hN2 β p).toReal
        / ((sliceDensity (N := N) μG ρ β p.1).toReal
          * (sliceDensity (N := N) μG ρ β p.2).toReal) from rfl,
    le_div_iff₀ hpos]
  calc Real.exp (-6 * actionBound (N := N) β)
        * ((sliceDensity (N := N) μG ρ β p.1).toReal
          * (sliceDensity (N := N) μG ρ β p.2).toReal)
      ≤ Real.exp (-6 * actionBound (N := N) β)
          * (Real.exp (2 * actionBound (N := N) β)
            * Real.exp (2 * actionBound (N := N) β)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h1 h2 ENNReal.toReal_nonneg
            (Real.exp_nonneg _))
          (Real.exp_nonneg _)
    _ = Real.exp (-2 * actionBound (N := N) β) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ (jDensity μG ρ hN2 β p).toReal :=
        jDensity_toReal_ge μG ρ hρcont hd hN2 β p

/-- The kernel floor for the real value of the candidate
`HDen` kernel `hdKernel`: the casting form of `kReal_ge`
registered in the scoping (§5). -/
theorem hdKernel_re_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    Real.exp (-6 * actionBound (N := N) β)
      ≤ (hdKernel μG ρ hN2 β p).re := by
  have hre : (hdKernel μG ρ hN2 β p).re = kReal μG ρ hN2 β p :=
    Complex.ofReal_re _
  rw [hre]
  exact kReal_ge μG ρ hρcont hd hN2 β p

end ThetLogos
