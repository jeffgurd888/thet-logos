/-
# The completion transport — PARTIAL (A1 + A3 landed; A2
# stopped at the pre-registered slip condition)

The gap clause of `SliceSpectralCorrespondence`
(`SliceBattery`): the one conjunct FG-2c-4 left open.
`GapBoundU1` bounds the spectrum of the PRE-completion
operator `transferOp` on `osSpace`; the battery's pairing
bound lives on the COMPLETED space, for pairings of
`T̂_c = sliceTc`. The scoping memo
(`transport-scoping-2026-10-26.md`, Route A) priced the
transport in three packages:

* **A1 — LANDED here.** The weld `W = sliceWeldCLM`
  extends by continuity to the completion,
  `W_c = W.fromCompletion`, and its three landed
  identities — intertwining, the twisted form identity,
  vacuum-to-vacuum — extend with it. Hence
  `‖W_c y‖² = ⟪y, T̂_c y⟫.re` (the first moment `b₁`),
  `⟪W_c y, transferOp (W_c y)⟫.re = ⟪y, T̂_c² y⟫.re`
  (the second moment `b₂`), and orthogonality to the
  vacuum is preserved.
* **A3 — LANDED here.** The moment step `b₁² ≤ b₂`:
  the landed Jensen recursion at `j = 2`
  (`sliceJensen_moment_pow`: `a₁² ≤ a₂` for the defect
  moments `a_j = ⟪y, Â_c^j y⟫.re`), with
  `a₂ = 1 − 2b₁ + b₂` by the `cfc` pairing splits at
  `T̂_c`.
* **A2 — STOPPED at the slip condition.** The remaining
  package is the `osSpace` form-gap: for `z ⊥ Ω`,
  `⟪z, transferOp z⟫.re ≤ (1 − δ)‖z‖²`, whose scoped
  proof runs through the continuous functional calculus
  at `transferOp` (bump at the isolated spectral point
  `1`; range in `ker (transferOp − 1) = ℂ Ω` by
  `fixed_mem_span`; the function `(1 − δ) + δf − id`
  nonnegative on the spectrum). Its spectrum half IS
  landed here (`transferOp_spectrum_dichotomy_circle`:
  every real spectral point of `transferOp` is `1` or
  `≤ 1 − δ`, from `GapBoundU1` alone), as is the bump
  (`sliceGapBump`). The `cfc` step itself is blocked in
  the pinned Mathlib (v4.35.0-rc3) by an exact
  instance-synthesis failure at the `osSpace` algebra:
  `ContinuousFunctionalCalculus ℝ
  (osSpace →L[ℂ] osSpace) ?p` does not synthesize —
  although every hypothesis of the generic instance
  `IsSelfAdjoint.instContinuousFunctionalCalculus`
  synthesizes standalone for this algebra, and the same
  synthesis succeeds for `sliceTc`'s algebra. The
  generic instance's predicate is `IsSelfAdjoint` under
  the `StarRing`-derived star, which is NOT definitionally
  the corpus's `ContinuousLinearMap.instStarId` star, so
  even a hand-built instance value (via
  `SpectrumRestricts.cfc`) type-mismatches the
  `IsSelfAdjoint (transferOp …)` of every landed lemma;
  one synthesis branch moreover loops through
  `AddSubgroup.seminormedAddCommGroup` on the `Lp`
  coercion. Per the memo's slip condition, A2 alone
  re-prices to L (Route A′ — the compact spectral
  decomposition — is its priced continuation); this
  module lands A1 + A3 as PARTIAL and stops. The gap
  conjunct of the correspondence therefore remains a
  hypothesis, with its remainder reduced to exactly
  A2's statement above.

Fences: fixed volume; Items 3 (uniform estimates) and 4
(continuum) untouched. NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.SliceBattery
import ThetLogos.LatticeSliceIdentify
import ThetLogos.LatticeSliceWeld
import ThetLogos.LatticeUniformGap

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceTransport

variable {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) (hN : Even N)
  (β : ℝ)
  (hpos : SliceHPosOne (haarProb Circle) circleRep hN2
    circleRep_continuous β)

/-! ## A1. The completed weld -/

/-- **The completed weld** `W_c`: the weld `W`, extended
by continuity from the engine quotient to its completion.
`W_c` maps the completed space to `osSpace`. -/
noncomputable def sliceWeldCompleted :
    sliceHilbertSpace (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos →L[ℂ]
      osSpace (N := N) (haarProb Circle) circleRep β :=
  (sliceWeldCLM (haarProb Circle) circleRep hN2
    circleRep_continuous hN β hpos).fromCompletion

/-- The completed weld agrees with the weld on the dense
embedded copy of the engine space. -/
theorem sliceWeldCompleted_apply_embed
    (x : sliceQuotient (haarProb Circle) circleRep hN2
      circleRep_continuous hN β hpos) :
    sliceWeldCompleted hN2 hN β hpos
        (sliceEmbed (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos x)
      = sliceWeldMap (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos x := by
  unfold sliceWeldCompleted
  rw [sliceEmbed_apply (haarProb Circle) circleRep hN2
    circleRep_continuous hN β hpos x]
  exact ContinuousLinearMap.fromCompletion_apply_coe _ _

/-- **A1(i) — intertwining on the completion:**
`W_c ∘ T̂_c = transferOp ∘ W_c`, extended from
`sliceWeldMap_sliceHat` by density. -/
theorem sliceWeldCompleted_intertwining
    (u : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos) :
    sliceWeldCompleted hN2 hN β hpos
        (sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos u)
      = transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β
          (sliceWeldCompleted hN2 hN β hpos u) := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq
      ((sliceWeldCompleted hN2 hN β hpos).continuous.comp
        (sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos).continuous)
      ((transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β).continuous.comp
        (sliceWeldCompleted hN2 hN β hpos).continuous)
  · intro a
    rw [← sliceEmbed_apply (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos a,
      sliceTc_apply (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos _,
      sliceHatCompletedFun_embed (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos a,
      sliceWeldCompleted_apply_embed hN2 hN β hpos _,
      sliceWeldCompleted_apply_embed hN2 hN β hpos a]
    exact sliceWeldMap_sliceHat (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos a

/-- **A1(ii) — the twisted form identity on the
completion:** `⟪W_c u, W_c v⟫ = ⟪u, T̂_c v⟫`, extended
from `sliceWeldMap_inner` by density. -/
theorem sliceWeldCompleted_inner
    (u v : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos) :
    inner ℂ (sliceWeldCompleted hN2 hN β hpos u)
        (sliceWeldCompleted hN2 hN β hpos v)
      = inner ℂ u (sliceTc (haarProb Circle) circleRep
          hN2 circleRep_continuous hN β hpos v) := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
  · exact isClosed_eq
      (((sliceWeldCompleted hN2 hN β hpos).continuous.comp
          continuous_fst).inner
        ((sliceWeldCompleted hN2 hN β hpos).continuous.comp
          continuous_snd))
      (continuous_fst.inner
        ((sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos).continuous.comp
          continuous_snd))
  · intro a b
    rw [← sliceEmbed_apply (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos a,
      ← sliceEmbed_apply (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos b,
      sliceWeldCompleted_apply_embed hN2 hN β hpos a,
      sliceWeldCompleted_apply_embed hN2 hN β hpos b,
      sliceTc_apply (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos _,
      sliceHatCompletedFun_embed (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos b,
      sliceEmbed_inner (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos a
        (sliceHat (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos b)]
    exact sliceWeldMap_inner (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos a b

/-- **A1(iii) — vacuum to vacuum on the completion:**
the completed weld sends the completed vacuum to the
OS vacuum. -/
theorem sliceWeldCompleted_vacuum :
    sliceWeldCompleted hN2 hN β hpos
        (sliceOmegaCompleted (haarProb Circle) circleRep
          hN2 circleRep_continuous hN β hpos zero_lt_one)
      = osVacuum (haarProb Circle) circleRep
          circleRep_continuous zero_lt_one β := by
  show sliceWeldCompleted hN2 hN β hpos
      (sliceEmbed (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos
        (sliceOmega (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos zero_lt_one))
    = _
  rw [sliceWeldCompleted_apply_embed hN2 hN β hpos _]
  exact sliceWeldMap_sliceOmega (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β hpos zero_lt_one

/-- **First moment:** the completed weld's squared norm
is the transfer pairing, `‖W_c y‖² = ⟪y, T̂_c y⟫.re`. -/
theorem sliceWeldCompleted_norm_sq
    (y : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos) :
    ‖sliceWeldCompleted hN2 hN β hpos y‖ ^ 2
      = (inner ℂ y (sliceTc (haarProb Circle) circleRep
          hN2 circleRep_continuous hN β hpos y)).re := by
  have h := sliceWeldCompleted_inner hN2 hN β hpos y y
  have hre := congrArg Complex.re h
  rw [inner_self_eq_norm_sq_to_K] at hre
  norm_cast at hre

/-- **Second moment:** the completed weld transports
the second transfer moment,
`⟪W_c y, transferOp (W_c y)⟫.re = ⟪y, T̂_c² y⟫.re`. -/
theorem sliceWeldCompleted_second_moment
    (y : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos) :
    (inner ℂ (sliceWeldCompleted hN2 hN β hpos y)
      (transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β
          (sliceWeldCompleted hN2 hN β hpos y))).re
      = (inner ℂ y (((sliceTc (haarProb Circle) circleRep
            hN2 circleRep_continuous hN β hpos) ^ 2)
          y)).re := by
  have h2 : ((sliceTc (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos) ^ 2) y
      = sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos
          (sliceTc (haarProb Circle) circleRep hN2
            circleRep_continuous hN β hpos y) := by
    rw [pow_two]
    rfl
  rw [← sliceWeldCompleted_intertwining hN2 hN β hpos y,
    sliceWeldCompleted_inner hN2 hN β hpos y
      (sliceTc (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos y),
    h2]

/-- **Orthogonality is preserved:** a vector of the
completed space orthogonal to the completed vacuum
welds to a vector orthogonal to the OS vacuum. -/
theorem sliceWeldCompleted_orthogonal
    (y : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos)
    (hy : inner ℂ y (sliceOmegaCompleted (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos
          zero_lt_one) = 0) :
    inner ℂ (sliceWeldCompleted hN2 hN β hpos y)
        (osVacuum (haarProb Circle) circleRep
          circleRep_continuous zero_lt_one β) = 0 := by
  rw [← sliceWeldCompleted_vacuum hN2 hN β hpos,
    sliceWeldCompleted_inner hN2 hN β hpos y
      (sliceOmegaCompleted (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos zero_lt_one),
    sliceTc_apply (haarProb Circle) circleRep hN2
      circleRep_continuous hN β hpos _,
    sliceHatCompletedFun_omega (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos zero_lt_one]
  exact hy

/-! ## A2. The `osSpace` form-gap -/

/-- **The spectral bump at the isolated point `1`:**
`0` at and below the gap edge `1 − δ`, ramping linearly
to `1` at `μ = 1`. It is built for the stopped A2 step:
its `cfc` image at `transferOp` would be the projection
onto the vacuum line, with no spectral-projection API
needed — the bump itself is landed; the `cfc` wiring is
what is stopped (see the header). -/
noncomputable def sliceGapBump (δ : ℝ) : ℝ → ℝ :=
  fun μ => max (μ - (1 - δ)) 0 * δ⁻¹

/-- The bump is continuous. -/
theorem sliceGapBump_continuous (δ : ℝ) :
    Continuous (sliceGapBump δ) :=
  ((continuous_id.sub continuous_const).max
    continuous_const).mul continuous_const

/-- The bump vanishes at and below the gap edge. -/
theorem sliceGapBump_eq_zero (δ : ℝ) {μ : ℝ}
    (hμ : μ ≤ 1 - δ) : sliceGapBump δ μ = 0 := by
  show max (μ - (1 - δ)) 0 * δ⁻¹ = 0
  rw [max_eq_right (sub_nonpos.mpr hμ), zero_mul]

/-- The bump is `1` at the vacuum eigenvalue. -/
theorem sliceGapBump_one (δ : ℝ) (hδ0 : 0 < δ) :
    sliceGapBump δ 1 = 1 := by
  show max (1 - (1 - δ)) 0 * δ⁻¹ = 1
  rw [show (1 : ℝ) - (1 - δ) = δ by ring,
    max_eq_left hδ0.le, mul_inv_cancel₀ hδ0.ne']

/-! ## A2. The spectrum dichotomy (the `cfc` half of
A2 is stopped at the slip condition — see the header) -/

/-- **A2, spectrum half — the dichotomy.** Every real
spectral point of the circle seat's transfer operator
is either the vacuum eigenvalue `1` or lies at or below
the gap edge `1 − δ`. From `GapBoundU1` alone (through
the self-adjoint real/complex spectrum bridge); no sign
information is needed. This is the input the stopped
`cfc` step would have consumed. -/
theorem transferOp_spectrum_dichotomy_circle
    (hN' : Even N) (δ : ℝ) (hgap : GapBoundU1 β hN2 δ) :
    ∀ μ ∈ spectrum ℝ (transferOp (haarProb Circle)
        circleRep hN2 circleRep_continuous β),
      μ = 1 ∨ μ ≤ 1 - δ := by
  have hsaT : IsSelfAdjoint (transferOp (haarProb Circle)
      circleRep hN2 circleRep_continuous β) :=
    transferOp_isSelfAdjoint (haarProb Circle) circleRep
      hN2 circleRep_continuous hN' β
  intro μ hμ
  by_cases h1 : μ = 1
  · exact Or.inl h1
  · right
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ (transferOp
        (haarProb Circle) circleRep hN2
          circleRep_continuous β) :=
      (IsSelfAdjoint.coe_mem_spectrum_complex hsaT).mpr hμ
    have hne : (μ : ℂ) ≠ 1 := by exact_mod_cast h1
    have hle := hgap (μ : ℂ) hμℂ hne
    rw [Complex.norm_real] at hle
    exact le_trans (le_abs_self μ) hle

/-! ## A3. The moment step -/

/-- **A3 — the moment step:** for a unit vector `y` of
the completed space, `b₁² ≤ b₂` for the transfer
moments `b_j = ⟪y, T̂_c^j y⟫.re`. The landed Jensen
recursion at `j = 2`, read through
`Â_c² = 1 − 2T̂_c + T̂_c²`. -/
theorem sliceTransport_moment_sq
    (y : sliceHilbertSpace (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos)
    (hy : ‖y‖ = 1) :
    (inner ℂ y (sliceTc (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos y)).re ^ 2
      ≤ (inner ℂ y (((sliceTc (haarProb Circle) circleRep
            hN2 circleRep_continuous hN β hpos) ^ 2)
          y)).re := by
  have ha1nn : 0 ≤ sliceJensenMoment (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos y 1 := by
    rw [← sliceJensen_first_moment (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos y]
    exact sliceCfc_pairing_nonneg (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos
      (fun μ : ℝ => 1 - μ) (fun μ hμ => sub_nonneg.mpr hμ.2) y
  have hb1nn : 0 ≤ (inner ℂ y (sliceTc (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos y)).re := by
    rw [← sliceCfc_id (haarProb Circle) circleRep hN2
      circleRep_continuous hN β hpos]
    exact sliceCfc_pairing_nonneg (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos
      (fun μ : ℝ => μ) (fun μ hμ => hμ.1) y
  have hTc := sliceJensen_tc_pairing (haarProb Circle)
    circleRep hN2 circleRep_continuous hN β hpos y hy
  have ha1le : sliceJensenMoment (haarProb Circle)
      circleRep hN2 circleRep_continuous hN β hpos y 1
      ≤ 1 := by linarith
  have hpow := sliceJensen_moment_pow (haarProb Circle)
    circleRep hN2 circleRep_continuous hN β hpos y hy
    ha1nn ha1le 2
  -- The second defect moment expands as `1 − 2b₁ + b₂`
  -- through the `cfc` pairing splits at `T̂_c`.
  have hexp : sliceJensenMoment (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos y 2
      = 1 - 2 * (inner ℂ y (sliceTc (haarProb Circle)
            circleRep hN2 circleRep_continuous hN β hpos
            y)).re
        + (inner ℂ y (((sliceTc (haarProb Circle) circleRep
              hN2 circleRep_continuous hN β hpos) ^ 2)
            y)).re := by
    have hfun : (fun μ : ℝ => (1 - μ) ^ 2)
        = (fun μ : ℝ => (1 - (μ + μ)) + μ ^ 2) := by
      funext μ
      ring
    unfold sliceJensenMoment
    rw [← sliceCfc_defect_pow (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos 2, hfun,
      sliceJensen_pairing_add (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos
        (fun μ : ℝ => 1 - (μ + μ)) (fun μ : ℝ => μ ^ 2)
        (continuous_const.sub
          (continuous_id.add continuous_id))
        (continuous_id.pow 2) y,
      sliceJensen_pairing_sub (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos
        (fun _ : ℝ => (1 : ℝ)) (fun μ : ℝ => μ + μ)
        continuous_const (continuous_id.add continuous_id) y,
      sliceJensen_pairing_add (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos
        (fun μ : ℝ => μ) (fun μ : ℝ => μ) continuous_id
        continuous_id y,
      sliceCfc_pairing_const (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos 1 y,
      sliceCfc_id (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos,
      sliceCfc_pow (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos 2, hy]
    norm_num
    ring
  have ha1 : sliceJensenMoment (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β hpos y 1
    = 1 - (inner ℂ y (sliceTc (haarProb Circle) circleRep
        hN2 circleRep_continuous hN β hpos y)).re := by
    linarith
  rw [ha1] at hpow
  have hsq : (1 - (inner ℂ y (sliceTc (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos y)).re) ^ 2
      = 1 - 2 * (inner ℂ y (sliceTc (haarProb Circle)
          circleRep hN2 circleRep_continuous hN β hpos y)).re
        + (inner ℂ y (sliceTc (haarProb Circle) circleRep
            hN2 circleRep_continuous hN β hpos y)).re ^ 2 := by
    ring
  rw [hsq] at hpow
  linarith

end SliceTransport

end ThetLogos
