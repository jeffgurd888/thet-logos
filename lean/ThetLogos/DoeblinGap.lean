/-
# ThetLogos.DoeblinGap — Brick Q1: the Doeblin step, an
explicit per-instance gap bound

From `routeb-general-scratch/uniformity-attack-scoping-2026-10-26.md`
§2–§3 (brick Q1 there, priced M), on top of brick U-0
(`ThetLogos.UniformityDensityBound`, the pointwise kernel
floor). The corpus's landed per-instance gap
(`transfer_gap_of_formPos`) is qualitative: its
`δ = 1 - sSup R` is a spectral tautology, and positivity of
`δ` comes from contradiction with vacuum simplicity at
`hr_lt` — no modulus in `(β, N)` is ever produced. This
brick assembles the Doeblin/minorization route out of
landed ingredients and produces the explicit modulus

  `δ₀(β, N) = Real.exp (-6 * actionBound (N := N) β)`,

which at `β > 0` is `exp (-192 * β * N ^ 4)` (the scoping's
candidate; the constant is verified in Lean below,
`actionBound_eq_volume`: `actionBound β = |β| * (32 * N^4)`,
and the corpus-native form is valid for **all real `β`**,
since `actionBound` already carries `|β|`).

## What is proved

* **Minorization (§1–§2).** `kReal ≥ δ₀` pointwise (U-0),
  and both marginals of `kReal` against the slice measure
  are `1` a.e. — the two-slice law's marginals are both the
  slice measure (definition + stationarity), transported
  through Claim D's density form
  (`twoSliceMeasure_eq_kernelDensity`) by an abstract
  marginal-of-`withDensity` lemma. Hence the residual
  kernel `s = kReal - δ₀ ≥ 0` has both marginals `1 - δ₀`.
* **Compression (§3).** For `f : osSpace` with
  `⟪osVacuum, f⟫ = 0`, the transfer form compresses:
  `‖⟪f, T f⟫‖ ≤ (1 - δ₀) * ‖f‖ ^ 2`. The proof is the
  form identity for the HDen kernel (`hdKernel`, from
  `LatticeHdenSeat`'s discharged `HDen` package — routed
  here through the corpus's two-slice form identity and
  Claim D, since the package's existential hides its
  kernel) split at the integrand into the residual
  kernel and the constant kernel — the constant piece is
  `δ₀ * (∫ star f) * (∫ f) = 0` on the vacuum-orthogonal
  subspace — followed by Tonelli and AM–GM against the
  two marginals of `s`. This is the Doeblin decomposition
  `T = δ₀ E + (1 - δ₀) R` read at the level of the form.
* **Spectrum (§4).** The transfer operator is compact at
  general `(G, ρ)` for all real `β`
  (`transferOp_compact_of_HDen` ∘ `hden_all`, with a
  Hilbert basis carried as data, the corpus's own
  convention in `gapBoundU1_zero`). Every spectral point
  `λ ≠ 1` therefore satisfies the **explicit bound**
  `‖λ‖ ≤ 1 - δ₀`, at general `(G, ρ)`, every even `N ≥ 2`,
  all real `β` (`transfer_spectrum_le_doeblin`). At the
  circle seat this is `GapBoundU1 β hN2 δ₀`
  (`gapBoundU1_doeblin`) — the first landed gap bound at
  the seat whose `δ` is a formula in `(β, N)`.

## Fences — read before citing

**δ₀ DECAYS in `N`.** At every fixed `β ≠ 0`,
`δ₀ = exp (-192 * |β| * N ^ 4)` tends to `0` exponentially
in the four-volume as `N → ∞`; its infimum over `N` is
`0`. This brick **measures the enemy**: it replaces a
purely existential per-instance gap by an explicit but
volume-decaying lower bound. It proves **no (U-vol)
regime, no (U-traj) floor, and nothing at large `N`** —
the global action bound treats all `N ^ 4` plaquettes as
adversarial and erases the locality a genuine uniformity
modulus would need (scoping §3, Q2: L+ / research
program). Uniformity across `N` remains OPEN.

**NO CLAIM** — parts of any Clay statement closed by
this module: 0. Dials: 0/4.
-/

import ThetLogos.UniformityDensityBound
import ThetLogos.LatticeTransferCompact
import ThetLogos.LatticeUniformGap
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

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

/-! ## §0. The Doeblin modulus δ₀ and the constant check -/

/-- **The Doeblin modulus** `δ₀(β, N) = exp (-6 * actionBound β)`:
the explicit per-instance gap bound assembled in this brick.
In `(0, 1]` for every real `β` (the action bound is
nonnegative), equal to `1` at `β = 0`, and
`exp (-192 * β * N ^ 4)` at `β > 0` by
`actionBound_eq_volume`. It **decays in `N`** — see the
module header's fence. -/
noncomputable def doeblinDelta (β : ℝ) : ℝ :=
  Real.exp (-6 * actionBound (N := N) β)

/-- The action bound is nonnegative at every real `β`:
it is `|β|` times a cardinality count. -/
theorem actionBound_nonneg' (β : ℝ) :
    0 ≤ actionBound (N := N) β := by
  unfold actionBound
  positivity

/-- The volume form of the action bound:
`actionBound β = |β| * (32 * N ^ 4)`, since the torus
`Fin 4 → ZMod N` has `N ^ 4` points. This is the Lean
check of the scoping's constant: `6 * actionBound β =
192 * β * N ^ 4` at `β > 0`, so `δ₀ = exp (-192 β N⁴)`
there — the candidate constant is confirmed, not
superseded. -/
theorem actionBound_eq_volume (β : ℝ) :
    actionBound (N := N) β = |β| * (32 * (N : ℝ) ^ 4) := by
  have hcard : Fintype.card (Fin 4 → ZMod N) = N ^ 4 := by
    rw [Fintype.card_fun, ZMod.card N, Fintype.card_fin]
  unfold actionBound
  rw [hcard]
  push_cast
  ring

theorem doeblinDelta_pos (β : ℝ) : 0 < doeblinDelta (N := N) β :=
  Real.exp_pos _

theorem doeblinDelta_le_one (β : ℝ) :
    doeblinDelta (N := N) β ≤ 1 := by
  unfold doeblinDelta
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr
    (by have := actionBound_nonneg' (N := N) β; linarith)

/-! ## §1. Marginals of a product `withDensity` measure
(abstract measure theory) -/

section MarginalDensity

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  [IsProbabilityMeasure μ] {K : X × X → ℝ≥0∞}

/-- The first-factor marginal of a product `withDensity`
measure is the `withDensity` measure of the marginal
density: pushing `(μ.prod μ).withDensity K` forward along
`Prod.fst` integrates `K` over the second factor. -/
theorem withDensity_prod_map_fst (hK : Measurable K) :
    ((μ.prod μ).withDensity K).map Prod.fst
      = μ.withDensity (fun z => ∫⁻ z', K (z, z') ∂μ) := by
  have hKmarg : Measurable (fun z => ∫⁻ z', K (z, z') ∂μ) :=
    hK.lintegral_prod_right'
  ext s hs
  have hset : (Prod.fst : X × X → X) ⁻¹' s = s ×ˢ Set.univ := by
    ext ⟨z, z'⟩
    simp [Set.mem_prod]
  rw [Measure.map_apply measurable_fst hs,
    withDensity_apply K (measurable_fst hs),
    withDensity_apply (fun z => ∫⁻ z', K (z, z') ∂μ) hs, hset,
    ← lintegral_indicator (hs.prod MeasurableSet.univ) K,
    ← lintegral_indicator hs (fun z => ∫⁻ z', K (z, z') ∂μ),
    MeasureTheory.lintegral_prod _
      ((hK.indicator (hs.prod MeasurableSet.univ)).aemeasurable)]
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro z'
    exact Set.indicator_of_mem
      (Set.mem_prod.mpr ⟨hz, Set.mem_univ z'⟩) _
  · rw [Set.indicator_of_notMem hz]
    have hpt : ∀ z', (s ×ˢ Set.univ).indicator K (z, z') = 0 := by
      intro z'
      exact Set.indicator_of_notMem
        (fun h => hz (Set.mem_prod.mp h).1) _
    show (∫⁻ z', (s ×ˢ Set.univ).indicator K (z, z') ∂μ) = 0
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp

/-- The second-factor marginal of a product `withDensity`
measure: pushing forward along `Prod.snd` integrates `K`
over the first factor. Proved directly, with the
iteration order swapped by Tonelli. -/
theorem withDensity_prod_map_snd (hK : Measurable K) :
    ((μ.prod μ).withDensity K).map Prod.snd
      = μ.withDensity (fun z' => ∫⁻ z, K (z, z') ∂μ) := by
  have hKmarg : Measurable (fun z' => ∫⁻ z, K (z, z') ∂μ) :=
    hK.lintegral_prod_left'
  ext s hs
  have hset : (Prod.snd : X × X → X) ⁻¹' s = Set.univ ×ˢ s := by
    ext ⟨z, z'⟩
    simp [Set.mem_prod]
  have hAM : AEMeasurable
      ((Set.univ ×ˢ s).indicator K) (μ.prod μ) :=
    (hK.indicator (MeasurableSet.univ.prod hs)).aemeasurable
  have hAM2 : AEMeasurable
      (Function.uncurry fun z z' =>
        (Set.univ ×ˢ s).indicator K (z, z')) (μ.prod μ) :=
    (hK.indicator (MeasurableSet.univ.prod hs)).aemeasurable
  rw [Measure.map_apply measurable_snd hs,
    withDensity_apply K (measurable_snd hs),
    withDensity_apply (fun z' => ∫⁻ z, K (z, z') ∂μ) hs, hset,
    ← lintegral_indicator (MeasurableSet.univ.prod hs) K,
    ← lintegral_indicator hs (fun z' => ∫⁻ z, K (z, z') ∂μ),
    MeasureTheory.lintegral_prod _ hAM,
    MeasureTheory.lintegral_lintegral_swap hAM2]
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro z'
  by_cases hz : z' ∈ s
  · rw [Set.indicator_of_mem hz]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    exact Set.indicator_of_mem
      (Set.mem_prod.mpr ⟨Set.mem_univ z, hz⟩) _
  · rw [Set.indicator_of_notMem hz]
    have hpt : ∀ z, (Set.univ ×ˢ s).indicator K (z, z') = 0 := by
      intro z
      exact Set.indicator_of_notMem
        (fun h => hz (Set.mem_prod.mp h).2) _
    show (∫⁻ z, (Set.univ ×ˢ s).indicator K (z, z') ∂μ) = 0
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp

end MarginalDensity

/-! ## §2. The two-slice marginals, and the marginals of
`kReal` and of the residual kernel -/

section TwoSliceMarginals

/-- **The first marginal of `kReal` is `1`, a.e.** The
two-slice law has the slice measure as its first
marginal, and by Claim D it is the product of the slice
measures with density `ENNReal.ofReal ∘ kReal`; density
uniqueness for `withDensity` then forces the marginal
density of `kReal` to be `1` a.e. — `kReal` is a Markov
kernel density in its second argument. -/
theorem kReal_fst_marginal
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ∫ z', kReal μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β) = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  set μs := sliceMeasure (N := N) μG ρ β with hμs
  have hKmeas : Measurable
      (fun p => ENNReal.ofReal (kReal μG ρ hN2 β p)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_kReal μG ρ hρcont hN2 β)
  have hmarg : Measurable
      (fun z => ∫⁻ z', ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs) :=
    hKmeas.lintegral_prod_right'
  have hmeas_eq : μs.withDensity
        (fun z => ∫⁻ z', ENNReal.ofReal
          (kReal μG ρ hN2 β (z, z')) ∂μs)
      = μs.withDensity 1 := by
    rw [← withDensity_prod_map_fst μs hKmeas,
      ← twoSliceMeasure_eq_kernelDensity μG ρ hρcont hd hN2 β,
      twoSliceMeasure_map_fst μG ρ hN2 hρcont β, withDensity_one]
  have hae : (fun z => ∫⁻ z', ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs)
      =ᵐ[μs] (1 : (↥(sliceLinks (N := N)) → G) → ℝ≥0∞) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      hmarg measurable_one
    intro s hs hfin
    rw [← withDensity_apply
      (fun z => ∫⁻ z', ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs) hs,
      ← withDensity_apply
        (1 : (↥(sliceLinks (N := N)) → G) → ℝ≥0∞) hs, hmeas_eq]
  filter_upwards [hae] with z hz
  have hsec : AEStronglyMeasurable
      (fun z' => kReal μG ρ hN2 β (z, z'))
      (sliceMeasure (N := N) μG ρ β) :=
    ((measurable_kReal μG ρ hρcont hN2 β).comp
      measurable_prodMk_left).aestronglyMeasurable
  calc ∫ z', kReal μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
      = (∫⁻ z', ENNReal.ofReal (kReal μG ρ hN2 β (z, z'))
          ∂(sliceMeasure (N := N) μG ρ β)).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun z' =>
            kReal_nonneg μG ρ hρcont hd hN2 β (z, z')) hsec
    _ = (1 : ℝ≥0∞).toReal := by
        have h1 : (∫⁻ z', ENNReal.ofReal (kReal μG ρ hN2 β (z, z'))
            ∂(sliceMeasure (N := N) μG ρ β)) = 1 := hz
        rw [h1]
    _ = 1 := ENNReal.toReal_one

/-- **The second marginal of `kReal` is `1`, a.e.**:
`kReal` is a Markov kernel density in its first argument
too. Same proof through the second marginal of the
two-slice law (stationarity). -/
theorem kReal_snd_marginal
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    ∀ᵐ z' ∂(sliceMeasure (N := N) μG ρ β),
      ∫ z, kReal μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β) = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  set μs := sliceMeasure (N := N) μG ρ β with hμs
  have hKmeas : Measurable
      (fun p => ENNReal.ofReal (kReal μG ρ hN2 β p)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_kReal μG ρ hρcont hN2 β)
  have hmarg : Measurable
      (fun z' => ∫⁻ z, ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs) :=
    hKmeas.lintegral_prod_left'
  have hmeas_eq : μs.withDensity
        (fun z' => ∫⁻ z, ENNReal.ofReal
          (kReal μG ρ hN2 β (z, z')) ∂μs)
      = μs.withDensity 1 := by
    rw [← withDensity_prod_map_snd μs hKmeas,
      ← twoSliceMeasure_eq_kernelDensity μG ρ hρcont hd hN2 β,
      twoSliceMeasure_map_snd μG ρ hN2 hρcont β, withDensity_one]
  have hae : (fun z' => ∫⁻ z, ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs)
      =ᵐ[μs] (1 : (↥(sliceLinks (N := N)) → G) → ℝ≥0∞) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      hmarg measurable_one
    intro s hs hfin
    rw [← withDensity_apply
      (fun z' => ∫⁻ z, ENNReal.ofReal
        (kReal μG ρ hN2 β (z, z')) ∂μs) hs,
      ← withDensity_apply
        (1 : (↥(sliceLinks (N := N)) → G) → ℝ≥0∞) hs, hmeas_eq]
  filter_upwards [hae] with z' hz
  have hsec : AEStronglyMeasurable
      (fun z => kReal μG ρ hN2 β (z, z'))
      (sliceMeasure (N := N) μG ρ β) :=
    ((measurable_kReal μG ρ hρcont hN2 β).comp
      measurable_prodMk_right).aestronglyMeasurable
  calc ∫ z, kReal μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
      = (∫⁻ z, ENNReal.ofReal (kReal μG ρ hN2 β (z, z'))
          ∂(sliceMeasure (N := N) μG ρ β)).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun z =>
            kReal_nonneg μG ρ hρcont hd hN2 β (z, z')) hsec
    _ = (1 : ℝ≥0∞).toReal := by
        have h1 : (∫⁻ z, ENNReal.ofReal (kReal μG ρ hN2 β (z, z'))
            ∂(sliceMeasure (N := N) μG ρ β)) = 1 := hz
        rw [h1]
    _ = 1 := ENNReal.toReal_one

/-- The **residual kernel** `s = kReal - δ₀`: the
Doeblin remainder after the constant minorization piece
is split off. Nonnegative by the U-0 floor. -/
noncomputable def residualKernel (hN2 : 2 ≤ N) (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G))
      → ℝ :=
  fun p => kReal μG ρ hN2 β p - doeblinDelta (N := N) β

theorem residualKernel_nonneg
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    0 ≤ residualKernel μG ρ hN2 β p :=
  sub_nonneg.mpr (kReal_ge μG ρ hρcont hd hN2 β p)

theorem measurable_residualKernel
    (hρcont : Continuous fun g => repMatrix ρ g) (hN2 : 2 ≤ N)
    (β : ℝ) :
    Measurable (residualKernel μG ρ hN2 β) :=
  (measurable_kReal μG ρ hρcont hN2 β).sub_const _

/-- The first marginal of the residual kernel is
`1 - δ₀`, a.e.: the `kReal` marginal `1` minus the
constant piece's marginal `δ₀` (the slice measure is a
probability measure). -/
theorem residualKernel_fst_marginal
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ∫ z', residualKernel μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
        = 1 - doeblinDelta (N := N) β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  have hInt : ∀ z : ↥(sliceLinks (N := N)) → G,
      Integrable (fun z' => kReal μG ρ hN2 β (z, z'))
        (sliceMeasure (N := N) μG ρ β) := by
    intro z
    refine Integrable.of_bound
      ((measurable_kReal μG ρ hρcont hN2 β).comp
        measurable_prodMk_left).aestronglyMeasurable
      (Real.exp (6 * actionBound (N := N) β))
      (Filter.Eventually.of_forall fun z' => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (kReal_nonneg μG ρ hρcont hd hN2 β (z, z'))]
    exact kReal_le μG ρ hρcont hd hN2 β (z, z')
  filter_upwards [kReal_fst_marginal μG ρ hρcont hd hN2 β]
    with z hz
  calc ∫ z', residualKernel μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
      = ∫ z', (kReal μG ρ hN2 β (z, z')
          - doeblinDelta (N := N) β)
          ∂(sliceMeasure (N := N) μG ρ β) := rfl
    _ = (∫ z', kReal μG ρ hN2 β (z, z')
          ∂(sliceMeasure (N := N) μG ρ β))
        - ∫ z', doeblinDelta (N := N) β
          ∂(sliceMeasure (N := N) μG ρ β) :=
        integral_sub (hInt z) (integrable_const _)
    _ = 1 - doeblinDelta (N := N) β := by
        rw [hz]
        simp

/-- The second marginal of the residual kernel is
`1 - δ₀`, a.e. -/
theorem residualKernel_snd_marginal
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    ∀ᵐ z' ∂(sliceMeasure (N := N) μG ρ β),
      ∫ z, residualKernel μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
        = 1 - doeblinDelta (N := N) β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  have hInt : ∀ z' : ↥(sliceLinks (N := N)) → G,
      Integrable (fun z => kReal μG ρ hN2 β (z, z'))
        (sliceMeasure (N := N) μG ρ β) := by
    intro z'
    refine Integrable.of_bound
      ((measurable_kReal μG ρ hρcont hN2 β).comp
        measurable_prodMk_right).aestronglyMeasurable
      (Real.exp (6 * actionBound (N := N) β))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (kReal_nonneg μG ρ hρcont hd hN2 β (z, z'))]
    exact kReal_le μG ρ hρcont hd hN2 β (z, z')
  filter_upwards [kReal_snd_marginal μG ρ hρcont hd hN2 β]
    with z' hz
  calc ∫ z, residualKernel μG ρ hN2 β (z, z')
        ∂(sliceMeasure (N := N) μG ρ β)
      = ∫ z, (kReal μG ρ hN2 β (z, z')
          - doeblinDelta (N := N) β)
          ∂(sliceMeasure (N := N) μG ρ β) := rfl
    _ = (∫ z, kReal μG ρ hN2 β (z, z')
          ∂(sliceMeasure (N := N) μG ρ β))
        - ∫ z, doeblinDelta (N := N) β
          ∂(sliceMeasure (N := N) μG ρ β) :=
        integral_sub (hInt z') (integrable_const _)
    _ = 1 - doeblinDelta (N := N) β := by
        rw [hz]
        simp

end TwoSliceMarginals

/-! ## §3. The compression

The Doeblin split at the kernel level: `hdKernel = residualKernelC + δ₀`.
The constant piece pairs `f` against the vacuum direction twice and so
vanishes on `f ⊥ Ω`; the residual piece has both marginals `1 − δ₀`
a.e. (its kernel row/column masses), so Tonelli plus AM–GM bounds its
pairing by `(1 − δ₀)‖f‖²`. -/

section Compression

/-- The complex-valued residual kernel `kReal − δ₀`. -/
noncomputable def residualKernelC (hN2 : 2 ≤ N) (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G)
      × (↥(sliceLinks (N := N)) → G)) → ℂ :=
  fun p => (residualKernel μG ρ hN2 β p : ℂ)

/-- The kernel split: `hdKernel = residual + constant floor`, pointwise. -/
theorem hdKernel_eq_residual (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G)
      × (↥(sliceLinks (N := N)) → G)) :
    hdKernel μG ρ hN2 β p
      = residualKernelC μG ρ hN2 β p
        + (doeblinDelta (N := N) β : ℂ) := by
  show (kReal μG ρ hN2 β p : ℂ)
      = ((kReal μG ρ hN2 β p - doeblinDelta (N := N) β : ℝ) : ℂ)
        + (doeblinDelta (N := N) β : ℂ)
  push_cast
  ring

/-- The pointwise norm of the complex residual kernel is the real
residual kernel itself (it is nonnegative). -/
theorem residualKernelC_norm
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G)
      × (↥(sliceLinks (N := N)) → G)) :
    ‖residualKernelC μG ρ hN2 β p‖ = residualKernel μG ρ hN2 β p := by
  rw [show residualKernelC μG ρ hN2 β p
      = (residualKernel μG ρ hN2 β p : ℂ) from rfl]
  exact (RCLike.norm_ofReal _).trans
    (abs_of_nonneg (residualKernel_nonneg μG ρ hρcont hd hN2 β p))

/-- The residual kernel is `L²` on the product (bounded by `exp (6A)`). -/
theorem memLp_residualKernelC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    MemLp (residualKernelC μG ρ hN2 β) 2
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  refine MemLp.of_bound
    ((Complex.continuous_ofReal.measurable).comp
      (measurable_residualKernel μG ρ hρcont hN2 β)).aestronglyMeasurable
    (Real.exp (6 * actionBound (N := N) β))
    (Filter.Eventually.of_forall fun p => ?_)
  calc ‖residualKernelC μG ρ hN2 β p‖
      = residualKernel μG ρ hN2 β p :=
        residualKernelC_norm μG ρ hρcont hd hN2 β p
    _ ≤ kReal μG ρ hN2 β p := by
        show kReal μG ρ hN2 β p - doeblinDelta (N := N) β
            ≤ kReal μG ρ hN2 β p
        exact sub_le_self _ (doeblinDelta_pos β).le
    _ ≤ Real.exp (6 * actionBound (N := N) β) :=
        kReal_le μG ρ hρcont hd hN2 β p

/-- **The transfer form in kernel coordinates**: `⟪g, Tf⟫` against the
two-slice product measure with the HDen kernel `hdKernel`. Routed
through the corpus's two-slice form identity
(`transferOp_inner_twoSlice`) and the measure identity (Claim D)
rather than through the `HDen` existential, whose kernel is hidden. -/
theorem transferOp_inner_hdKernel
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (transferOp μG ρ hN2 hρcont β f)
      = ∫ p, star (⇑g p.1) * (hdKernel μG ρ hN2 β p * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) := by
  calc inner ℂ g (transferOp μG ρ hN2 hρcont β f)
      = ∫ p, (starRingEnd ℂ) (⇑g p.1) * ⇑f p.2
          ∂(twoSliceMeasure μG ρ hN2 hρcont β) :=
        transferOp_inner_twoSlice μG ρ hN2 hρcont β g f
    _ = ∫ p, (starRingEnd ℂ) (⇑g p.1) * ⇑f p.2
          ∂(((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)).withDensity
            fun p => ENNReal.ofReal (kReal μG ρ hN2 β p)) := by
        rw [twoSliceMeasure_eq_kernelDensity μG ρ hρcont hd hN2 β]
    _ = ∫ p, (ENNReal.ofReal (kReal μG ρ hN2 β p)).toReal
            • ((starRingEnd ℂ) (⇑g p.1) * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) :=
        integral_withDensity_eq_integral_toReal_smul
          (ENNReal.measurable_ofReal.comp
            (measurable_kReal μG ρ hρcont hN2 β))
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫ p, star (⇑g p.1) * (hdKernel μG ρ hN2 β p * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro p
        have e1 : hdKernel μG ρ hN2 β p = (kReal μG ρ hN2 β p : ℂ) := rfl
        have e2 : (starRingEnd ℂ) (⇑g p.1) = star (⇑g p.1) := rfl
        show (ENNReal.ofReal (kReal μG ρ hN2 β p)).toReal
            • ((starRingEnd ℂ) (⇑g p.1) * ⇑f p.2)
          = star (⇑g p.1) * (hdKernel μG ρ hN2 β p * ⇑f p.2)
        rw [e1, e2,
          ENNReal.toReal_ofReal (kReal_nonneg μG ρ hρcont hd hN2 β p),
          Complex.real_smul]
        ring

/-- **The Doeblin compression** (form level, general `(G, ρ)`, all real
`β`, `2 ≤ N`): on the vacuum-orthogonal complement, the transfer form
contracts by `1 − δ₀`. The constant piece of the kernel split pairs `f`
with the constant function, i.e. with the vacuum direction
(`⟪Ω, f⟫ = ∫ f`), and vanishes; the residual piece is bounded by its
two marginals, each `1 − δ₀` (Tonelli + AM–GM). -/
theorem transfer_form_compression
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (f : osSpace (N := N) μG ρ β)
    (hf : inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) f = 0) :
    ‖inner ℂ f (transferOp μG ρ hN2 hρcont β f)‖
      ≤ (1 - doeblinDelta (N := N) β) * ‖f‖ ^ 2 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hμs0 : sliceMeasure (N := N) μG ρ β ≠ 0 := by
    intro h0
    have h1 : sliceMeasure (N := N) μG ρ β Set.univ = 0 := by
      rw [h0]; simp
    rw [measure_univ] at h1
    exact one_ne_zero h1
  -- `∫ f = ⟪Ω, f⟫ = 0`.
  have hfint : ∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ β) = 0 := by
    have h := inner_osVacuum_left μG ρ hρcont hd β f
    rw [hf] at h
    exact h.symm
  -- Integrability of the pieces.
  have hIntS : Integrable
      (fun p => star (⇑f p.1)
        * (residualKernelC μG ρ hN2 β p * ⇑f p.2))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    integrable_kernel_pairing μG ρ β hρcont hd
      (residualKernelC μG ρ hN2 β)
      (memLp_residualKernelC μG ρ hρcont hd hN2 β) f f
  have hIntC : Integrable
      (fun p => star (⇑f p.1)
        * ((doeblinDelta (N := N) β : ℂ) * ⇑f p.2))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    integrable_kernel_pairing μG ρ β hρcont hd
      (fun _ => (doeblinDelta (N := N) β : ℂ)) (memLp_const _) f f
  have hIntT : Integrable
      (fun p => star (⇑f p.1) * ⇑f p.2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    memLp_one_iff_integrable.mp
      ((memLp_tensor μG ρ β hρcont hd f f).mono_exponent (by norm_num))
  -- Squared-norm integrability on one slice (corpus's own pattern).
  have hint2 : Integrable (fun z => ‖⇑f z‖ ^ 2)
      (sliceMeasure (N := N) μG ρ β) := by
    have h := (MeasureTheory.Lp.memLp f).integrable_norm_rpow
      (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
    rw [h2] at h
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using h
  -- The two marginal integrands, integrable by the `exp (6A)` dominator.
  have hnormF : ∀ (i : Fin 2),
      AEStronglyMeasurable
        (fun p : (↥(sliceLinks (N := N)) → G)
            × (↥(sliceLinks (N := N)) → G) =>
          ‖⇑f (if i = 0 then p.1 else p.2)‖ * ‖⇑f (if i = 0 then p.1 else p.2)‖)
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) := by
    intro i
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact (((MeasureTheory.Lp.aestronglyMeasurable f).comp_fst).norm).mul
        (((MeasureTheory.Lp.aestronglyMeasurable f).comp_fst).norm)
    · simp only [hi, if_false]
      exact (((MeasureTheory.Lp.aestronglyMeasurable f).comp_snd).norm).mul
        (((MeasureTheory.Lp.aestronglyMeasurable f).comp_snd).norm)
  have hIntF1 : Integrable
      (fun p => residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
    refine Integrable.mono'
      (g := fun p => Real.exp (6 * actionBound (N := N) β)
        * ‖⇑f p.1‖ ^ 2)
      ?_ ?_ ?_
    · exact (Integrable.comp_fst_iff hμs0).mpr (hint2.const_mul _)
    · refine ((measurable_residualKernel μG ρ hρcont hN2 β).aestronglyMeasurable).mul ?_
      exact ((hnormF 0).congr (Filter.Eventually.of_forall fun p => by
        simp [pow_two]))
    · refine Filter.Eventually.of_forall fun p => ?_
      have hs0 : 0 ≤ residualKernel μG ρ hN2 β p :=
        residualKernel_nonneg μG ρ hρcont hd hN2 β p
      have hsC : residualKernel μG ρ hN2 β p
          ≤ Real.exp (6 * actionBound (N := N) β) :=
        le_trans (by
          show kReal μG ρ hN2 β p - doeblinDelta (N := N) β
              ≤ kReal μG ρ hN2 β p
          exact sub_le_self _ (doeblinDelta_pos β).le)
          (kReal_le μG ρ hρcont hd hN2 β p)
      have hsq : 0 ≤ ‖⇑f p.1‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 hsq)]
      exact mul_le_mul_of_nonneg_right hsC hsq
  have hIntF2 : Integrable
      (fun p => residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
    refine Integrable.mono'
      (g := fun p => Real.exp (6 * actionBound (N := N) β)
        * ‖⇑f p.2‖ ^ 2)
      ?_ ?_ ?_
    · exact (Integrable.comp_snd_iff hμs0).mpr (hint2.const_mul _)
    · refine ((measurable_residualKernel μG ρ hρcont hN2 β).aestronglyMeasurable).mul ?_
      exact ((hnormF 1).congr (Filter.Eventually.of_forall fun p => by
        simp [pow_two]))
    · refine Filter.Eventually.of_forall fun p => ?_
      have hs0 : 0 ≤ residualKernel μG ρ hN2 β p :=
        residualKernel_nonneg μG ρ hρcont hd hN2 β p
      have hsC : residualKernel μG ρ hN2 β p
          ≤ Real.exp (6 * actionBound (N := N) β) :=
        le_trans (by
          show kReal μG ρ hN2 β p - doeblinDelta (N := N) β
              ≤ kReal μG ρ hN2 β p
          exact sub_le_self _ (doeblinDelta_pos β).le)
          (kReal_le μG ρ hρcont hd hN2 β p)
      have hsq : 0 ≤ ‖⇑f p.2‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 hsq)]
      exact mul_le_mul_of_nonneg_right hsC hsq
  -- The pointwise AM–GM step against the marginals.
  have hJ1 : (∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))
      = (1 - doeblinDelta (N := N) β) * ‖f‖ ^ 2 := by
    rw [MeasureTheory.integral_prod _ hIntF1]
    have hinner : ∀ z, (∫ z', residualKernel μG ρ hN2 β (z, z')
          * ‖⇑f z‖ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
        = ‖⇑f z‖ ^ 2 * (∫ z', residualKernel μG ρ hN2 β (z, z')
            ∂(sliceMeasure (N := N) μG ρ β)) := by
      intro z
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z' => mul_comm _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    have hcongr : (∫ z, ‖⇑f z‖ ^ 2
          * (∫ z', residualKernel μG ρ hN2 β (z, z')
              ∂(sliceMeasure (N := N) μG ρ β))
          ∂(sliceMeasure (N := N) μG ρ β))
        = ∫ z, ‖⇑f z‖ ^ 2 * (1 - doeblinDelta (N := N) β)
            ∂(sliceMeasure (N := N) μG ρ β) := by
      apply integral_congr_ae
      filter_upwards [residualKernel_fst_marginal μG ρ hρcont hd
        hN2 β] with z hz
      rw [hz]
    rw [hcongr, integral_mul_const,
      integral_norm_sq_lp (sliceMeasure (N := N) μG ρ β) f]
    exact mul_comm _ _
  have hJ2 : (∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))
      = (1 - doeblinDelta (N := N) β) * ‖f‖ ^ 2 := by
    have hIntF2' : Integrable
        (Function.uncurry fun z z' =>
          residualKernel μG ρ hN2 β (z, z') * ‖⇑f z'‖ ^ 2)
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) := hIntF2
    rw [MeasureTheory.integral_prod _ hIntF2,
      MeasureTheory.integral_integral_swap hIntF2']
    have hinner : ∀ z', (∫ z, residualKernel μG ρ hN2 β (z, z')
          * ‖⇑f z'‖ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
        = ‖⇑f z'‖ ^ 2 * (∫ z, residualKernel μG ρ hN2 β (z, z')
            ∂(sliceMeasure (N := N) μG ρ β)) := by
      intro z'
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_comm _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    have hcongr : (∫ z', ‖⇑f z'‖ ^ 2
          * (∫ z, residualKernel μG ρ hN2 β (z, z')
              ∂(sliceMeasure (N := N) μG ρ β))
          ∂(sliceMeasure (N := N) μG ρ β))
        = ∫ z', ‖⇑f z'‖ ^ 2 * (1 - doeblinDelta (N := N) β)
            ∂(sliceMeasure (N := N) μG ρ β) := by
      apply integral_congr_ae
      filter_upwards [residualKernel_snd_marginal μG ρ hρcont hd
        hN2 β] with z' hz
      rw [hz]
    rw [hcongr, integral_mul_const,
      integral_norm_sq_lp (sliceMeasure (N := N) μG ρ β) f]
    exact mul_comm _ _
  -- The split of the form integral; the constant piece vanishes.
  have hsplit : inner ℂ f (transferOp μG ρ hN2 hρcont β f)
      = ∫ p, star (⇑f p.1)
          * (residualKernelC μG ρ hN2 β p * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) := by
    have hform : inner ℂ f (transferOp μG ρ hN2 hρcont β f)
        = (∫ p, star (⇑f p.1)
            * (residualKernelC μG ρ hN2 β p * ⇑f p.2)
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          + ∫ p, star (⇑f p.1)
              * ((doeblinDelta (N := N) β : ℂ) * ⇑f p.2)
              ∂((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)) := by
      rw [transferOp_inner_hdKernel μG ρ hρcont hd hN2 β f f,
        ← integral_add hIntS hIntC]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      show star (⇑f p.1) * (hdKernel μG ρ hN2 β p * ⇑f p.2)
          = star (⇑f p.1) * (residualKernelC μG ρ hN2 β p * ⇑f p.2)
            + star (⇑f p.1)
              * ((doeblinDelta (N := N) β : ℂ) * ⇑f p.2)
      rw [hdKernel_eq_residual μG ρ hN2 β p]
      ring
    have hconst : ∫ p, star (⇑f p.1)
          * ((doeblinDelta (N := N) β : ℂ) * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) = 0 := by
      have e1 : (∫ p, star (⇑f p.1)
            * ((doeblinDelta (N := N) β : ℂ) * ⇑f p.2)
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          = (doeblinDelta (N := N) β : ℂ)
            * ∫ p, star (⇑f p.1) * ⇑f p.2
              ∂((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro p
        ring
      have e2 : (∫ p, star (⇑f p.1) * ⇑f p.2
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          = (∫ z, star (⇑f z) ∂(sliceMeasure (N := N) μG ρ β))
            * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ β)) := by
        rw [MeasureTheory.integral_prod _ hIntT,
          integral_congr_ae (Filter.Eventually.of_forall fun z =>
            integral_const_mul (star (⇑f z)) ⇑f)]
        exact integral_mul_const _ _
      rw [e1, e2, hfint, mul_zero, mul_zero]
    rw [hform, hconst, add_zero]
  -- The residual piece: norm, then Tonelli + AM–GM against marginals.
  have hnorm : ∀ p, ‖star (⇑f p.1)
        * (residualKernelC μG ρ hN2 β p * ⇑f p.2)‖
      = residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖) := by
    intro p
    rw [norm_mul, norm_mul, norm_star,
      residualKernelC_norm μG ρ hρcont hd hN2 β p]
    ring
  have hIntJ : Integrable
      (fun p => residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    hIntS.norm.congr (Filter.Eventually.of_forall hnorm)
  have hJle : (∫ p, residualKernel μG ρ hN2 β p
          * (‖⇑f p.1‖ * ‖⇑f p.2‖)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)))
      ≤ ((∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          + (∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2
              ∂((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)))) * (1 / 2) := by
    have hpt : ∀ p, residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖)
        ≤ (residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
            + residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2) * (1 / 2) := by
      intro p
      have hab : ‖⇑f p.1‖ * ‖⇑f p.2‖
          ≤ (‖⇑f p.1‖ ^ 2 + ‖⇑f p.2‖ ^ 2) * (1 / 2) := by
        have h := two_mul_le_add_sq ‖⇑f p.1‖ ‖⇑f p.2‖
        linarith
      calc residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖)
          ≤ residualKernel μG ρ hN2 β p
              * ((‖⇑f p.1‖ ^ 2 + ‖⇑f p.2‖ ^ 2) * (1 / 2)) :=
            mul_le_mul_of_nonneg_left hab
              (residualKernel_nonneg μG ρ hρcont hd hN2 β p)
        _ = (residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
              + residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2)
              * (1 / 2) := by ring
    calc (∫ p, residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)))
        ≤ ∫ p, (residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
              + residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2) * (1 / 2)
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)) :=
          integral_mono_ae hIntJ
            ((hIntF1.add hIntF2).mul_const (1 / 2))
            (Filter.Eventually.of_forall hpt)
      _ = ((∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
              ∂((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)))
            + (∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2
                ∂((sliceMeasure (N := N) μG ρ β).prod
                  (sliceMeasure (N := N) μG ρ β)))) * (1 / 2) := by
          rw [integral_mul_const, integral_add hIntF1 hIntF2]
  rw [hsplit]
  calc ‖∫ p, star (⇑f p.1)
        * (residualKernelC μG ρ hN2 β p * ⇑f p.2)
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))‖
      ≤ ∫ p, ‖star (⇑f p.1)
          * (residualKernelC μG ρ hN2 β p * ⇑f p.2)‖
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) :=
        norm_integral_le_integral_norm _
    _ = ∫ p, residualKernel μG ρ hN2 β p * (‖⇑f p.1‖ * ‖⇑f p.2‖)
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)) :=
        integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ ≤ ((∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.1‖ ^ 2
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          + (∫ p, residualKernel μG ρ hN2 β p * ‖⇑f p.2‖ ^ 2
              ∂((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)))) * (1 / 2) := hJle
    _ = (1 - doeblinDelta (N := N) β) * ‖f‖ ^ 2 := by
        rw [hJ1, hJ2]; ring

end Compression

/-! ## §4. The explicit spectral bound

An eigenvector with eigenvalue `≠ 1` is vacuum-orthogonal
(self-adjointness at `Even N` plus `T Ω = Ω`), so the compression
bounds its eigenvalue. Fredholm alternative for the compact transfer
operator turns the eigenvalue bound into a bound on the whole
spectrum — at **general** `(G, ρ)`, every real `β`, every even
`N ≥ 2`. The U(1) corollary then discharges the corpus's `GapBoundU1`
existence statements (`transfer_gap_of_formPos`,
`gapBoundU1_of_package`) with the explicit value `δ₀`. -/

section SpectrumBound

/-- Eigenvalue bound: any eigenvalue `lam ≠ 1` of the transfer
operator (at `Even N`, where it is self-adjoint) satisfies
`‖lam‖ ≤ 1 − δ₀`. -/
theorem transfer_eigenvalue_norm_le_doeblin
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (hN : Even N) (β : ℝ)
    {lam : ℂ} {v : osSpace (N := N) μG ρ β} (hv : v ≠ 0)
    (hev : transferOp μG ρ hN2 hρcont β v = lam • v) (hlam1 : lam ≠ 1) :
    ‖lam‖ ≤ 1 - doeblinDelta (N := N) β := by
  have horth : inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v = 0 := by
    have h1 : inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
        = lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v := by
      calc inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
          = inner ℂ (transferOp μG ρ hN2 hρcont β
              (osVacuum (N := N) μG ρ hρcont hd β)) v := by
            rw [transferOp_vacuum μG ρ hN2 hρcont hd β]
        _ = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β)
              (transferOp μG ρ hN2 hρcont β v) := by
            rw [← ContinuousLinearMap.adjoint_inner_left,
              transferOp_adjoint μG ρ hN2 hρcont hN β]
        _ = lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v := by
            rw [hev, inner_smul_right]
    have h2 : (1 - lam) * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
        = 0 := by
      have h3 : (1 - lam) * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
          = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
            - lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v := by
        rw [sub_mul, one_mul]
      rw [h3, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hlam1
    · exact h
  have hcomp := transfer_form_compression μG ρ hρcont hd hN2 β v horth
  have hform : inner ℂ v (transferOp μG ρ hN2 hρcont β v)
      = lam * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hev, inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hnormv : ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ = ‖v‖ ^ 2 :=
    (RCLike.norm_ofReal _).trans
      (abs_of_nonneg (pow_nonneg (norm_nonneg _) 2))
  rw [hform, norm_mul, hnormv] at hcomp
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  by_contra hcon
  push_neg at hcon
  have hlt := mul_lt_mul_of_pos_right hcon hv2
  linarith

/-- **HEADLINE — the Doeblin step, assembled.** At general `(G, ρ)`,
every real `β`, every even `N ≥ 2`: every spectral point of the
transfer operator other than the vacuum eigenvalue `1` has norm at
most `1 − δ₀`, where `δ₀ = exp (−6 · actionBound β)` — i.e.
`exp (−192 β N⁴)` for `β > 0`. The corpus's qualitative gap
(`transfer_gap_of_formPos`: some `δ > 0` exists) is hereby given the
explicit value `δ₀` at every seat where the corpus's spectral theory
runs. **Fence**: `δ₀` DECAYS in `N`; `inf` over `N` is `0`; this is a
per-`(β, N)` bound, NOT uniformity, and says nothing at large `N`. -/
theorem transfer_spectrum_le_doeblin
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (hN : Even N) (β : ℝ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    ∀ lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β),
      lam ≠ 1 → ‖lam‖ ≤ 1 - doeblinDelta (N := N) β := by
  intro lam hlam hlam1
  have hT : IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β) :=
    transferOp_compact_of_HDen μG ρ β hN2 hρcont hd
      (hden_all μG ρ hρcont hd hN2 β) b
  by_cases h0 : lam = 0
  · rw [h0, norm_zero]
    have hδ := doeblinDelta_le_one (N := N) β
    linarith
  · obtain ⟨v, hv, hvv⟩ := transfer_eigen_of_mem_spectrum μG ρ β hN2
      hρcont hT hlam h0
    exact transfer_eigenvalue_norm_le_doeblin μG ρ hρcont hd hN2 hN β
      hv hvv hlam1

/-- **The U(1) corollary in the corpus's own packaging**: `δ₀` is a
`GapBoundU1` gap bound — the explicit value for the existence
statements of `LatticeUniformGap`. -/
theorem gapBoundU1_doeblin (hN2 : 2 ≤ N) (hN : Even N) (β : ℝ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ
      (osSpace (N := N) (haarProb Circle) circleRep β)) :
    GapBoundU1 β hN2 (doeblinDelta (N := N) β) :=
  transfer_spectrum_le_doeblin (haarProb Circle) circleRep
    circleRep_continuous zero_lt_one hN2 hN β b

end SpectrumBound

end ThetLogos
