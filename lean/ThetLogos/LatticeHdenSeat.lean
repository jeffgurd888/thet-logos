/-
# ThetLogos.LatticeHdenSeat — HDen discharged, and the
per-instance gap at the U(1) seat made unconditional

Brick: the `HDen` discharge at the seat, the single named
hypothesis left after the D-1 weld
(`LatticeVacuumSimple.gapPackageU1_of_weld` /
`gapBoundU1_of_weld`, which consume `HDen` and a carried
Hilbert basis and nothing else).

## What is proved

* **`hden_all`** (§2): the density hypothesis `HDen` of
  Q12 (`LatticeTransferCompact`) holds at **every** real
  `β`, at general `(G, ρ)` — in particular at the U(1)
  seat. The two-slice Gibbs law has an explicit `L²`
  (indeed bounded) density kernel against the product of
  its marginals: the kernel is the ratio

    `K (z, z') = J̃ (z, z') / (M z * M z')`,

  where `M` is the slice marginal's density against the
  product Haar measure on the slice and `J̃` is the
  two-slice law's density against the product of the two
  product Haar measures. Both densities are *fiber
  integrals of the Gibbs density* over the complementary
  coordinates, transported along the corpus's splitting
  equivs (`splitEquiv`); the Gibbs density is two-sided
  bounded by exponentials of the bounded Wilson action
  (the weld's `gibbsDensity_le/ge`), and fiber integration
  over probability measures preserves the two-sided
  bounds, so `M` is bounded above and bounded away from
  `0`, `J̃` is bounded above, and `K` is bounded. The
  form identity is then the two landed form identities
  (`transferOp_inner_twoSlice`, `kernelLinMap_inner`)
  joined by the density.
* **`gapBoundU1_unconditional`** (§3): Q12's per-instance
  gap at the U(1) seat, `β > 0`, even `N ≥ 2`, holds
  **unconditionally** — modulo only the carried Hilbert
  basis (separability carried as data, FG-1's
  convention). Per-instance only: no uniformity in `N`
  or along trajectories is asserted or implied.

**NO CLAIM** — parts of any Clay statement closed by
this module: 0. Dials: 0/4. Stage 1b-B at general
`(G, ρ)` remains OPEN and untouched.
-/

import ThetLogos.LatticeVacuumSimple

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

/-! ## §1. General measure-theory helpers -/

section Helpers

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ]

/-- A density transported along a measurable equivalence:
pushing a `withDensity` measure along `e` composes the
density with `e.symm`. -/
theorem withDensity_map_equiv {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (e : α ≃ᵐ β) :
    (μ.withDensity f).map e
      = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    ← lintegral_indicator (e.measurable hs) f,
    ← lintegral_indicator hs (f ∘ e.symm)]
  have h1 : ∀ a : α, s.indicator (f ∘ ⇑e.symm) (e a)
      = (⇑e ⁻¹' s).indicator f a := by
    intro a
    by_cases ha : e a ∈ s
    · rw [Set.indicator_of_mem ha,
        Set.indicator_of_mem (Set.mem_preimage.mpr ha)]
      simp [Function.comp_apply]
    · rw [Set.indicator_of_notMem ha,
        Set.indicator_of_notMem (fun h => ha (Set.mem_preimage.mp h))]
  rw [lintegral_map
    ((hf.comp e.symm.measurable).indicator hs) e.measurable]
  exact lintegral_congr_ae
    (Filter.Eventually.of_forall (fun a => (h1 a).symm))

/-- The first-factor marginal of a density on a product:
marginalizing a `withDensity` measure along `Prod.fst`
integrates the density over the second factor. -/
theorem withDensity_map_fst {μ : Measure α} {ν : Measure β}
    [SFinite ν] {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ((μ.prod ν).withDensity F).map Prod.fst
      = μ.withDensity (fun x => ∫⁻ y, F (x, y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs,
    ← lintegral_indicator (measurable_fst hs) F,
    ← lintegral_indicator hs
      (fun x => ∫⁻ y, F (x, y) ∂ν)]
  rw [lintegral_prod _ (hF.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    apply lintegral_congr_ae
    filter_upwards with y
    exact Set.indicator_of_mem (show (x, y) ∈ Prod.fst ⁻¹' s from hx) _
  · rw [Set.indicator_of_notMem hx]
    have h0 : ∀ y : β, (Prod.fst ⁻¹' s).indicator F (x, y) = 0 :=
      fun y => Set.indicator_of_notMem (a := (x, y))
        (s := Prod.fst ⁻¹' s) (fun hy => hx hy) F
    rw [lintegral_congr_ae (Filter.Eventually.of_forall h0)]
    simp

/-- The scalar in the Gibbs measure folds into the
density. -/
theorem smul_withDensity' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (c : ℝ≥0∞) :
    c • μ.withDensity f = μ.withDensity (fun a => c * f a) := by
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs,
    withDensity_apply _ hs, lintegral_const_mul _ hf]

end Helpers

/-! ## §2. The density kernel at general `(G, ρ)` -/

section HDenDischarge

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The combined splitting equivalence: a configuration is
its time-`0` slice reading, its slice-`1` reading inside
the complement, and the remaining coordinates. -/
noncomputable def splitE :
    Config (Fin 4 → ZMod N) G ≃ᵐ
      ((↥(sliceLinks (N := N)) → G) ×
        ((↥(slice1InCompl (N := N)) → G) ×
          (↥(slice1InCompl (N := N))ᶜ → G))) :=
  (splitEquiv (sliceLinks (N := N))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (splitEquiv (slice1InCompl (N := N))))

/-- The combined split preserves the configuration
measure. -/
theorem measurePreserving_splitE :
    MeasurePreserving ⇑(splitE (G := G) (N := N))
      (configMeasure μG)
      ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))) := by
  have h1 := measurePreserving_splitEquiv μG (sliceLinks (N := N))
  have h2 := measurePreserving_splitEquiv μG (slice1InCompl (N := N))
  have h3 : MeasurePreserving
      (Prod.map id ⇑(splitEquiv (slice1InCompl (N := N))))
      ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(sliceLinks (N := N))ᶜ => μG))
      ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))) :=
    (MeasurePreserving.id _).prod h2
  have h4 := h3.comp h1
  exact h4

/-- The Gibbs scalar `Z⁻¹` as an `ℝ≥0∞` constant. -/
noncomputable def gibbsScalar (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹

/-- The lower density bound `exp (−2·actionBound (N := N) β)`. -/
noncomputable def densityLo (β : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-2 * actionBound (N := N) β))

/-- The upper density bound `exp (2·actionBound (N := N) β)`. -/
noncomputable def densityHi (β : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (2 * actionBound (N := N) β))

theorem densityLo_ne_zero (β : ℝ) : densityLo (N := N) β ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem densityHi_ne_top (β : ℝ) : densityHi (N := N) β ≠ ∞ :=
  ENNReal.ofReal_lt_top.ne

theorem densityLo_ne_top (β : ℝ) : densityLo (N := N) β ≠ ∞ :=
  ENNReal.ofReal_lt_top.ne

theorem densityHi_pos (β : ℝ) : 0 < densityHi (N := N) β :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- The Gibbs scalar is bounded above by `exp (actionBound
β)`: from the weld's lower set-bound at the universe. -/
theorem gibbsScalar_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    gibbsScalar (N := N) μG ρ β
      ≤ ENNReal.ofReal (Real.exp (actionBound (N := N) β)) := by
  have hge := gibbsMeasure_ge (N := N) μG ρ hd hρcont β
    (E := Set.univ) MeasurableSet.univ
  haveI := isProbabilityMeasure_gibbsMeasure (torusShift N) μG ρ
    hρcont hd β
  simp only [measure_univ, mul_one] at hge
  -- hge : gibbsScalar * ofReal (exp (-B)) ≤ 1
  have h1 : gibbsScalar (N := N) μG ρ β
      = gibbsScalar (N := N) μG ρ β
        * ENNReal.ofReal (Real.exp (-actionBound (N := N) β))
        * (ENNReal.ofReal (Real.exp (-actionBound (N := N) β)))⁻¹ := by
    rw [mul_assoc, ENNReal.mul_inv_cancel
      (by simp [ENNReal.ofReal_eq_zero, Real.exp_pos])
      ENNReal.ofReal_lt_top.ne, mul_one]
  calc gibbsScalar (N := N) μG ρ β
      = gibbsScalar (N := N) μG ρ β
          * ENNReal.ofReal (Real.exp (-actionBound (N := N) β))
          * (ENNReal.ofReal (Real.exp (-actionBound (N := N) β)))⁻¹ := h1
    _ ≤ 1 * (ENNReal.ofReal (Real.exp (-actionBound (N := N) β)))⁻¹ :=
        mul_le_mul hge le_rfl zero_le zero_le
    _ = ENNReal.ofReal (Real.exp (actionBound (N := N) β)) := by
        rw [one_mul, ← ENNReal.ofReal_inv_of_pos
          (Real.exp_pos _), Real.exp_neg, inv_inv]

/-- The Gibbs scalar is bounded below by
`exp (−actionBound (N := N) β)`: from the weld's upper set-bound at
the universe. -/
theorem gibbsScalar_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) :
    ENNReal.ofReal (Real.exp (-actionBound (N := N) β))
      ≤ gibbsScalar (N := N) μG ρ β := by
  have hle := gibbsMeasure_le (N := N) μG ρ hd hρcont β
    (E := Set.univ) MeasurableSet.univ
  haveI := isProbabilityMeasure_gibbsMeasure (torusShift N) μG ρ
    hρcont hd β
  simp only [measure_univ, mul_one] at hle
  -- hle : 1 ≤ gibbsScalar * ofReal (exp B)
  calc ENNReal.ofReal (Real.exp (-actionBound (N := N) β))
      = (ENNReal.ofReal (Real.exp (actionBound (N := N) β)))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos
          (Real.exp_pos _), Real.exp_neg]
    _ = (ENNReal.ofReal (Real.exp (actionBound (N := N) β)))⁻¹ * 1 :=
        (mul_one _).symm
    _ ≤ (ENNReal.ofReal (Real.exp (actionBound (N := N) β)))⁻¹
          * (gibbsScalar (N := N) μG ρ β
            * ENNReal.ofReal (Real.exp (actionBound (N := N) β))) :=
        mul_le_mul le_rfl hle zero_le zero_le
    _ = gibbsScalar (N := N) μG ρ β := by
        rw [mul_comm (gibbsScalar (N := N) μG ρ β) _, ← mul_assoc,
          ENNReal.inv_mul_cancel
          (by simp [ENNReal.ofReal_eq_zero, Real.exp_pos])
          ENNReal.ofReal_lt_top.ne, one_mul]

/-- The folded Gibbs density `Z⁻¹ • exp (−S_β)` is bounded
above by `densityHi`, pointwise. -/
theorem gibbsDensity'_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    gibbsScalar (N := N) μG ρ β
        * (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
      ≤ densityHi (N := N) β := by
  have hexp : Real.exp (actionBound (N := N) β)
        * Real.exp (actionBound (N := N) β)
      = Real.exp (2 * actionBound (N := N) β) := by
    rw [← Real.exp_add]; congr 1; ring
  calc gibbsScalar (N := N) μG ρ β
          * (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
      ≤ ENNReal.ofReal (Real.exp (actionBound (N := N) β))
          * ENNReal.ofReal (Real.exp (actionBound (N := N) β)) :=
        mul_le_mul (gibbsScalar_le μG ρ hρcont hd β)
          (gibbsDensity_le ρ hd β U) zero_le zero_le
    _ = densityHi (N := N) β := by
        rw [densityHi, ← ENNReal.ofReal_mul
          (Real.exp_nonneg _), hexp]

/-- The folded Gibbs density is bounded below by
`densityLo`, pointwise. -/
theorem gibbsDensity'_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    densityLo (N := N) β
      ≤ gibbsScalar (N := N) μG ρ β
        * (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞) := by
  have hexp : Real.exp (-actionBound (N := N) β)
        * Real.exp (-actionBound (N := N) β)
      = Real.exp (-2 * actionBound (N := N) β) := by
    rw [← Real.exp_add]; congr 1; ring
  calc densityLo (N := N) β
      = ENNReal.ofReal (Real.exp (-actionBound (N := N) β))
          * ENNReal.ofReal (Real.exp (-actionBound (N := N) β)) := by
        rw [densityLo, ← ENNReal.ofReal_mul
          (Real.exp_nonneg _), hexp]
    _ ≤ gibbsScalar (N := N) μG ρ β
          * (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞) :=
        mul_le_mul (gibbsScalar_ge μG ρ hρcont hd β)
          (gibbsDensity_ge ρ hd β U) zero_le zero_le

/-- The joint density of the Gibbs law in split
coordinates: the folded Gibbs density read through the
combined split. -/
noncomputable def jointDensity (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G) ×
      ((↥(slice1InCompl (N := N)) → G) ×
        (↥(slice1InCompl (N := N))ᶜ → G))) → ℝ≥0∞ :=
  fun p => gibbsScalar (N := N) μG ρ β
    * (gibbsDensity (torusShift N) ρ β
        ((splitE (G := G) (N := N)).symm p) : ℝ≥0∞)

theorem measurable_jointDensity
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measurable (jointDensity (N := N) μG ρ β) :=
  Measurable.const_mul
    (measurable_coe_nnreal_ennreal.comp
      ((measurable_gibbsDensity (torusShift N) ρ hρcont β).comp
        (splitE (G := G) (N := N)).symm.measurable)) _

theorem jointDensity_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      ((↥(slice1InCompl (N := N)) → G) ×
        (↥(slice1InCompl (N := N))ᶜ → G))) :
    jointDensity (N := N) μG ρ β p ≤ densityHi (N := N) β :=
  gibbsDensity'_le μG ρ hρcont hd β _

theorem jointDensity_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      ((↥(slice1InCompl (N := N)) → G) ×
        (↥(slice1InCompl (N := N))ᶜ → G))) :
    densityLo (N := N) β ≤ jointDensity (N := N) μG ρ β p :=
  gibbsDensity'_ge μG ρ hρcont hd β _

/-- **Claim A.** The Gibbs measure, read in split
coordinates, is the product Haar measure with density
`jointDensity`. -/
theorem gibbsMeasure_map_splitE
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    (gibbsMeasure (torusShift N) μG ρ β).map
        ⇑(splitE (G := G) (N := N))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
            (Measure.pi
              fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).withDensity
          (jointDensity (N := N) μG ρ β) := by
  have hDf : Measurable (fun U : Config (Fin 4 → ZMod N) G =>
        (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp
      (measurable_gibbsDensity (torusShift N) ρ hρcont β)
  unfold gibbsMeasure
  calc ((ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
          ((configMeasure μG).withDensity
            fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞))).map
        ⇑(splitE (G := G) (N := N))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
          (((configMeasure μG).map ⇑(splitE (G := G) (N := N))).withDensity
            ((fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)) ∘
              ⇑(splitE (G := G) (N := N)).symm)) := by
        rw [Measure.map_smul _
          (splitE (G := G) (N := N)).measurable.aemeasurable,
          withDensity_map_equiv hDf (splitE (G := G) (N := N))]
    _ = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
          (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
            ((Measure.pi
                fun _ : ↥(slice1InCompl (N := N)) => μG).prod
              (Measure.pi
                fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).withDensity
            ((fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)) ∘
              ⇑(splitE (G := G) (N := N)).symm)) := by
        have hmp : (configMeasure μG).map
              ⇑(splitE (G := G) (N := N))
            = (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
                ((Measure.pi
                    fun _ : ↥(slice1InCompl (N := N)) => μG).prod
                  (Measure.pi
                    fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)) :=
          (measurePreserving_splitE μG).map_eq
        rw [hmp]
    _ = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
            (Measure.pi
              fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).withDensity
          (jointDensity (N := N) μG ρ β) :=
        smul_withDensity' (hDf.comp
          (splitE (G := G) (N := N)).symm.measurable) _

/-- The slice marginal's density against the product Haar
measure on the slice: the fiber integral of the joint
density over the complementary coordinates. -/
noncomputable def sliceDensity (β : ℝ) :
    (↥(sliceLinks (N := N)) → G) → ℝ≥0∞ :=
  fun z => ∫⁻ q, jointDensity (N := N) μG ρ β (z, q)
    ∂((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))

theorem measurable_sliceDensity
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measurable (sliceDensity (N := N) μG ρ β) :=
  (measurable_jointDensity (N := N) μG ρ hρcont β).lintegral_prod_right'

theorem sliceDensity_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (z : ↥(sliceLinks (N := N)) → G) :
    sliceDensity (N := N) μG ρ β z ≤ densityHi (N := N) β := by
  calc sliceDensity (N := N) μG ρ β z
      ≤ ∫⁻ _q, densityHi (N := N) β
          ∂((Measure.pi
              fun _ : ↥(slice1InCompl (N := N)) => μG).prod
            (Measure.pi
              fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)) :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun q => jointDensity_le (N := N) μG ρ hρcont hd β (z, q))
    _ = densityHi (N := N) β := by
        rw [lintegral_const, measure_univ, mul_one]

theorem sliceDensity_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (z : ↥(sliceLinks (N := N)) → G) :
    densityLo (N := N) β ≤ sliceDensity (N := N) μG ρ β z := by
  calc densityLo (N := N) β
      = ∫⁻ _q, densityLo (N := N) β
          ∂((Measure.pi
              fun _ : ↥(slice1InCompl (N := N)) => μG).prod
            (Measure.pi
              fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ sliceDensity (N := N) μG ρ β z :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun q => jointDensity_ge (N := N) μG ρ hρcont hd β (z, q))

/-- **Claim B.** The slice measure is the product Haar
measure on the slice with density `sliceDensity`. -/
theorem sliceMeasure_eq
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    sliceMeasure μG ρ β
      = (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).withDensity
          (sliceDensity (N := N) μG ρ β) := by
  have hfst : ∀ U : Config (Fin 4 → ZMod N) G,
      (splitE (G := G) (N := N) U).1
        = restrictConfig (sliceLinks (N := N)) U :=
    fun U => splitEquiv_fst _ U
  have hfun : restrictConfig (sliceLinks (N := N))
      = Prod.fst ∘ ⇑(splitE (G := G) (N := N)) := by
    funext U
    exact (hfst U).symm
  have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (restrictConfig (sliceLinks (N := N)))
      = ((gibbsMeasure (torusShift N) μG ρ β).map
          ⇑(splitE (G := G) (N := N))).map Prod.fst := by
    rw [hfun, Measure.map_map measurable_fst
      (splitE (G := G) (N := N)).measurable]
  unfold sliceMeasure marginalMeasure
  rw [hmap, gibbsMeasure_map_splitE (N := N) μG ρ hρcont β]
  exact withDensity_map_fst
    (measurable_jointDensity (N := N) μG ρ hρcont β)

/-- The coordinate identification between the second
slice's coordinates and the first complement's: the landed
`sliceToCompl`, read as a pi-congruence (its underlying
function is precomposition by `sliceToCompl`). -/
noncomputable def sliceCoordEquiv (hN2 : 2 ≤ N) :
    (↥(slice1InCompl (N := N)) → G) ≃ᵐ
      (↥(sliceLinks (N := N)) → G) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : ↥(slice1InCompl (N := N)) => G)
    (sliceToCompl (N := N) hN2)).symm

theorem sliceCoordEquiv_apply (hN2 : 2 ≤ N)
    (w : ↥(slice1InCompl (N := N)) → G)
    (ℓ : ↥(sliceLinks (N := N))) :
    sliceCoordEquiv (N := N) hN2 w ℓ
      = w (sliceToCompl (N := N) hN2 ℓ) :=
  Equiv.piCongrLeft_symm_apply
    (fun _ : ↥(slice1InCompl (N := N)) => G)
    (sliceToCompl (N := N) hN2) w ℓ

/-- The two-slice readout map in split coordinates: keep
the slice coordinates, read the second slice off the first
complement through `sliceToCompl`, discard the rest. -/
noncomputable def twoSliceSplitMap (hN2 : 2 ≤ N) :
    ((↥(sliceLinks (N := N)) → G) ×
      ((↥(slice1InCompl (N := N)) → G) ×
        (↥(slice1InCompl (N := N))ᶜ → G)))
      → (↥(sliceLinks (N := N)) → G) ×
        (↥(sliceLinks (N := N)) → G) :=
  fun p => (p.1, sliceCoordEquiv (N := N) hN2 p.2.1)

/-- The readout map factors as reassociation, first
projection, and a product map. -/
theorem twoSliceSplitMap_factor (hN2 : 2 ≤ N) :
    twoSliceSplitMap (N := N) hN2
      = (Prod.map id ⇑(sliceCoordEquiv (N := N) hN2))
          ∘ Prod.fst
          ∘ ⇑(MeasurableEquiv.prodAssoc
              (α := (↥(sliceLinks (N := N)) → G))
              (β := (↥(slice1InCompl (N := N)) → G))
              (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm :=
  funext fun p => rfl

theorem measurable_twoSliceSplitMap (hN2 : 2 ≤ N) :
    Measurable (twoSliceSplitMap (N := N) hN2 :
      ((↥(sliceLinks (N := N)) → G) ×
        ((↥(slice1InCompl (N := N)) → G) ×
          (↥(slice1InCompl (N := N))ᶜ → G)))
        → (↥(sliceLinks (N := N)) → G) ×
          (↥(sliceLinks (N := N)) → G)) := by
  have h1 : Measurable (Prod.fst :
      ((↥(sliceLinks (N := N)) → G) ×
        ((↥(slice1InCompl (N := N)) → G) ×
          (↥(slice1InCompl (N := N))ᶜ → G)))
        → (↥(sliceLinks (N := N)) → G)) := measurable_fst
  have h2 : Measurable (fun p :
      ((↥(sliceLinks (N := N)) → G) ×
        ((↥(slice1InCompl (N := N)) → G) ×
          (↥(slice1InCompl (N := N))ᶜ → G))) => p.2.1) :=
    measurable_snd.fst
  exact h1.prodMk
    ((sliceCoordEquiv (N := N) hN2).measurable.comp h2)

/-- The first component of the combined split is the
slice restriction. -/
theorem splitE_fst (U : Config (Fin 4 → ZMod N) G) :
    (splitE (G := G) (N := N) U).1
      = restrictConfig (sliceLinks (N := N)) U :=
  splitEquiv_fst _ U

/-- The readout of the split of a configuration is the
corpus's two-slice readout of that configuration. -/
theorem twoSliceSplitMap_splitE (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    twoSliceSplitMap (N := N) hN2 (splitE (G := G) (N := N) U)
      = (restrictConfig (sliceLinks (N := N)) U,
          nextConfig (N := N) hN2 U) := by
  have h2 : (splitE (G := G) (N := N) U).2.1
      = restrictConfig (slice1InCompl (N := N))
          (restrictConfig (sliceLinks (N := N))ᶜ U) :=
    splitEquiv_fst _ _
  have hkey : ∀ ℓ : ↥(sliceLinks (N := N)),
      sliceCoordEquiv (N := N) hN2
          (splitE (G := G) (N := N) U).2.1 ℓ
        = nextConfig (N := N) hN2 U ℓ := by
    intro ℓ
    rw [sliceCoordEquiv_apply, h2, nextConfig_eq_nextOfRest,
      nextOfRest_eq]
  exact Prod.ext (splitE_fst U) (funext hkey)

/-- The two-slice density against the product of the
marginal base measures: the fiber integral of the joint
density over the discarded coordinates, with the second
slice read back through the coordinate identification. -/
noncomputable def jDensity (hN2 : 2 ≤ N) (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) → ℝ≥0∞ :=
  fun p => ∫⁻ u : ↥(slice1InCompl (N := N))ᶜ → G,
    jointDensity (N := N) μG ρ β
      (p.1, (sliceCoordEquiv (N := N) hN2).symm p.2, u)
    ∂(Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)

theorem measurable_jDensity
    (hρcont : Continuous fun g => repMatrix ρ g) (hN2 : 2 ≤ N)
    (β : ℝ) :
    Measurable (jDensity μG ρ hN2 β) := by
  have hmap : Measurable (fun pu :
      (((↥(sliceLinks (N := N)) → G) ×
          (↥(sliceLinks (N := N)) → G)) ×
        (↥(slice1InCompl (N := N))ᶜ → G)) =>
      (pu.1.1, ((sliceCoordEquiv (N := N) hN2).symm pu.1.2,
        pu.2))) :=
    (measurable_fst.fst).prodMk
      (((sliceCoordEquiv (N := N) hN2).symm.measurable.comp
        measurable_fst.snd).prodMk measurable_snd)
  exact ((measurable_jointDensity (N := N) μG ρ hρcont β).comp
    hmap).lintegral_prod_right'

theorem jDensity_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    jDensity μG ρ hN2 β p ≤ densityHi (N := N) β := by
  calc jDensity μG ρ hN2 β p
      ≤ ∫⁻ _u : ↥(slice1InCompl (N := N))ᶜ → G,
          densityHi (N := N) β
          ∂(Measure.pi
            fun _ : ↥(slice1InCompl (N := N))ᶜ => μG) :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun u => jointDensity_le (N := N) μG ρ hρcont hd β _)
    _ = densityHi (N := N) β := by
        rw [lintegral_const, measure_univ, mul_one]

theorem jDensity_ge
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    densityLo (N := N) β ≤ jDensity μG ρ hN2 β p := by
  calc densityLo (N := N) β
      = ∫⁻ _u : ↥(slice1InCompl (N := N))ᶜ → G,
          densityLo (N := N) β
          ∂(Measure.pi
            fun _ : ↥(slice1InCompl (N := N))ᶜ => μG) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ jDensity μG ρ hN2 β p :=
        lintegral_mono_ae (Filter.Eventually.of_forall
          fun u => jointDensity_ge (N := N) μG ρ hρcont hd β _)

/-- The readout map factors as reassociation, first
projection, and a product of measurable equivalences. -/
theorem twoSliceSplitMap_factor' (hN2 : 2 ≤ N) :
    twoSliceSplitMap (N := N) hN2
      = ⇑(MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl (↥(sliceLinks (N := N)) → G))
            (sliceCoordEquiv (N := N) hN2))
          ∘ Prod.fst
          ∘ ⇑(MeasurableEquiv.prodAssoc
              (α := (↥(sliceLinks (N := N)) → G))
              (β := (↥(slice1InCompl (N := N)) → G))
              (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm :=
  funext fun p => rfl

/-- The coordinate identification is measure-preserving
between the product Haar measures: the corpus's
precomposition fact, transported along the pointwise
law. -/
theorem measurePreserving_sliceCoordEquiv (hN2 : 2 ≤ N) :
    MeasurePreserving ⇑(sliceCoordEquiv (N := N) hN2)
      (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)
      (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG) := by
  have hfun : ⇑(sliceCoordEquiv (N := N) hN2)
      = fun w : ↥(slice1InCompl (N := N)) → G =>
        fun ℓ => w (sliceToCompl (N := N) hN2 ℓ) :=
    funext fun w => funext fun ℓ =>
      sliceCoordEquiv_apply (N := N) hN2 w ℓ
  rw [hfun]
  exact measurePreserving_sliceToCompl_precomp μG hN2

/-- **Claim C, step 1.** Reassociation of the joint
law. -/
theorem withDensity_jointDensity_map_prodAssoc_symm
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
      ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
        (Measure.pi
          fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).withDensity
      (jointDensity (N := N) μG ρ β)).map
        ⇑(MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm
      = (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)).prod
        (Measure.pi
          fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)).withDensity
          (jointDensity (N := N) μG ρ β ∘
            ⇑(MeasurableEquiv.prodAssoc
              (α := (↥(sliceLinks (N := N)) → G))
              (β := (↥(slice1InCompl (N := N)) → G))
              (γ := (↥(slice1InCompl (N := N))ᶜ → G)))) := by
  have hmp : ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        ((Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG).prod
          (Measure.pi
            fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).map
        ⇑(MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)).prod
        (Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG) :=
    ((measurePreserving_prodAssoc
      (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)
      (Measure.pi fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)).symm
        (MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G)))).map_eq
  refine (withDensity_map_equiv
    (measurable_jointDensity (N := N) μG ρ hρcont β)
    (MeasurableEquiv.prodAssoc
      (α := (↥(sliceLinks (N := N)) → G))
      (β := (↥(slice1InCompl (N := N)) → G))
      (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm).trans ?_
  rw [hmp, MeasurableEquiv.symm_symm]

/-- **Claim C, step 2.** Discarding the last coordinate
of the joint law produces the fiber density over the
discarded coordinates. -/
theorem withDensity_jointDensity_map_fst
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    ((((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)).prod
      (Measure.pi
        fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)).withDensity
      (jointDensity (N := N) μG ρ β ∘
        ⇑(MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G))))).map Prod.fst
      = (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG))).withDensity
          (fun q => ∫⁻ u : ↥(slice1InCompl (N := N))ᶜ → G,
            (jointDensity (N := N) μG ρ β ∘
              ⇑(MeasurableEquiv.prodAssoc
                (α := (↥(sliceLinks (N := N)) → G))
                (β := (↥(slice1InCompl (N := N)) → G))
                (γ := (↥(slice1InCompl (N := N))ᶜ → G)))) (q, u)
            ∂(Measure.pi
              fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)) :=
  withDensity_map_fst
    ((measurable_jointDensity (N := N) μG ρ hρcont β).comp
      (MeasurableEquiv.prodAssoc
        (α := (↥(sliceLinks (N := N)) → G))
        (β := (↥(slice1InCompl (N := N)) → G))
        (γ := (↥(slice1InCompl (N := N))ᶜ → G))).measurable)

/-- **Claim C, step 3.** Reindexing the second slice by
the coordinate identification produces `jDensity`. -/
theorem withDensity_fiber_map_prodCongr
    (hρcont : Continuous fun g => repMatrix ρ g) (hN2 : 2 ≤ N)
    (β : ℝ) :
    ((((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG))).withDensity
      (fun q => ∫⁻ u : ↥(slice1InCompl (N := N))ᶜ → G,
        (jointDensity (N := N) μG ρ β ∘
          ⇑(MeasurableEquiv.prodAssoc
            (α := (↥(sliceLinks (N := N)) → G))
            (β := (↥(slice1InCompl (N := N)) → G))
            (γ := (↥(slice1InCompl (N := N))ᶜ → G)))) (q, u)
        ∂(Measure.pi
          fun _ : ↥(slice1InCompl (N := N))ᶜ => μG))).map
      ⇑(MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (↥(sliceLinks (N := N)) → G))
        (sliceCoordEquiv (N := N) hN2))
      = (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG))).withDensity
          (jDensity μG ρ hN2 β) := by
  have hF : Measurable (fun q => ∫⁻ u : ↥(slice1InCompl (N := N))ᶜ → G,
      (jointDensity (N := N) μG ρ β ∘
        ⇑(MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G)))) (q, u)
      ∂(Measure.pi
        fun _ : ↥(slice1InCompl (N := N))ᶜ => μG)) :=
    ((measurable_jointDensity (N := N) μG ρ hρcont β).comp
      (MeasurableEquiv.prodAssoc
        (α := (↥(sliceLinks (N := N)) → G))
        (β := (↥(slice1InCompl (N := N)) → G))
        (γ := (↥(slice1InCompl (N := N))ᶜ → G))).measurable).lintegral_prod_right'
  have hmp2 : (((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG))).map
      ⇑(MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (↥(sliceLinks (N := N)) → G))
        (sliceCoordEquiv (N := N) hN2))
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)) :=
    ((MeasurePreserving.id
      (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)).prod
        (measurePreserving_sliceCoordEquiv μG hN2)).map_eq
  have heq := withDensity_map_equiv
    (μ := ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(slice1InCompl (N := N)) => μG)))
    hF
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (↥(sliceLinks (N := N)) → G))
      (sliceCoordEquiv (N := N) hN2))
  refine heq.trans ?_
  rw [hmp2]
  congr 1

/-- **Claim C.** The two-slice measure is the product
Haar measure on the pair of slices with density
`jDensity`. -/
theorem twoSliceMeasure_eq
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    twoSliceMeasure μG ρ hN2 hρcont β
      = ((Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG)).withDensity
          (jDensity μG ρ hN2 β) := by
  have hcomp : (fun U : Config (Fin 4 → ZMod N) G =>
        (restrictConfig (sliceLinks (N := N)) U,
          nextConfig (N := N) hN2 U))
      = twoSliceSplitMap (N := N) hN2
          ∘ ⇑(splitE (G := G) (N := N)) :=
    funext fun U => (twoSliceSplitMap_splitE hN2 U).symm
  have step0 : twoSliceMeasure μG ρ hN2 hρcont β
      = ((gibbsMeasure (torusShift N) μG ρ β).map
          ⇑(splitE (G := G) (N := N))).map
          (twoSliceSplitMap (N := N) hN2) := by
    unfold twoSliceMeasure
    rw [hcomp, Measure.map_map
      (measurable_twoSliceSplitMap (N := N) hN2)
      (splitE (G := G) (N := N)).measurable]
  rw [step0, gibbsMeasure_map_splitE (N := N) μG ρ hρcont β,
    twoSliceSplitMap_factor' (N := N) hN2,
    ← Measure.map_map
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (↥(sliceLinks (N := N)) → G))
        (sliceCoordEquiv (N := N) hN2)).measurable
      (measurable_fst.comp
        (MeasurableEquiv.prodAssoc
          (α := (↥(sliceLinks (N := N)) → G))
          (β := (↥(slice1InCompl (N := N)) → G))
          (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm.measurable),
    ← Measure.map_map measurable_fst
      (MeasurableEquiv.prodAssoc
        (α := (↥(sliceLinks (N := N)) → G))
        (β := (↥(slice1InCompl (N := N)) → G))
        (γ := (↥(slice1InCompl (N := N))ᶜ → G))).symm.measurable,
    withDensity_jointDensity_map_prodAssoc_symm μG ρ hρcont β,
    withDensity_jointDensity_map_fst μG ρ hρcont β,
    withDensity_fiber_map_prodCongr μG ρ hρcont hN2 β]

/-- The slice density, read as a real number, lies in
the two-sided exponential window. -/
theorem sliceDensity_toReal_mem
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (z : ↥(sliceLinks (N := N)) → G) :
    Real.exp (-2 * actionBound (N := N) β)
        ≤ (sliceDensity (N := N) μG ρ β z).toReal
      ∧ (sliceDensity (N := N) μG ρ β z).toReal
        ≤ Real.exp (2 * actionBound (N := N) β) := by
  have hne : sliceDensity (N := N) μG ρ β z ≠ ⊤ :=
    ne_top_of_le_ne_top (densityHi_ne_top (N := N) β)
      (sliceDensity_le μG ρ hρcont hd β z)
  constructor
  · calc Real.exp (-2 * actionBound (N := N) β)
        = (densityLo (N := N) β).toReal :=
          (ENNReal.toReal_ofReal (Real.exp_nonneg _)).symm
      _ ≤ (sliceDensity (N := N) μG ρ β z).toReal :=
          ENNReal.toReal_mono hne
            (sliceDensity_ge μG ρ hρcont hd β z)
  · calc (sliceDensity (N := N) μG ρ β z).toReal
        ≤ (densityHi (N := N) β).toReal :=
          ENNReal.toReal_mono (densityHi_ne_top (N := N) β)
            (sliceDensity_le μG ρ hρcont hd β z)
      _ = Real.exp (2 * actionBound (N := N) β) :=
          ENNReal.toReal_ofReal (Real.exp_nonneg _)

theorem jDensity_toReal_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    (jDensity μG ρ hN2 β p).toReal
      ≤ Real.exp (2 * actionBound (N := N) β) := by
  calc (jDensity μG ρ hN2 β p).toReal
      ≤ (densityHi (N := N) β).toReal :=
        ENNReal.toReal_mono (densityHi_ne_top (N := N) β)
          (jDensity_le μG ρ hρcont hd hN2 β p)
    _ = Real.exp (2 * actionBound (N := N) β) :=
        ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- The candidate `HDen` density as a real-valued ratio:
the two-slice density over the product of the marginal
densities. -/
noncomputable def kReal (hN2 : 2 ≤ N) (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) → ℝ :=
  fun p => (jDensity μG ρ hN2 β p).toReal
    / ((sliceDensity (N := N) μG ρ β p.1).toReal
      * (sliceDensity (N := N) μG ρ β p.2).toReal)

theorem kReal_nonneg
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    0 ≤ kReal μG ρ hN2 β p :=
  div_nonneg ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

theorem kReal_le
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    kReal μG ρ hN2 β p
      ≤ Real.exp (6 * actionBound (N := N) β) := by
  have h1 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.1).1
  have h2 := (sliceDensity_toReal_mem μG ρ hρcont hd β p.2).1
  have hpos : 0 < (sliceDensity (N := N) μG ρ β p.1).toReal
      * (sliceDensity (N := N) μG ρ β p.2).toReal :=
    mul_pos (lt_of_lt_of_le (Real.exp_pos _) h1)
      (lt_of_lt_of_le (Real.exp_pos _) h2)
  rw [show kReal μG ρ hN2 β p
      = (jDensity μG ρ hN2 β p).toReal
        / ((sliceDensity (N := N) μG ρ β p.1).toReal
          * (sliceDensity (N := N) μG ρ β p.2).toReal) from rfl,
    div_le_iff₀ hpos]
  calc (jDensity μG ρ hN2 β p).toReal
      ≤ Real.exp (2 * actionBound (N := N) β) :=
        jDensity_toReal_le μG ρ hρcont hd hN2 β p
    _ = Real.exp (6 * actionBound (N := N) β)
          * (Real.exp (-2 * actionBound (N := N) β)
            * Real.exp (-2 * actionBound (N := N) β)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (6 * actionBound (N := N) β)
          * ((sliceDensity (N := N) μG ρ β p.1).toReal
            * (sliceDensity (N := N) μG ρ β p.2).toReal) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h1 h2 (Real.exp_nonneg _)
            ENNReal.toReal_nonneg)
          (Real.exp_nonneg _)

/-- The candidate `HDen` kernel. -/
noncomputable def hdKernel (hN2 : 2 ≤ N) (β : ℝ) :
    ((↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) → ℂ :=
  fun p => (kReal μG ρ hN2 β p : ℂ)

theorem measurable_kReal
    (hρcont : Continuous fun g => repMatrix ρ g) (hN2 : 2 ≤ N)
    (β : ℝ) :
    Measurable (kReal μG ρ hN2 β) :=
  (measurable_jDensity μG ρ hρcont hN2 β).ennreal_toReal.div
    (((measurable_sliceDensity (N := N) μG ρ hρcont β).comp
      measurable_fst).ennreal_toReal.mul
      ((measurable_sliceDensity (N := N) μG ρ hρcont β).comp
        measurable_snd).ennreal_toReal)

theorem measurable_hdKernel
    (hρcont : Continuous fun g => repMatrix ρ g) (hN2 : 2 ≤ N)
    (β : ℝ) :
    Measurable (hdKernel μG ρ hN2 β) :=
  (Complex.continuous_ofReal.measurable).comp
    (measurable_kReal μG ρ hρcont hN2 β)

theorem memLp_hdKernel
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    MemLp (hdKernel μG ρ hN2 β) 2
      ((sliceMeasure μG ρ β).prod (sliceMeasure μG ρ β)) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ
    hρcont hd β
  refine MemLp.of_bound
    (measurable_hdKernel μG ρ hρcont hN2 β).aestronglyMeasurable
    (Real.exp (6 * actionBound (N := N) β))
    (Filter.Eventually.of_forall fun p => ?_)
  calc ‖hdKernel μG ρ hN2 β p‖
      = |kReal μG ρ hN2 β p| :=
        RCLike.norm_ofReal (kReal μG ρ hN2 β p)
    _ = kReal μG ρ hN2 β p :=
        abs_of_nonneg
          (kReal_nonneg μG ρ hρcont hd hN2 β p)
    _ ≤ Real.exp (6 * actionBound (N := N) β) :=
        kReal_le μG ρ hρcont hd hN2 β p

/-- The pointwise `ℝ≥0∞` identity at the heart of
Claim D. -/
theorem sliceDensity_mul_ofReal_kReal
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ)
    (p : (↥(sliceLinks (N := N)) → G) ×
      (↥(sliceLinks (N := N)) → G)) :
    (sliceDensity (N := N) μG ρ β p.1
        * sliceDensity (N := N) μG ρ β p.2)
      * ENNReal.ofReal (kReal μG ρ hN2 β p)
      = jDensity μG ρ hN2 β p := by
  have hlp : 0 < densityLo (N := N) β :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hne1 : sliceDensity (N := N) μG ρ β p.1 ≠ 0 :=
    (hlp.trans_le (sliceDensity_ge μG ρ hρcont hd β p.1)).ne'
  have hne2 : sliceDensity (N := N) μG ρ β p.2 ≠ 0 :=
    (hlp.trans_le (sliceDensity_ge μG ρ hρcont hd β p.2)).ne'
  have htop1 : sliceDensity (N := N) μG ρ β p.1 ≠ ⊤ :=
    ne_top_of_le_ne_top (densityHi_ne_top (N := N) β)
      (sliceDensity_le μG ρ hρcont hd β p.1)
  have htop2 : sliceDensity (N := N) μG ρ β p.2 ≠ ⊤ :=
    ne_top_of_le_ne_top (densityHi_ne_top (N := N) β)
      (sliceDensity_le μG ρ hρcont hd β p.2)
  have htopJ : jDensity μG ρ hN2 β p ≠ ⊤ :=
    ne_top_of_le_ne_top (densityHi_ne_top (N := N) β)
      (jDensity_le μG ρ hρcont hd hN2 β p)
  have hpos1 : 0 < (sliceDensity (N := N) μG ρ β p.1).toReal :=
    lt_of_lt_of_le (Real.exp_pos _)
      (sliceDensity_toReal_mem μG ρ hρcont hd β p.1).1
  have hpos2 : 0 < (sliceDensity (N := N) μG ρ β p.2).toReal :=
    lt_of_lt_of_le (Real.exp_pos _)
      (sliceDensity_toReal_mem μG ρ hρcont hd β p.2).1
  show (sliceDensity (N := N) μG ρ β p.1
        * sliceDensity (N := N) μG ρ β p.2)
      * ENNReal.ofReal ((jDensity μG ρ hN2 β p).toReal
        / ((sliceDensity (N := N) μG ρ β p.1).toReal
          * (sliceDensity (N := N) μG ρ β p.2).toReal))
      = jDensity μG ρ hN2 β p
  rw [ENNReal.ofReal_div_of_pos (mul_pos hpos1 hpos2),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal htop1, ENNReal.ofReal_toReal htop2,
    ENNReal.ofReal_toReal htopJ]
  exact ENNReal.mul_div_cancel (mul_ne_zero hne1 hne2)
    (ENNReal.mul_ne_top htop1 htop2)

/-- **Claim D.** The two-slice measure is the product of
the slice measures with density
`ENNReal.ofReal ∘ kReal`. -/
theorem twoSliceMeasure_eq_kernelDensity
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    twoSliceMeasure μG ρ hN2 hρcont β
      = ((sliceMeasure μG ρ β).prod
          (sliceMeasure μG ρ β)).withDensity
          (fun p => ENNReal.ofReal (kReal μG ρ hN2 β p)) := by
  have hMf : Measurable (fun z :
        (↥(sliceLinks (N := N)) → G) ×
          (↥(sliceLinks (N := N)) → G) =>
      sliceDensity (N := N) μG ρ β z.1
        * sliceDensity (N := N) μG ρ β z.2) :=
    ((measurable_sliceDensity (N := N) μG ρ hρcont β).comp
      measurable_fst).mul
      ((measurable_sliceDensity (N := N) μG ρ hρcont β).comp
        measurable_snd)
  have hKg : Measurable (fun p =>
      ENNReal.ofReal (kReal μG ρ hN2 β p)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_kReal μG ρ hρcont hN2 β)
  rw [twoSliceMeasure_eq μG ρ hρcont hd hN2 β,
    sliceMeasure_eq μG ρ hρcont β,
    prod_withDensity
      (measurable_sliceDensity (N := N) μG ρ hρcont β)
      (measurable_sliceDensity (N := N) μG ρ hρcont β),
    ← withDensity_mul _ hMf hKg]
  congr 1
  funext p
  exact (sliceDensity_mul_ofReal_kReal μG ρ hρcont hd hN2 β p).symm

/-- **The discharge (Claim E).** `HDen` holds at every
real `β`, at every seat of this shape: the two-slice law
has the explicit bounded density `hdKernel` with respect
to the product of the marginals. -/
theorem hden_all
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN2 : 2 ≤ N) (β : ℝ) :
    HDen μG ρ β hN2 hρcont hd :=
  ⟨hdKernel μG ρ hN2 β, memLp_hdKernel μG ρ hρcont hd hN2 β,
   fun g f => by
     have hpt : ∀ p : (↥(sliceLinks (N := N)) → G) ×
          (↥(sliceLinks (N := N)) → G),
        star (g p.1) * ((hdKernel μG ρ hN2 β) p * f p.2)
          = (ENNReal.ofReal (kReal μG ρ hN2 β p)).toReal
            • ((starRingEnd ℂ) (g p.1) * f p.2) := by
       intro p
       rw [ENNReal.toReal_ofReal
          (kReal_nonneg μG ρ hρcont hd hN2 β p),
        Complex.real_smul]
       have e1 : (hdKernel μG ρ hN2 β) p
          = (kReal μG ρ hN2 β p : ℂ) := rfl
       have e2 : (starRingEnd ℂ) (g p.1) = star (g p.1) := rfl
       rw [e1, e2]
       ring
     calc inner ℂ g (kernelLinMap μG ρ β hρcont hd
            (hdKernel μG ρ hN2 β)
            (memLp_hdKernel μG ρ hρcont hd hN2 β) f)
         = ∫ p, star (g p.1) * ((hdKernel μG ρ hN2 β) p * f p.2)
            ∂((sliceMeasure μG ρ β).prod
              (sliceMeasure μG ρ β)) :=
          kernelLinMap_inner μG ρ β hρcont hd
            (hdKernel μG ρ hN2 β)
            (memLp_hdKernel μG ρ hρcont hd hN2 β) g f
       _ = ∫ p, (ENNReal.ofReal (kReal μG ρ hN2 β p)).toReal
              • ((starRingEnd ℂ) (g p.1) * f p.2)
            ∂((sliceMeasure μG ρ β).prod
              (sliceMeasure μG ρ β)) :=
          integral_congr_ae
            (Filter.Eventually.of_forall hpt)
       _ = ∫ p, (starRingEnd ℂ) (g p.1) * f p.2
            ∂(twoSliceMeasure μG ρ hN2 hρcont β) := by
          rw [twoSliceMeasure_eq_kernelDensity
            μG ρ hρcont hd hN2 β]
          exact (integral_withDensity_eq_integral_toReal_smul
            (ENNReal.measurable_ofReal.comp
              (measurable_kReal μG ρ hρcont hN2 β))
            (Filter.Eventually.of_forall fun _ =>
              ENNReal.ofReal_lt_top) _).symm
       _ = inner ℂ g (transferOp μG ρ hN2 hρcont β f) :=
          (transferOp_inner_twoSlice μG ρ hN2 hρcont β g f).symm⟩

end HDenDischarge

section Seat

/-- **The discharge at the seat.** `HDen` holds at the
`U(1)` seat, at every real `β`, in exactly the form the
seat packages consume it. -/
theorem hden_seat {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) (β : ℝ) :
    HDen (haarProb Circle) circleRep β hN2 circleRep_continuous
      zero_lt_one :=
  hden_all (haarProb Circle) circleRep circleRep_continuous
    zero_lt_one hN2 β

/-- **The endpoint.** Q12's per-instance gap at the `U(1)`
seat, unconditional apart from the carried Hilbert basis
(separability carried as data, FG-1's convention): at
every even `N ≥ 2` and every `β > 0`, some `δ > 0` bounds
every non-vacuum spectral point of the transfer operator
by `1 − δ` in norm. Per-instance only — no uniformity in
`N` or `β` is claimed. -/
theorem gapBoundU1_unconditional {N : ℕ} [NeZero N]
    (hβ : 0 < β) (hN2 : 2 ≤ N) (hN : Even N)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    ∃ δ > 0, GapBoundU1 β hN2 δ :=
  gapBoundU1_of_weld hβ hN2 hN (hden_seat hN2 β) b

end Seat

end ThetLogos
