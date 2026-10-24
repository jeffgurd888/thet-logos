import ThetLogos.LatticeTransfer

/-!
# ThetLogos.LatticeTransferID — transfer-matrix route, step S1:
the depth-one identification

The R0 gate of the transfer-matrix charter
(`whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`)
passed on paper: at depth one — a *slice* observable — the OS
diagonal is the depth-one transfer quadratic form, modulo two
finite plumbing lemmas (the gate memo,
`routeb-general-scratch/verdict-memo-tm-r0.md`). This module
formalizes exactly that chain:

- **L1** (`restrict_sliceLinks_reflConfig`): the slice reading
  of a reflected configuration is the reflected-slice reading
  transported back along `sliceReflEquiv` — the mirror image of
  the landed `restrict_reflConfig_eq`.
- **L2** (the axis reflection `axisRefl`): reflection composed
  with a one-step forward time shift preserves the Gibbs
  measure (`gibbsMeasure_map_axisRefl`), fixes the slice
  reading (`restrict_sliceLinks_axisRefl`), and sends the
  transported reflected-slice reading to the next-slice reading
  (`reflectedSliceReading_axisRefl`).
- **Headline** (`osForm_depthOne_transfer`): for a slice
  observable `φ`, at general `(G, ρ)`, every real `β`, even
  `N` with `2 ≤ N`,
  `osForm β F F = ⟪sliceState β φ, transferOp (sliceState β φ)⟫`
  with `F U = φ (restrictConfig sliceLinks U)`.

Scope fence (the gate memo's §6, kept): this is the **slice
subclass only** (depth one). It asserts nothing about deeper
observables, nothing about positivity of the transfer operator
on arbitrary vectors, and it does not consume the layer/Markov
factorization of the Gibbs measure.

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1); general `(G, ρ)` OPEN).

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  L1, L2 (a/b/c), the headline `osForm_depthOne_transfer` and
  the β = 0 companion are machine-checked (parent-verified
  rebuild, 3,552 jobs; axioms standard, no `sorryAx`).
  Dossier:
  `whitepaper/gram-transfer-s1-depth-one-identification-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section DepthOne

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. Lemma L1: the slice reading of the reflection -/

/-- **Lemma L1 (slice reading of the reflection).** The
restriction of a reflected configuration to the time-`0` slice
is the reflected-slice restriction transported back along the
slice equivalence. The exact mirror of the landed
`restrict_reflConfig_eq`, which computes the other
restriction. -/
theorem restrict_sliceLinks_reflConfig
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (reflConfig U)
      = fun ℓ : ↥(sliceLinks (N := N)) =>
          restrictConfig reflSliceLinks U (sliceReflEquiv ℓ) := by
  funext ℓ
  obtain ⟨⟨x, μ⟩, hℓ⟩ := ℓ
  have hμ : μ ≠ 0 := (mem_sliceLinks.mp hℓ).1
  have hpair : (sliceReflEquiv ⟨⟨x, μ⟩, hℓ⟩).1 = (reflSite x, μ) := by
    show reflLink (x, μ) = (reflSite x, μ)
    exact reflLink_of_ne hμ
  show reflConfig U (x, μ)
    = restrictConfig reflSliceLinks U (sliceReflEquiv ⟨⟨x, μ⟩, hℓ⟩)
  show reflConfig U (x, μ) = U ((sliceReflEquiv ⟨⟨x, μ⟩, hℓ⟩).1)
  rw [hpair]
  exact reflConfig_apply_of_ne U hμ

/-! ## §2. Lemma L2: the axis reflection -/

/-- The **axis reflection**: reflect, after a one-step forward
time shift. As a configuration map it reads `U` at time
`-(x 0)` — the reflection about the axis through time slices
`0` and `N/2`. -/
def axisRefl : Config (Fin 4 → ZMod N) G
    → Config (Fin 4 → ZMod N) G :=
  reflConfig ∘ shiftConfig (torusShift N 0)

theorem measurable_axisRefl :
    Measurable (axisRefl (G := G) (N := N)) :=
  measurable_reflConfig.comp (measurable_shiftConfig (torusShift N 0))

/-- The one-step shift of a reflected site, in update form:
`σ₀ (θ x) = update x 0 (-(x 0))`. -/
theorem torusShift_zero_reflSite (x : Fin 4 → ZMod N) :
    torusShift N 0 (reflSite x)
      = Function.update x 0 (-(x 0)) := by
  funext j
  rw [torusShift_apply, Pi.add_apply]
  by_cases hj : j = 0
  · subst hj
    rw [Pi.single_eq_same, reflSite_apply_self, Function.update_self]
    ring
  · rw [Pi.single_eq_of_ne hj, reflSite_apply_of_ne _ hj,
      Function.update_of_ne hj, zero_add]

/-- The axis reflection at a spatial link: it reads `U` at the
same site with the time coordinate negated, same direction
(the strict factor of the gate memo's step C). -/
theorem axisRefl_apply_of_ne (U : Config (Fin 4 → ZMod N) G)
    {x : Fin 4 → ZMod N} {μ : Fin 4} (hμ : μ ≠ 0) :
    axisRefl U (x, μ) = U (Function.update x 0 (-(x 0)), μ) := by
  show reflConfig (shiftConfig (torusShift N 0) U) (x, μ) = _
  rw [reflConfig_apply_of_ne _ hμ]
  show U (torusShift N 0 (reflSite x), μ) = _
  rw [torusShift_zero_reflSite]

/-- **Lemma L2 (a): the axis reflection preserves the Gibbs
measure** — the composition of the two landed invariances
(shift, then reflection) under `Measure.map`. -/
theorem gibbsMeasure_map_axisRefl
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (β : ℝ) :
    Measure.map axisRefl (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  have hcomp : axisRefl (G := G) (N := N)
      = reflConfig ∘ shiftConfig (torusShift N 0) := rfl
  rw [hcomp, ← Measure.map_map measurable_reflConfig
      (measurable_shiftConfig (torusShift N 0)),
    gibbsMeasure_map_shiftConfig μG ρ (torusShift N 0)
      torusShift_one_hcomm hρcont β,
    gibbsMeasure_map_reflConfig ρ μG hρcont hN β]

/-- **Lemma L2 (b): the axis reflection fixes the slice
reading** — a slice link has time `0`, and `-(0) = 0`. -/
theorem restrict_sliceLinks_axisRefl
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (axisRefl U)
      = restrictConfig sliceLinks U := by
  funext ℓ
  obtain ⟨⟨x, μ⟩, hℓ⟩ := ℓ
  have hμ : μ ≠ 0 := (mem_sliceLinks.mp hℓ).1
  have hx0 : x 0 = 0 := (ZMod.val_eq_zero _).mp (mem_sliceLinks.mp hℓ).2
  have hupd : Function.update x 0 (-(x 0)) = x := by
    have hneg : -(x 0) = x 0 := by rw [hx0, neg_zero]
    rw [hneg, Function.update_eq_self]
  show axisRefl U (x, μ) = U (x, μ)
  rw [axisRefl_apply_of_ne U hμ, hupd]

/-- **Lemma L2 (c): the transported reflected-slice reading
of the axis-reflected configuration is the next-slice
reading** — at a slice link, the axis reflection's source
time is `-(-1) = 1`. -/
theorem reflectedSliceReading_axisRefl (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    (fun ℓ : ↥(sliceLinks (N := N)) =>
        restrictConfig reflSliceLinks (axisRefl U) (sliceReflEquiv ℓ))
      = nextConfig hN2 U := by
  funext ℓ
  obtain ⟨⟨x, μ⟩, hℓ⟩ := ℓ
  have hμ : μ ≠ 0 := (mem_sliceLinks.mp hℓ).1
  have hx0 : x 0 = 0 := (ZMod.val_eq_zero _).mp (mem_sliceLinks.mp hℓ).2
  have hpair : (sliceReflEquiv ⟨⟨x, μ⟩, hℓ⟩).1 = (reflSite x, μ) := by
    show reflLink (x, μ) = (reflSite x, μ)
    exact reflLink_of_ne hμ
  have hupd : Function.update (reflSite x) 0 (-((reflSite x) 0))
      = Function.update x 0 1 := by
    funext j
    by_cases hj : j = 0
    · subst hj
      rw [Function.update_self, Function.update_self,
        reflSite_apply_self, hx0]
      ring
    · rw [Function.update_of_ne hj, Function.update_of_ne hj,
        reflSite_apply_of_ne _ hj]
  have hpair01 : (slice01Equiv hN2 ⟨⟨x, μ⟩, hℓ⟩).1
      = (Function.update x 0 1, μ) := rfl
  show axisRefl U ((sliceReflEquiv ⟨⟨x, μ⟩, hℓ⟩).1)
    = nextConfig hN2 U ⟨⟨x, μ⟩, hℓ⟩
  rw [hpair, axisRefl_apply_of_ne U hμ, hupd]
  show U (Function.update x 0 1, μ)
    = U ((slice01Equiv hN2 ⟨⟨x, μ⟩, hℓ⟩).1)
  rw [hpair01]

/-! ## §3. The depth-one identification -/

/-- **The depth-one identification (transfer-matrix route,
step S1).** For a slice observable `φ` — the OS form's
diagonal at the pulled-back observable
`F U = φ (restrictConfig sliceLinks U)` is the depth-one
transfer quadratic form at the prepared slice state. At
general `(G, ρ)`, every real `β`, even `N` with `2 ≤ N`.
The gate memo's chain, formalized: reflection substitution
(Step B), the axis-reflection substitution (Step C, via L2),
and the landed form identity `transferOp_inner`. -/
theorem osForm_depthOne_transfer
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d) (β : ℝ)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)) :
    osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
        (fun U => φ (restrictConfig sliceLinks U))
      = inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)) := by
  -- AE strong measurability of the pulled-back observable.
  have hFsm : AEStronglyMeasurable
      (fun U => φ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    hφ.aestronglyMeasurable.comp_aemeasurable
      (measurable_restrictConfig sliceLinks).aemeasurable
  -- AE strong measurability of the OS integrand.
  have hΦsm : AEStronglyMeasurable
      (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
        * φ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    (aesm_reflObs μG ρ hρcont hN β hFsm).mul hFsm
  -- AE strong measurability of the substituted integrand Ξ.
  have hΞsm : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * φ (restrictConfig sliceLinks (reflConfig U)))
      (gibbsMeasure (torusShift N) μG ρ β) := by
    have hF2 : AEStronglyMeasurable
        (fun U => φ (restrictConfig sliceLinks U))
        (Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)) := by
      rwa [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
    have hB : AEStronglyMeasurable
        ((fun U => φ (restrictConfig sliceLinks U)) ∘ reflConfig)
        (gibbsMeasure (torusShift N) μG ρ β) :=
      hF2.comp_measurable measurable_reflConfig
    exact ((RCLike.continuous_conj).comp_aestronglyMeasurable
      hFsm).mul hB
  -- The axis-reflection substitution, as an integral identity.
  have hΞsm' : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * φ (restrictConfig sliceLinks (reflConfig U)))
      (Measure.map axisRefl (gibbsMeasure (torusShift N) μG ρ β)) := by
    rwa [gibbsMeasure_map_axisRefl μG ρ hρcont hN β]
  have hsub : ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * φ (restrictConfig sliceLinks (reflConfig U))
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ U, (starRingEnd ℂ)
          (φ (restrictConfig sliceLinks (axisRefl U)))
          * φ (restrictConfig sliceLinks (reflConfig (axisRefl U)))
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    have h := integral_map measurable_axisRefl.aemeasurable hΞsm'
    rwa [gibbsMeasure_map_axisRefl μG ρ hρcont hN β] at h
  -- The two AE replacements of the transfer form's kernel
  -- pairing by `φ` itself.
  have h1 : ⇑(sliceState μG ρ β φ hφ) ∘ restrictConfig sliceLinks
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      φ ∘ restrictConfig sliceLinks :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => ⇑(sliceState μG ρ β φ hφ) z = φ z) hφ.coeFn_toLp
  have h2 : ⇑(sliceState μG ρ β φ hφ) ∘ nextConfig hN2
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      φ ∘ nextConfig hN2 := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig μG ρ hN2 hρcont β).map_eq
    have hcoe : ⇑(sliceState μG ρ β φ hφ)
        =ᵐ[(gibbsMeasure (torusShift N) μG ρ β).map (nextConfig hN2)] φ := by
      rw [hmap]
      exact hφ.coeFn_toLp
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      (p := fun z => ⇑(sliceState μG ρ β φ hφ) z = φ z) hcoe
  calc osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
          (fun U => φ (restrictConfig sliceLinks U))
      = ∫ U, reflObs (fun U => φ (restrictConfig sliceLinks U)) U
          * φ (restrictConfig sliceLinks U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        osForm_eq_integral μG ρ hρcont hd β _ _
    _ = ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
          * φ (restrictConfig sliceLinks (reflConfig U))
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        have h := integral_comp_reflConfig μG ρ hρcont hN β
          (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
            * φ (restrictConfig sliceLinks U)) hΦsm
        rw [← h]
        apply integral_congr_ae
        filter_upwards with U
        show reflObs (fun U => φ (restrictConfig sliceLinks U))
            (reflConfig U) * φ (restrictConfig sliceLinks (reflConfig U))
          = (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
            * φ (restrictConfig sliceLinks (reflConfig U))
        rw [reflObs_reflConfig]
    _ = ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
          * φ (nextConfig hN2 U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        rw [hsub]
        apply integral_congr_ae
        filter_upwards with U
        show (starRingEnd ℂ)
            (φ (restrictConfig sliceLinks (axisRefl U)))
            * φ (restrictConfig sliceLinks (reflConfig (axisRefl U)))
          = (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
            * φ (nextConfig hN2 U)
        rw [restrict_sliceLinks_axisRefl, restrict_sliceLinks_reflConfig,
          reflectedSliceReading_axisRefl hN2]
    _ = inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)) := by
        rw [transferOp_inner μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)
          (sliceState μG ρ β φ hφ)]
        apply integral_congr_ae
        filter_upwards [h1, h2] with U h1U h2U
        simp only [Function.comp_apply] at h1U h2U
        rw [h1U, h2U]

/-- **Cross-check at `β = 0` (the gate memo's §4).** At zero
coupling the transfer operator is the vacuum projection, so
the depth-one diagonal is the squared modulus of the vacuum
expectation — in particular it is real and nonnegative. -/
theorem osForm_depthOne_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ 0)) :
    (osForm μG ρ 0 (fun U => φ (restrictConfig sliceLinks U))
        (fun U => φ (restrictConfig sliceLinks U))).im = 0
      ∧ 0 ≤ (osForm μG ρ 0 (fun U => φ (restrictConfig sliceLinks U))
          (fun U => φ (restrictConfig sliceLinks U))).re := by
  have h := osForm_depthOne_transfer μG ρ hρcont hN hN2 hd 0 φ hφ
  rw [h, transferOp_zero_apply μG ρ hN2 hρcont hd
    (sliceState μG ρ 0 φ hφ), inner_smul_right, ← inner_conj_symm]
  constructor
  · rw [mul_comm, Complex.mul_conj]
    exact Complex.ofReal_im _
  · rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

end DepthOne

end ThetLogos
