import ThetLogos.LatticeTransferID
import ThetLogos.LatticeLayerFactor

/-!
# ThetLogos.LatticeTransferIdent — transfer-matrix route, rung R3:
the identification half (preparation and powers, positivity-free)

Gap-queue item Q8 / charter
(`whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`,
§4, rung R3) was **split** by the gap audit and the R2
obstruction dossier
(`whitepaper/gram-transfer-r2-obstruction-2026-10-24.md`, §7):
the *positivity* half (positivity of odd transfer powers) is
BLOCKED — it is R2 on the range of `T^k`, and R2 is killed.
This module builds the **identification half only**: equalities
of forms and of operators on their domains of definition.
**No positivity is asserted anywhere in this module** — no
`T̂ ≥ 0`, no PSD claim, no `osForm_nonneg`. (Even-power
nonnegativity was already free from landed adjoint algebra
and is not restated here.)

What is identified, and at what depth:

- **§2, depth one, polarized** (`osForm_depthOne_transfer_pair`):
  S1 (`osForm_depthOne_transfer`) is the diagonal; here the
  full sesquilinear identity at depth one, for two slice
  observables `φ, χ`:
  `osForm β F_φ F_χ = ⟪sliceState φ, transferOp (sliceState χ)⟫`.
  This is the transfer-matrix side of the S2-0 paper gate's
  weld floor T5.2, stated and proved on the nose — the gate's
  `H_OS` does not exist yet (S2-2 unbuilt), so the identity
  lives here as a statement about `osForm` and `transferOp`
  pairings on slice states, which is exactly T5.2's content
  minus the quotient-space notation.
- **§2, every depth** (`osForm_depthM`): the OS form of two
  slice observables equals the depth-`m` reflected pairing
  `∫ conj(φ (reflStepReading m U)) · χ (stepConfig m U) dGibbs`
  for **every** `m : ℕ` — S1's substitution with the depth-`m`
  axis reflection `axisReflM m = reflConfig ∘ shiftPow m`
  (Gibbs-invariant, §1). At `m = 1` this is the same OS form
  read at depth one in reflected dress; S1 reads it in
  transfer dress.
- **§3, the two-point operator** (`twoPointOp`): the operator
  whose form is the Gibbs two-point pairing at separation `m`,
  `twoPointOp m = (slicePull)† ∘L stepPull m`. Its form
  identity (`twoPointOp_inner`) is proved at every `m`; at
  `m = 0` its form is the OS inner product
  (`twoPointOp_zero_inner`); at `m = 1` it **is** the transfer
  operator (`twoPointOp_one`, from `stepConfig_one`:
  the depth-one reading is `nextConfig`). Consistency with
  the S2-0 gate's companion catch: the OS norm on slice
  classes is the `transferOp`-form norm, and §2's polarized
  identity is stated for exactly that form — no `L²`-norm
  identification of slice classes is made or needed here.

What is **not** identified, by name (the registered gap):
`twoPointOp m = transferOp^m` for `m ≥ 2`, and with it
`osForm β F F = ⟪ψ_F, T^m ψ_F⟫` for a general strict-half
observable `F`. The missing step is the Markov/tower property
at the intermediate slices: passing from the two-point
pairing at separation `m` to the `m`-fold operator power
requires conditional expectations over slices `1, …, m−1`
(or, equivalently, iterating R1's layer factorization over
the positive half's layers — R1 factors at the single
half cut, and its iterated form is Fubini over the two
halves, not over layers). The corpus has neither. The
charter's pre-registered kill for Q8 ("preparation closes
for slice observables only — temporal links *inside* the
positive half couple the layers in a way the iteration does
not absorb") therefore fires against the *general-`F`*
statement, and this module lands the slice-class
identification instead, with the obstruction stated here
rather than smoothed. The prepared state exists in this
module exactly where the corpus supports it: `ψ = sliceState
φ` for slice observables, at the depths above.

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1) at all `β ≥ 0`; general `(G, ρ)`
OPEN). R2 stays killed; R4 stays blocked; nothing here
resurrects either.

- Status: brick R3-identification — built 2026-10-24 under
  the gap queue (Q8, identification half); verdict PARTIAL
  (general-`F` preparation and the `T^m` power identification
  obstructed as named above); parent-verified 2026-10-24
  (targeted build exit 0, strict recount, axiom check).
  Dossier:
  `whitepaper/transfer-r3-identification-partial-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section DepthReadings

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. Shift powers, depth readings, depth-`m` axis reflection -/

/-- The `m`-fold one-step time shift of a configuration,
as a configuration map (the iterate of `shiftConfig` along
the time translation `torusShift N 0`). -/
def shiftPow (m : ℕ) : Config (Fin 4 → ZMod N) G
    → Config (Fin 4 → ZMod N) G :=
  (shiftConfig (torusShift N 0))^[m]

theorem shiftPow_zero :
    shiftPow (G := G) (N := N) 0 = id :=
  Function.iterate_zero _

theorem shiftPow_succ (m : ℕ) :
    shiftPow (G := G) (N := N) (m + 1)
      = shiftPow m ∘ shiftConfig (torusShift N 0) :=
  Function.iterate_succ _ _

theorem measurable_shiftPow (m : ℕ) :
    Measurable (shiftPow (G := G) (N := N) m) := by
  induction m with
  | zero => rw [shiftPow_zero]; exact measurable_id
  | succ k ih =>
      rw [shiftPow_succ]
      exact ih.comp (measurable_shiftConfig _)

/-- The Gibbs measure is invariant under every shift power
(the one-step invariance `gibbsMeasure_map_shiftConfig` at
`torusShift_one_hcomm`, iterated). At every real `β`. -/
theorem gibbsMeasure_map_shiftPow
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) :
    Measure.map (shiftPow (G := G) (N := N) m)
        (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  induction m with
  | zero => rw [shiftPow_zero]; exact Measure.map_id
  | succ k ih =>
      rw [shiftPow_succ,
        ← Measure.map_map (measurable_shiftPow k)
          (measurable_shiftConfig _),
        gibbsMeasure_map_shiftConfig μG ρ (torusShift N 0)
          torusShift_one_hcomm hρcont β, ih]

/-- The **depth-`m` slice reading**: the time-`0` slice of
the `m`-step-shifted configuration — the configuration's
time-`m` slice, transported to the slice index set. -/
def stepConfig (m : ℕ) (U : Config (Fin 4 → ZMod N) G) :
    ↥(sliceLinks (N := N)) → G :=
  restrictConfig sliceLinks (shiftPow m U)

theorem measurable_stepConfig (m : ℕ) :
    Measurable (stepConfig (G := G) (N := N) m) :=
  (measurable_restrictConfig sliceLinks).comp
    (measurable_shiftPow m)

/-- The depth-`m` reading is measure-preserving from the
Gibbs measure to the slice measure, at every real `β`
(stationarity at depth `m`). -/
theorem measurePreserving_stepConfig
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) :
    MeasurePreserving (stepConfig (G := G) (N := N) m)
      (gibbsMeasure (torusShift N) μG ρ β)
      (sliceMeasure μG ρ β) := by
  have hcomp : stepConfig (G := G) (N := N) m
      = restrictConfig (G := G) sliceLinks ∘ shiftPow m := rfl
  rw [hcomp]
  exact (measurePreserving_slicePull μG ρ β).comp
    ⟨measurable_shiftPow m,
      gibbsMeasure_map_shiftPow μG ρ hρcont β m⟩

/-- At depth `0` the step reading is the time-`0`
restriction itself. -/
theorem stepConfig_zero (U : Config (Fin 4 → ZMod N) G) :
    stepConfig (G := G) (N := N) 0 U
      = restrictConfig sliceLinks U := by
  show restrictConfig sliceLinks (shiftPow 0 U) = _
  rw [shiftPow_zero]
  rfl

/-- At depth `1` the step reading is the next-slice
reading: the bridge between the step tower and the landed
transfer operator's second leg. -/
theorem stepConfig_one (hN2 : 2 ≤ N)
    (U : Config (Fin 4 → ZMod N) G) :
    stepConfig (G := G) (N := N) 1 U = nextConfig hN2 U := by
  have h1 : shiftPow (G := G) (N := N) 1
      = shiftConfig (torusShift N 0) := by
    have hcomp : shiftPow (G := G) (N := N) (0 + 1)
        = shiftPow 0 ∘ shiftConfig (torusShift N 0) :=
      Function.iterate_succ _ _
    rw [shiftPow_zero] at hcomp
    exact hcomp
  show restrictConfig sliceLinks (shiftPow 1 U) = nextConfig hN2 U
  rw [h1]
  exact restrict_shiftConfig_step hN2 U

/-- The **depth-`m` axis reflection**: reflect after
shifting `m` steps forward — S1's `axisRefl` is the case
`m = 1` up to the same formula. -/
def axisReflM (m : ℕ) : Config (Fin 4 → ZMod N) G
    → Config (Fin 4 → ZMod N) G :=
  reflConfig ∘ shiftPow m

theorem measurable_axisReflM (m : ℕ) :
    Measurable (axisReflM (G := G) (N := N) m) :=
  measurable_reflConfig.comp (measurable_shiftPow m)

/-- The depth-`m` axis reflection preserves the Gibbs
measure (shift-power invariance, then reflection
invariance). At every real `β`, even `N`. -/
theorem gibbsMeasure_map_axisReflM
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) (m : ℕ) :
    Measure.map (axisReflM (G := G) (N := N) m)
        (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  have hcomp : axisReflM (G := G) (N := N) m
      = reflConfig ∘ shiftPow m := rfl
  rw [hcomp, ← Measure.map_map measurable_reflConfig
      (measurable_shiftPow m),
    gibbsMeasure_map_shiftPow μG ρ hρcont β m,
    gibbsMeasure_map_reflConfig ρ μG hρcont hN β]

/-- The **reflected depth-`m` reading**: the time-`0`
slice of the depth-`m` axis reflection, read through the
landed slice-reflection transport (S1's lemma L1 at the
shifted configuration). -/
def reflStepReading (m : ℕ) (U : Config (Fin 4 → ZMod N) G) :
    ↥(sliceLinks (N := N)) → G :=
  fun ℓ => restrictConfig reflSliceLinks (shiftPow m U)
    (sliceReflEquiv ℓ)

/-- The slice reading of the depth-`m` axis reflection is
the reflected depth-`m` reading (S1's L1, verbatim at the
shifted configuration). -/
theorem restrict_sliceLinks_axisReflM (m : ℕ)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (axisReflM m U)
      = reflStepReading m U :=
  restrict_sliceLinks_reflConfig (shiftPow m U)

/-- Reflecting the depth-`m` axis reflection returns the
depth-`m` reading: the second factor of the OS integrand
under the depth-`m` substitution. -/
theorem restrict_refl_axisReflM (m : ℕ)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (reflConfig (axisReflM m U))
      = restrictConfig sliceLinks (shiftPow m U) := by
  have h : reflConfig (axisReflM (G := G) (N := N) m U)
      = shiftPow m U :=
    reflConfig_involutive _
  rw [h]

/-- The same identity in `stepConfig` form. -/
theorem restrict_refl_axisReflM_step (m : ℕ)
    (U : Config (Fin 4 → ZMod N) G) :
    restrictConfig sliceLinks (reflConfig (axisReflM m U))
      = stepConfig m U :=
  restrict_refl_axisReflM m U

end DepthReadings

section OSIdentification

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §2. The OS form at every depth, and polarized at depth one -/

/-- **The OS form at depth `m` (reflected dress).** For
slice observables `φ, χ`, the OS form equals the depth-`m`
reflected pairing — the conjugate of `φ` read on the
reflected depth-`m` slice against `χ` read on the depth-`m`
slice, integrated against the Gibbs measure — for **every**
`m : ℕ`, at general `(G, ρ)`, every real `β`, even `N` with
`2 ≤ N` not required (no transfer operator appears). The
proof is S1's substitution chain with the depth-`m` axis
reflection in place of the axis reflection: reflection
substitution, then the `axisReflM` substitution, then the
two reading lemmas of §1. No positivity is used or
asserted. -/
theorem osForm_depthM
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ) (m : ℕ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
        (fun U => χ (restrictConfig sliceLinks U))
      = ∫ U, (starRingEnd ℂ) (φ (reflStepReading m U))
          * χ (stepConfig m U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
  -- AE strong measurability of the two slice observables,
  -- pulled back to the full configuration space.
  have hFsm : AEStronglyMeasurable
      (fun U => φ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    hφ.aestronglyMeasurable.comp_aemeasurable
      (measurable_restrictConfig sliceLinks).aemeasurable
  have hGsm : AEStronglyMeasurable
      (fun U => χ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    hχ.aestronglyMeasurable.comp_aemeasurable
      (measurable_restrictConfig sliceLinks).aemeasurable
  -- AE strong measurability of the OS integrand.
  have hΦsm : AEStronglyMeasurable
      (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
        * χ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    (aesm_reflObs μG ρ hρcont hN β hFsm).mul hGsm
  -- AE strong measurability of the substituted integrand Ξ.
  have hΞsm : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U)))
      (gibbsMeasure (torusShift N) μG ρ β) := by
    have hB : AEStronglyMeasurable
        ((fun U => χ (restrictConfig sliceLinks U)) ∘ reflConfig)
        (gibbsMeasure (torusShift N) μG ρ β) := by
      have hF2 : AEStronglyMeasurable
          (fun U => χ (restrictConfig sliceLinks U))
          (Measure.map reflConfig
            (gibbsMeasure (torusShift N) μG ρ β)) := by
        rwa [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
      exact hF2.comp_measurable measurable_reflConfig
    exact ((RCLike.continuous_conj).comp_aestronglyMeasurable
      hFsm).mul hB
  -- The depth-`m` axis-reflection substitution.
  have hΞsm' : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U)))
      (Measure.map (axisReflM m)
        (gibbsMeasure (torusShift N) μG ρ β)) := by
    rwa [gibbsMeasure_map_axisReflM μG ρ hρcont hN β m]
  have hsub : ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U))
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ U, (starRingEnd ℂ)
          (φ (restrictConfig sliceLinks (axisReflM m U)))
          * χ (restrictConfig sliceLinks
              (reflConfig (axisReflM m U)))
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    have h := integral_map (measurable_axisReflM m).aemeasurable
      hΞsm'
    rwa [gibbsMeasure_map_axisReflM μG ρ hρcont hN β m] at h
  calc osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
          (fun U => χ (restrictConfig sliceLinks U))
      = ∫ U, reflObs (fun U => φ (restrictConfig sliceLinks U)) U
          * χ (restrictConfig sliceLinks U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        osForm_eq_integral μG ρ hρcont hd β _ _
    _ = ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
          * χ (restrictConfig sliceLinks (reflConfig U))
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        have h := integral_comp_reflConfig μG ρ hρcont hN β
          (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
            * χ (restrictConfig sliceLinks U)) hΦsm
        rw [← h]
        apply integral_congr_ae
        filter_upwards with U
        show reflObs (fun U => φ (restrictConfig sliceLinks U))
            (reflConfig U)
            * χ (restrictConfig sliceLinks (reflConfig U))
          = (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
            * χ (restrictConfig sliceLinks (reflConfig U))
        rw [reflObs_reflConfig]
    _ = ∫ U, (starRingEnd ℂ) (φ (reflStepReading m U))
          * χ (stepConfig m U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        rw [hsub]
        apply integral_congr_ae
        filter_upwards with U
        show (starRingEnd ℂ)
            (φ (restrictConfig sliceLinks (axisReflM m U)))
            * χ (restrictConfig sliceLinks
                (reflConfig (axisReflM m U)))
          = (starRingEnd ℂ) (φ (reflStepReading m U))
            * χ (stepConfig m U)
        rw [restrict_sliceLinks_axisReflM,
          restrict_refl_axisReflM_step]

/-- **The depth-one identification, polarized (transfer
dress).** For two slice observables `φ, χ`, the OS form is
the depth-one transfer pairing of the two prepared slice
states. This is S1's chain with the two observables kept
separate (S1 is the diagonal `χ = φ`), and it is the
transfer-matrix side of the S2-0 paper gate's weld floor
**T5.2**: the sesquilinear extension of S1's diagonal by
polarization, proved directly. At general `(G, ρ)`, every
real `β`, even `N` with `2 ≤ N`. No positivity is used or
asserted. -/
theorem osForm_depthOne_transfer_pair
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hN2 : 2 ≤ N) (hd : 0 < d) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
        (fun U => χ (restrictConfig sliceLinks U))
      = inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β χ hχ)) := by
  -- AE strong measurability of the two pulled-back observables.
  have hFsm : AEStronglyMeasurable
      (fun U => φ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    hφ.aestronglyMeasurable.comp_aemeasurable
      (measurable_restrictConfig sliceLinks).aemeasurable
  have hGsm : AEStronglyMeasurable
      (fun U => χ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    hχ.aestronglyMeasurable.comp_aemeasurable
      (measurable_restrictConfig sliceLinks).aemeasurable
  -- AE strong measurability of the OS integrand.
  have hΦsm : AEStronglyMeasurable
      (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
        * χ (restrictConfig sliceLinks U))
      (gibbsMeasure (torusShift N) μG ρ β) :=
    (aesm_reflObs μG ρ hρcont hN β hFsm).mul hGsm
  -- AE strong measurability of the substituted integrand Ξ.
  have hΞsm : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U)))
      (gibbsMeasure (torusShift N) μG ρ β) := by
    have hB2 : AEStronglyMeasurable
        ((fun U => χ (restrictConfig sliceLinks U)) ∘ reflConfig)
        (gibbsMeasure (torusShift N) μG ρ β) := by
      have hG2 : AEStronglyMeasurable
          (fun U => χ (restrictConfig sliceLinks U))
          (Measure.map reflConfig
            (gibbsMeasure (torusShift N) μG ρ β)) := by
        rwa [gibbsMeasure_map_reflConfig ρ μG hρcont hN β]
      exact hG2.comp_measurable measurable_reflConfig
    exact ((RCLike.continuous_conj).comp_aestronglyMeasurable
      hFsm).mul hB2
  -- The axis-reflection substitution, as an integral identity.
  have hΞsm' : AEStronglyMeasurable
      (fun U => (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U)))
      (Measure.map axisRefl
        (gibbsMeasure (torusShift N) μG ρ β)) := by
    rwa [gibbsMeasure_map_axisRefl μG ρ hρcont hN β]
  have hsub : ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
        * χ (restrictConfig sliceLinks (reflConfig U))
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ U, (starRingEnd ℂ)
          (φ (restrictConfig sliceLinks (axisRefl U)))
          * χ (restrictConfig sliceLinks (reflConfig (axisRefl U)))
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
    have h := integral_map measurable_axisRefl.aemeasurable hΞsm'
    rwa [gibbsMeasure_map_axisRefl μG ρ hρcont hN β] at h
  -- The two AE replacements of the transfer form's kernel
  -- pairing by `φ` and `χ` themselves.
  have h1 : ⇑(sliceState μG ρ β φ hφ) ∘ restrictConfig sliceLinks
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      φ ∘ restrictConfig sliceLinks :=
    ae_of_ae_map (measurable_restrictConfig sliceLinks).aemeasurable
      (p := fun z => ⇑(sliceState μG ρ β φ hφ) z = φ z) hφ.coeFn_toLp
  have h2 : ⇑(sliceState μG ρ β χ hχ) ∘ nextConfig hN2
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      χ ∘ nextConfig hN2 := by
    have hmap : (gibbsMeasure (torusShift N) μG ρ β).map
        (nextConfig hN2) = sliceMeasure (N := N) μG ρ β :=
      (measurePreserving_nextConfig μG ρ hN2 hρcont β).map_eq
    have hcoe : ⇑(sliceState μG ρ β χ hχ)
        =ᵐ[(gibbsMeasure (torusShift N) μG ρ β).map
          (nextConfig hN2)] χ := by
      rw [hmap]
      exact hχ.coeFn_toLp
    exact ae_of_ae_map (measurable_nextConfig hN2).aemeasurable
      (p := fun z => ⇑(sliceState μG ρ β χ hχ) z = χ z) hcoe
  calc osForm μG ρ β (fun U => φ (restrictConfig sliceLinks U))
          (fun U => χ (restrictConfig sliceLinks U))
      = ∫ U, reflObs (fun U => φ (restrictConfig sliceLinks U)) U
          * χ (restrictConfig sliceLinks U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) :=
        osForm_eq_integral μG ρ hρcont hd β _ _
    _ = ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
          * χ (restrictConfig sliceLinks (reflConfig U))
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        have h := integral_comp_reflConfig μG ρ hρcont hN β
          (fun U => reflObs (fun U => φ (restrictConfig sliceLinks U)) U
            * χ (restrictConfig sliceLinks U)) hΦsm
        rw [← h]
        apply integral_congr_ae
        filter_upwards with U
        show reflObs (fun U => φ (restrictConfig sliceLinks U))
            (reflConfig U)
            * χ (restrictConfig sliceLinks (reflConfig U))
          = (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
            * χ (restrictConfig sliceLinks (reflConfig U))
        rw [reflObs_reflConfig]
    _ = ∫ U, (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
          * χ (nextConfig hN2 U)
          ∂(gibbsMeasure (torusShift N) μG ρ β) := by
        rw [hsub]
        apply integral_congr_ae
        filter_upwards with U
        show (starRingEnd ℂ)
            (φ (restrictConfig sliceLinks (axisRefl U)))
            * χ (restrictConfig sliceLinks (reflConfig (axisRefl U)))
          = (starRingEnd ℂ) (φ (restrictConfig sliceLinks U))
            * χ (nextConfig hN2 U)
        rw [restrict_sliceLinks_axisRefl, restrict_sliceLinks_reflConfig,
          reflectedSliceReading_axisRefl hN2]
    _ = inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β
            (sliceState μG ρ β χ hχ)) := by
        rw [transferOp_inner μG ρ hN2 hρcont β
          (sliceState μG ρ β φ hφ) (sliceState μG ρ β χ hχ)]
        apply integral_congr_ae
        filter_upwards [h1, h2] with U h1U h2U
        simp only [Function.comp_apply] at h1U h2U
        rw [h1U, h2U]

end OSIdentification

section TwoPoint

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §3. The two-point operator -/

/-- **The depth-`m` leg:** pullback of a slice observable
along the depth-`m` reading, as a linear isometry
`osSpace β → L²(ν)` — the depth-`m` analogue of `slicePull`
(`m = 0`) and `nextPull` (`m = 1`, by `stepConfig_one`).
Measure-preservation of the reading is stationarity at
depth `m` (§1), so this leg needs `hρcont`. -/
noncomputable def stepPull
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) :
    osSpace (N := N) μG ρ β →ₗᵢ[ℂ]
      Lp ℂ 2 (gibbsMeasure (torusShift N) μG ρ β) where
  toFun := Lp.compMeasurePreserving
    (stepConfig (G := G) (N := N) m)
    (measurePreserving_stepConfig (N := N) μG ρ hρcont β m)
  map_add' := fun f g => map_add _ f g
  map_smul' := fun c f => by
    have hMP := measurePreserving_stepConfig (N := N) μG ρ
      hρcont β m
    have hsm : ⇑(c • f) ∘ stepConfig (G := G) (N := N) m
        =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
        (c • ⇑f) ∘ stepConfig (G := G) (N := N) m := by
      have h : ∀ᵐ y ∂((gibbsMeasure (torusShift N) μG ρ β).map
            (stepConfig (G := G) (N := N) m)),
          ⇑(c • f) y = (c • ⇑f) y := by
        rw [hMP.map_eq]
        exact Lp.coeFn_smul c f
      exact ae_of_ae_map (measurable_stepConfig m).aemeasurable h
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) hMP,
      Lp.coeFn_compMeasurePreserving f hMP,
      Lp.coeFn_smul c (Lp.compMeasurePreserving
        (stepConfig (G := G) (N := N) m) hMP f), hsm]
      with U h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply]
      at h1 h2 h3 h4 ⊢
    rw [h1, h4, h3, h2]
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (measurePreserving_stepConfig (N := N) μG ρ hρcont β m)

/-- The depth-`m` leg acts as composition with the
depth-`m` reading, almost everywhere. -/
theorem coeFn_stepPull
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) (f : osSpace (N := N) μG ρ β) :
    ⇑(stepPull μG ρ hρcont β m f)
      =ᵐ[gibbsMeasure (torusShift N) μG ρ β]
      ⇑f ∘ stepConfig (G := G) (N := N) m :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_stepConfig (N := N) μG ρ hρcont β m)

/-- The depth-`m` leg's continuous-linear-map presentation
acts as the isometry itself. -/
theorem stepPull_toCLM_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) (x : osSpace (N := N) μG ρ β) :
    (stepPull μG ρ hρcont β m).toContinuousLinearMap x
      = stepPull μG ρ hρcont β m x :=
  rfl

/-- **The two-point operator at separation `m`:**
`twoPointOp m = (slicePull)† ∘L stepPull m` on the OS
space — the operator whose sesquilinear form is the Gibbs
two-point pairing of the time-`0` reading against the
depth-`m` reading. At `m = 1` it is the transfer operator
(`twoPointOp_one`); the identification
`twoPointOp m = transferOp^m` for `m ≥ 2` is the registered
gap named in the header (the Markov/tower step), and is
**not** asserted here. -/
noncomputable def twoPointOp
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  ((slicePull μG ρ β).toContinuousLinearMap)†
    ∘L (stepPull μG ρ hρcont β m).toContinuousLinearMap

/-- The two-point operator applied:
`twoPointOp m f = (slicePull)† (stepPull m f)`. -/
theorem twoPointOp_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) (f : osSpace (N := N) μG ρ β) :
    twoPointOp μG ρ hρcont β m f
      = ContinuousLinearMap.adjoint
          (slicePull μG ρ β).toContinuousLinearMap
          (stepPull μG ρ hρcont β m f) :=
  rfl

/-- **The two-point form identity:** the form of
`twoPointOp m` is the two-slice Gibbs pairing at
separation `m` — the conjugate of the first observable
read on slice `0` against the second read at depth `m`.
At every real `β`, every `m`. The proof is
`transferOp_inner`'s, with the depth-`m` leg in place of
the next-slice leg. -/
theorem twoPointOp_inner
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (m : ℕ) (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (twoPointOp μG ρ hρcont β m f)
      = ∫ U, (starRingEnd ℂ)
          (⇑g (restrictConfig (G := G) sliceLinks U))
          * ⇑f (stepConfig m U)
        ∂(gibbsMeasure (torusShift N) μG ρ β) := by
  rw [twoPointOp_apply, ContinuousLinearMap.adjoint_inner_right,
    slicePull_toCLM_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_slicePull μG ρ β g,
    coeFn_stepPull μG ρ hρcont β m f] with U h1 h2
  rw [h1, h2]
  simp only [Function.comp_apply, RCLike.inner_apply,
    starRingEnd_apply]
  exact mul_comm _ _

/-- At depth `1` the depth leg is the next-slice leg:
the two pullbacks agree as linear isometries because the
depth-one reading **is** `nextConfig` (`stepConfig_one`). -/
theorem stepPull_one
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN2 : 2 ≤ N) (β : ℝ) :
    stepPull μG ρ hρcont β 1 = nextPull μG ρ hN2 hρcont β := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_stepPull μG ρ hρcont β 1 f,
    coeFn_nextPull μG ρ hN2 hρcont β f] with U h1 h2
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2, stepConfig_one hN2 U]

/-- **At separation one, the two-point operator is the
transfer operator** — on the nose, as continuous linear
maps, not merely at the level of forms. -/
theorem twoPointOp_one
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN2 : 2 ≤ N) (β : ℝ) :
    twoPointOp μG ρ hρcont β 1
      = transferOp μG ρ hN2 hρcont β := by
  show ((slicePull μG ρ β).toContinuousLinearMap)†
      ∘L (stepPull μG ρ hρcont β 1).toContinuousLinearMap
    = transferOp μG ρ hN2 hρcont β
  rw [stepPull_one μG ρ hρcont hN2 β]
  rfl

/-- **At separation zero, the two-point form is the OS
inner product itself**: the depth-`0` reading is the
time-`0` restriction (`stepConfig_zero`), and the slice
restriction is measure-preserving. Form-level only — at
the operator level `twoPointOp 0 = (slicePull)† ∘L
slicePull`, the compression of the identity pairing. -/
theorem twoPointOp_zero_inner
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (twoPointOp μG ρ hρcont β 0 f)
      = inner ℂ g f := by
  rw [twoPointOp_inner μG ρ hρcont β 0 g f]
  have hpt : ∀ U : Config (Fin 4 → ZMod N) G,
      (starRingEnd ℂ) (⇑g (restrictConfig (G := G) sliceLinks U))
          * ⇑f (stepConfig 0 U)
        = (starRingEnd ℂ) (⇑g (restrictConfig (G := G) sliceLinks U))
          * ⇑f (restrictConfig (G := G) sliceLinks U) :=
    fun U => by rw [stepConfig_zero]
  rw [integral_congr_ae (ae_of_all _ hpt)]
  have hcomp : (∫ U, (starRingEnd ℂ)
        (⇑g (restrictConfig (G := G) sliceLinks U))
        * ⇑f (restrictConfig (G := G) sliceLinks U)
      ∂(gibbsMeasure (torusShift N) μG ρ β))
      = ∫ z, (starRingEnd ℂ) (⇑g z) * ⇑f z
        ∂(sliceMeasure μG ρ β) := by
    have hHsm : AEStronglyMeasurable
        (fun z => (starRingEnd ℂ) (⇑g z) * ⇑f z)
        (sliceMeasure μG ρ β) :=
      ((RCLike.continuous_conj).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable g)).mul
        (Lp.aestronglyMeasurable f)
    have hH' : AEStronglyMeasurable
        (fun z => (starRingEnd ℂ) (⇑g z) * ⇑f z)
        ((gibbsMeasure (torusShift N) μG ρ β).map
          (restrictConfig (G := G) sliceLinks)) := by
      rwa [(measurePreserving_slicePull μG ρ β).map_eq]
    exact (integral_map
      (measurable_restrictConfig sliceLinks).aemeasurable
      hH').symm
  rw [hcomp]
  have hinner : ∀ z : ↥(sliceLinks (N := N)) → G,
      (starRingEnd ℂ) (⇑g z) * ⇑f z
        = inner ℂ (⇑g z) (⇑f z) :=
    fun z => by
      rw [RCLike.inner_apply]
      exact mul_comm _ _
  rw [integral_congr_ae (ae_of_all _ hinner),
    inner_osSpace μG ρ β g f]

end TwoPoint

end ThetLogos
