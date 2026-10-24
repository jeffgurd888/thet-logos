import ThetLogos.LatticeTransferIdent
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

open ComplexInnerProductSpace

/-!
# ThetLogos.LatticeTransferCompact — gap-queue item Q12:
spectral input on `T_β` at fixed volume

Charter: `whitepaper/gap-theorem-queue-2026-10-24.md`, item
Q12 (priced M–L, no kill named in source); source fence:
`whitepaper/pitch-4-stage-1b-d-2026-10-17.md`, fences item
(i) — at fixed `β > 0` and fixed volume, classically `T_β` is
shown compact (continuous kernel) and the gap is read off its
spectrum; neither compactness nor a spectral theorem for this
operator was formalized in this corpus. (Item (ii) of the
same fence — a gap uniform in volume and coupling — is Stage
3c / queue W1, a WALL, and is **out of scope** here: no
statement in this module is uniform in the volume, and no
continuum language appears.)

## What this module does

* **§1 — the kernel as a measure.** The transfer operator's
  quadratic form is a pairing against a single probability
  measure on the product slice space: the **two-slice law**
  `twoSliceMeasure`, the pushforward of the Gibbs measure
  under the two readings `(restr₀, nextConfig)`. Both of its
  marginals are the slice measure (landed stationarity), and
  `transferOp_inner_twoSlice` restates the landed form
  identity `transferOp_inner` as an integral over it. This is
  the kernel of `T_β` in the corpus's own terms: `T_β` is the
  integral operator of the two-slice Gibbs law.

* **§2 — abstract kernel operators.** For a kernel
  `K : X × X → ℂ` in `L²` of the product slice measure,
  `kernelOp K` is the integral operator
  `f ↦ (z ↦ ∫ z', K (z, z') f (z') ∂μ)`, built from partial
  integrals. Its form is the kernel pairing, and it obeys the
  Hilbert–Schmidt bound `‖kernelOp K‖ ≤ ‖K‖₂` — proved here
  from Cauchy–Schwarz and Tonelli, since Mathlib has no
  Hilbert–Schmidt API.

* **§3 — the density bridge.** If the two-slice law's pairing
  is given by an `L²` kernel `K` (hypothesis `HDen`, stated
  as a pairing identity), then `transferOp = kernelOp K`:
  the operators have the same form, hence agree. At `β = 0`
  `HDen` is discharged with the constant kernel `K ≡ 1` (the
  landed factorization `transferOp_zero_inner`).

* **§4 — compactness.** `kernelOp K` is compact for every
  `L²` kernel `K`: over any orthonormal basis `(bᵢ)` of the
  OS space, `Σᵢ ‖kernelOp K bᵢ‖² = ‖K‖²₂` (Parseval on the
  sections of `K`, then Tonelli), so the finite-rank partial
  sums converge to `kernelOp K` in operator norm, and
  compactness follows from Mathlib's
  `isCompactOperator_of_tendsto`. Consequently `T_β` is
  compact wherever `HDen` holds — in particular
  unconditionally at `β = 0`.

* **§5 — the spectral package and the gap.** From
  compactness and the landed self-adjointness (even `N`):
  every nonzero spectral point of `T_β` is an eigenvalue with
  finite-dimensional eigenspace; eigenvalues are real; the
  eigenvalues of modulus `≥ ε` are finite in number. The
  **gap** is then proved under the named positivity package
  **(H-PF)** (see the fences): **spectrum `T_β` ⊆ `{1} ∪`
  closed disc of radius `1 − δ`** for some `δ > 0`. At
  `β = 0` the gap is unconditional with `δ = 1` (spectrum
  `{0, 1}`, restating the landed exact gap spectrally).

## The fences (read before citing)

* **NO CLAIM on any part of any official Clay statement.**
  Parts closed by this module: **0**. Stage 1b-B label
  unchanged: positivity T1 for U(1) at all `β ≥ 0`; general
  `(G, ρ)` **OPEN**.
* **The positivity fence, named.** A gap with the vacuum as
  unique top eigenvector at general `(G, ρ)` needs
  positivity input that is OPEN (Stage 1b-B general). The
  gap theorem of §5 is therefore conditional on **(H-PF)**:
  (a) `T_β` is a positive operator (`0 ≤ ⟪f, T_β f⟫.re` for
  all `f` — the shape Stage 1b-B's `osForm` positivity would
  supply for the reconstructed transfer operator through the
  S1/R3 identifications), and (b) the vacuum eigenvalue is
  simple (`T_β v = v → v ∈ ℂ ∙ Ω`). Classically (a) and (b)
  are both outputs of pointwise strict positivity of the
  two-slice Gibbs kernel (Perron–Frobenius / Jentzsch); the
  corpus lands pointwise positivity only in the form version
  `transferOp_form_nonneg` (1b-D §7, slice observables), and
  the implication from there to (H-PF) is **not** formalized
  here — it is exactly where the gap stops at general
  `(G, ρ)`. Nothing in this module discharges (H-PF) at
  `β > 0`, at U(1) or anywhere else; the U(1) discharge would
  additionally need the S2-2 weld of `osForm` positivity to
  operator positivity on the whole OS space.
* **The density fence, named.** Compactness of `T_β` at
  general `β` is conditional on `HDen` (§3): the two-slice
  Gibbs law has an `L²` density kernel against the product
  of its marginals. Classically `HDen` holds with a
  continuous, strictly positive kernel (a fiber integral of
  the Gibbs weight); its formalization needs a disintegration
  of `configMeasure` over the link partition together with
  continuity and boundedness of `gibbsDensity` — outside
  this brick's ground (the landed 1b-D package), and named
  here as the remaining step rather than silently assumed
  for the Gibbs measure itself. What is proved
  unconditionally is: `HDen → IsCompactOperator T_β`, and
  `HDen` at `β = 0`.

This module is NOT in the root import list of the library
(the corpus pattern for recent exhibits); it is verified by a
targeted build.

- Status: brick Q12 — built 2026-10-24 under the gap queue;
  verdict PARTIAL (compactness conditional on `HDen` at
  general `β`, unconditional at `β = 0`; the general-`β` gap
  conditional on (H-PF), the `β = 0` gap unconditional);
  parent-verified 2026-10-24 (targeted build exit 0, strict
  recount, axiom check). Dossier:
  `whitepaper/transfer-q12-compact-partial-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section TwoSliceLaw

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The two-slice law -/

/-- **The two-slice law:** the pushforward of the Gibbs
measure under the two readings (time-`0` restriction,
next-slice reading) — a probability measure on the product
slice space. The transfer operator is the integral operator
of this law (§1's form identity). -/
noncomputable def twoSliceMeasure (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measure ((↥(sliceLinks (N := N)) → G)
      × (↥(sliceLinks (N := N)) → G)) :=
  (gibbsMeasure (torusShift N) μG ρ β).map
    (fun U => (restrictConfig (G := G) sliceLinks U,
      nextConfig hN2 U))

/-- The two readings are jointly measurable. -/
theorem measurable_twoSliceReading (hN2 : 2 ≤ N) :
    Measurable (fun U : Config (Fin 4 → ZMod N) G =>
      (restrictConfig (G := G) sliceLinks U, nextConfig hN2 U)) :=
  (measurable_restrictConfig sliceLinks).prodMk
    (measurable_nextConfig hN2)

/-- **First marginal:** the time-`0` marginal of the two-slice
law is the slice measure — landed stationarity
(`measurePreserving_slicePull`). -/
theorem twoSliceMeasure_map_fst (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    (twoSliceMeasure μG ρ hN2 hρcont β).map Prod.fst
      = sliceMeasure (N := N) μG ρ β := by
  show ((gibbsMeasure (torusShift N) μG ρ β).map _).map Prod.fst
    = sliceMeasure (N := N) μG ρ β
  rw [Measure.map_map measurable_fst
    (measurable_twoSliceReading (N := N) hN2)]
  exact (measurePreserving_slicePull (N := N) μG ρ β).map_eq

/-- **Second marginal:** the next-slice marginal of the
two-slice law is the slice measure — landed stationarity
(`measurePreserving_nextConfig`). -/
theorem twoSliceMeasure_map_snd (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    (twoSliceMeasure μG ρ hN2 hρcont β).map Prod.snd
      = sliceMeasure (N := N) μG ρ β := by
  show ((gibbsMeasure (torusShift N) μG ρ β).map _).map Prod.snd
    = sliceMeasure (N := N) μG ρ β
  rw [Measure.map_map measurable_snd
    (measurable_twoSliceReading (N := N) hN2)]
  exact (measurePreserving_nextConfig (N := N) μG ρ hN2
    hρcont β).map_eq

/-- The first projection is measure-preserving from the
two-slice law to the slice measure. -/
theorem measurePreserving_fst_twoSlice (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    MeasurePreserving Prod.fst (twoSliceMeasure μG ρ hN2 hρcont β)
      (sliceMeasure (N := N) μG ρ β) :=
  ⟨measurable_fst, twoSliceMeasure_map_fst μG ρ hN2 hρcont β⟩

/-- The second projection is measure-preserving from the
two-slice law to the slice measure. -/
theorem measurePreserving_snd_twoSlice (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    MeasurePreserving Prod.snd (twoSliceMeasure μG ρ hN2 hρcont β)
      (sliceMeasure (N := N) μG ρ β) :=
  ⟨measurable_snd, twoSliceMeasure_map_snd μG ρ hN2 hρcont β⟩

/-- **The form identity over the two-slice law:** the
quadratic form of the transfer operator is the pairing of
the two readings against the two-slice law. At every real
`β`. This is `transferOp_inner` (1b-D §5) with the integral
transported along the joint reading. -/
theorem transferOp_inner_twoSlice (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (transferOp μG ρ hN2 hρcont β f)
      = ∫ p, (starRingEnd ℂ) (⇑g p.1) * ⇑f p.2
          ∂(twoSliceMeasure μG ρ hN2 hρcont β) := by
  have hfst : AEStronglyMeasurable
      (fun p : (↥(sliceLinks (N := N)) → G)
        × (↥(sliceLinks (N := N)) → G) =>
        (starRingEnd ℂ) (⇑g p.1))
      (twoSliceMeasure μG ρ hN2 hρcont β) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (MeasureTheory.Lp.aestronglyMeasurable g)).comp_measurePreserving
        (measurePreserving_fst_twoSlice μG ρ hN2 hρcont β)
      |>.congr (Filter.Eventually.of_forall fun _ => rfl)
  have hsnd : AEStronglyMeasurable
      (fun p : (↥(sliceLinks (N := N)) → G)
        × (↥(sliceLinks (N := N)) → G) => ⇑f p.2)
      (twoSliceMeasure μG ρ hN2 hρcont β) :=
    (MeasureTheory.Lp.aestronglyMeasurable f).comp_measurePreserving
        (measurePreserving_snd_twoSlice μG ρ hN2 hρcont β)
      |>.congr (Filter.Eventually.of_forall fun _ => rfl)
  have hF : AEStronglyMeasurable
      (fun p : (↥(sliceLinks (N := N)) → G)
        × (↥(sliceLinks (N := N)) → G) =>
        (starRingEnd ℂ) (⇑g p.1) * ⇑f p.2)
      (twoSliceMeasure μG ρ hN2 hρcont β) :=
    (hfst.mul hsnd).congr (Filter.Eventually.of_forall
      fun _ => rfl)
  rw [transferOp_inner μG ρ hN2 hρcont β g f]
  symm
  show (∫ p, (starRingEnd ℂ) (⇑g p.1) * ⇑f p.2
      ∂((gibbsMeasure (torusShift N) μG ρ β).map
        (fun U => (restrictConfig (G := G) sliceLinks U,
          nextConfig hN2 U))))
    = ∫ U, (starRingEnd ℂ)
        (⇑g (restrictConfig (G := G) sliceLinks U))
          * ⇑f (nextConfig hN2 U)
        ∂(gibbsMeasure (torusShift N) μG ρ β)
  rw [integral_map (measurable_twoSliceReading (N := N)
    hN2).aemeasurable hF]

end TwoSliceLaw

/-! ## §2. Abstract kernel operators

Throughout, `μ` is the slice measure on the slice space
`X = (↥sliceLinks → G)` and `K : X × X → ℂ` is a kernel in
`L²(μ.prod μ)`. The operator `kernelOp K` is the partial
integral against `K`. Mathlib has no Hilbert–Schmidt API;
the bound `‖kernelOp K‖ ≤ ‖K‖₂` and the Parseval identity of
§4 are proved from Cauchy–Schwarz and Tonelli directly. -/

/-- The square of the `L²` seminorm is the Lebesgue integral
of the squared enorm. (Stated for an a.e.-strongly-measurable
function; the seminorm vanishes by convention otherwise.) -/
theorem eLpNorm_two_sq {α : Type*} {mα : MeasurableSpace α}
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (μ : Measure α)
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by simp) hf]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
  rw [h2]
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast]
  rw [one_div]
  exact ENNReal.rpow_inv_natCast_pow (show (2 : ℕ) ≠ 0 by norm_num) _

section KernelOp

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **Sections of an `L²` kernel are `L²`:** for a.e. slice
configuration `z`, the section `z' ↦ K (z, z')` is in
`L²` of the slice measure. -/
theorem memLp_section_ae (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hd : 0 < d)
    {K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ}
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      MemLp (fun z' => K (z, z')) 2 (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hfin : (∫⁻ p, ‖K p‖ₑ ^ 2
      ∂((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β))) ≠ ∞ := by
    have h := eLpNorm_two_sq
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β))
      hK.aestronglyMeasurable
    rw [← h]
    exact ENNReal.pow_ne_top (hK.eLpNorm_lt_top).ne
  have hAM : AEMeasurable (fun p => ‖K p‖ₑ ^ 2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
    simp only [pow_two]
    exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
      hK.aestronglyMeasurable.aemeasurable.enorm
  rw [MeasureTheory.lintegral_prod _ hAM] at hfin
  have hae : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      (∫⁻ z', ‖K (z, z')‖ₑ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
        < ∞ :=
    ae_lt_top' hAM.lintegral_prod_right' hfin
  filter_upwards [hK.aestronglyMeasurable.prodMk_left, hae]
    with z hz hsec
  show eLpNorm (fun z' => K (z, z')) 2
    (sliceMeasure (N := N) μG ρ β) < ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by simp) hz]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
  rw [h2]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  exact hsec.ne

/-- For an `L²` element, the integral of the squared norm of a
representative is the square of the norm. -/
theorem integral_norm_sq_lp {α : Type*} {mα : MeasurableSpace α}
    (μ : Measure α) (v : Lp ℂ 2 μ) :
    ∫ x, ‖⇑v x‖ ^ 2 ∂μ = ‖v‖ ^ 2 := by
  have hpt : ∀ y : ℂ, ENNReal.ofReal (‖y‖ ^ 2) = ‖y‖ₑ ^ 2 := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have hint : Integrable (fun x => ‖⇑v x‖ ^ 2) μ := by
    have h := (MeasureTheory.Lp.memLp v).integrable_norm_rpow (p := (2 : ℝ≥0∞))
      (by norm_num) (by simp)
    have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
    rw [h2] at h
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using h
  have hnn : 0 ≤ ∫ x, ‖⇑v x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by positivity)
  calc ∫ x, ‖⇑v x‖ ^ 2 ∂μ
      = (ENNReal.ofReal (∫ x, ‖⇑v x‖ ^ 2 ∂μ)).toReal := by
        rw [ENNReal.toReal_ofReal hnn]
    _ = (∫⁻ x, ‖⇑v x‖ₑ ^ 2 ∂μ).toReal := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => by positivity)]
        congr 1
        exact lintegral_congr_ae
          (Filter.Eventually.of_forall fun x => hpt (⇑v x))
    _ = ((eLpNorm (⇑v) 2 μ) ^ 2).toReal := by
        rw [eLpNorm_two_sq μ (MeasureTheory.Lp.aestronglyMeasurable v)]
    _ = ‖v‖ ^ 2 := by
        rw [ENNReal.toReal_pow, MeasureTheory.Lp.norm_def]

/-- The partial-integral function of the kernel operator:
`(kernelFun β K ⇑f) z = ∫ z', K (z, z') • f z'`. -/
noncomputable def kernelFun (β : ℝ)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (f : (↥(sliceLinks (N := N)) → G) → ℂ) :
    (↥(sliceLinks (N := N)) → G) → ℂ :=
  fun z => ∫ z', K (z, z') * f z' ∂(sliceMeasure (N := N) μG ρ β)

/-- **Sections of the kernel integrand are integrable:**
for a.e. `z`, the integrand `z' ↦ K (z, z') * f z'` of the
partial integral is integrable. -/
theorem integrable_kernelFun_integrand_ae (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    {K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ}
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace μG ρ β) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      Integrable (fun z' => K (z, z') * ⇑f z')
        (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  filter_upwards [memLp_section_ae μG ρ β hρcont hd hK] with z hz
  exact memLp_one_iff_integrable.mp
    (hz.mul (MeasureTheory.Lp.memLp f))

/-- **The partial integral of an `L²` kernel applied to an
`L²` function is `L²`**, with the Hilbert–Schmidt bound on
the seminorm (the operator bound `kernelOp_norm_le` is the
packaged form, proved via the form identity). -/
theorem memLp_kernelFun (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    {K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ}
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace μG ρ β) :
    MemLp (kernelFun μG ρ β K ⇑f) 2
      (sliceMeasure (N := N) μG ρ β) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hpt : ∀ y : ℂ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have haesm : AEStronglyMeasurable (kernelFun μG ρ β K ⇑f)
      (sliceMeasure (N := N) μG ρ β) := by
    have hH : AEStronglyMeasurable
        (fun p => K p * ⇑f p.2)
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) :=
      hK.aestronglyMeasurable.mul
        ((MeasureTheory.Lp.aestronglyMeasurable f).comp_snd)
    exact hH.integral_prod_right'
  have hbound : ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ‖kernelFun μG ρ β K ⇑f z‖ ^ 2
        ≤ (∫ z', ‖K (z, z')‖ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
          * ‖f‖ ^ 2 := by
    filter_upwards [memLp_section_ae μG ρ β hρcont hd hK] with z hz
    have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    have hKz : MemLp (fun z' => ‖K (z, z')‖) (ENNReal.ofReal 2)
        (sliceMeasure (N := N) μG ρ β) := by
      have h := hz.norm
      rw [← hof2] at h
      exact h
    have hf2 : MemLp (fun z' => ‖⇑f z'‖) (ENNReal.ofReal 2)
        (sliceMeasure (N := N) μG ρ β) := by
      show eLpNorm (fun z' => ‖⇑f z'‖) (ENNReal.ofReal 2)
        (sliceMeasure (N := N) μG ρ β) < ∞
      rw [hof2]
      exact (MeasureTheory.Lp.memLp f).norm
    have hcs : ∫ z', ‖K (z, z')‖ * ‖⇑f z'‖
          ∂(sliceMeasure (N := N) μG ρ β)
        ≤ (∫ z', ‖K (z, z')‖ ^ (2 : ℝ)
            ∂(sliceMeasure (N := N) μG ρ β)) ^ (1 / (2 : ℝ))
          * (∫ z', ‖⇑f z'‖ ^ (2 : ℝ)
            ∂(sliceMeasure (N := N) μG ρ β)) ^ (1 / (2 : ℝ)) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        ((Real.holderConjugate_iff (p := 2) (q := 2)).mpr
        ⟨by norm_num, by norm_num⟩)
        (Filter.Eventually.of_forall fun z' => norm_nonneg _)
        (Filter.Eventually.of_forall fun z' => norm_nonneg _) hKz hf2
    have hrw : ∀ (w : (↥(sliceLinks (N := N)) → G) → ℝ),
        (∫ z', w z' ^ (2 : ℝ) ∂(sliceMeasure (N := N) μG ρ β))
            ^ (1 / (2 : ℝ))
          = Real.sqrt (∫ z', w z' ^ 2
            ∂(sliceMeasure (N := N) μG ρ β)) := by
      intro w
      have e1 : (∫ z', w z' ^ (2 : ℝ)
            ∂(sliceMeasure (N := N) μG ρ β))
          = ∫ z', w z' ^ 2 ∂(sliceMeasure (N := N) μG ρ β) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z' => by
          simp only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
      rw [e1]
      exact (Real.sqrt_eq_rpow _).symm
    rw [hrw, hrw] at hcs
    have hnorm : ‖kernelFun μG ρ β K ⇑f z‖
        ≤ ∫ z', ‖K (z, z')‖ * ‖⇑f z'‖
          ∂(sliceMeasure (N := N) μG ρ β) := by
      calc ‖kernelFun μG ρ β K ⇑f z‖
          = ‖∫ z', K (z, z') * ⇑f z'
            ∂(sliceMeasure (N := N) μG ρ β)‖ := rfl
        _ ≤ ∫ z', ‖K (z, z') * ⇑f z'‖
            ∂(sliceMeasure (N := N) μG ρ β) :=
            norm_integral_le_integral_norm
              (fun z' => K (z, z') * ⇑f z')
        _ = ∫ z', ‖K (z, z')‖ * ‖⇑f z'‖
            ∂(sliceMeasure (N := N) μG ρ β) :=
            integral_congr_ae (Filter.Eventually.of_forall fun z' =>
              norm_mul _ _)
    have hsq : ‖kernelFun μG ρ β K ⇑f z‖ ^ 2
        ≤ (∫ z', ‖K (z, z')‖ * ‖⇑f z'‖
          ∂(sliceMeasure (N := N) μG ρ β)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    refine hsq.trans ?_
    calc (∫ z', ‖K (z, z')‖ * ‖⇑f z'‖
          ∂(sliceMeasure (N := N) μG ρ β)) ^ 2
        ≤ (Real.sqrt (∫ z', ‖K (z, z')‖ ^ 2
              ∂(sliceMeasure (N := N) μG ρ β))
            * Real.sqrt (∫ z', ‖⇑f z'‖ ^ 2
              ∂(sliceMeasure (N := N) μG ρ β))) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun z' =>
            mul_nonneg (norm_nonneg _) (norm_nonneg _))) hcs 2
      _ = (∫ z', ‖K (z, z')‖ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
            * ‖f‖ ^ 2 := by
          rw [mul_pow,
            Real.sq_sqrt (integral_nonneg_of_ae
              (Filter.Eventually.of_forall fun z' => by positivity)),
            Real.sq_sqrt (integral_nonneg_of_ae
              (Filter.Eventually.of_forall fun z' => by positivity)),
            integral_norm_sq_lp (sliceMeasure (N := N) μG ρ β) f]
  show eLpNorm (kernelFun μG ρ β K ⇑f) 2
    (sliceMeasure (N := N) μG ρ β) < ∞
  have hle : (eLpNorm (kernelFun μG ρ β K ⇑f) 2
        (sliceMeasure (N := N) μG ρ β)) ^ 2
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))) ^ 2
        * ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [eLpNorm_two_sq _ haesm]
    calc ∫⁻ z, ‖kernelFun μG ρ β K ⇑f z‖ₑ ^ 2
          ∂(sliceMeasure (N := N) μG ρ β)
        ≤ ∫⁻ z, ENNReal.ofReal
            ((∫ z', ‖K (z, z')‖ ^ 2
              ∂(sliceMeasure (N := N) μG ρ β)) * ‖f‖ ^ 2)
            ∂(sliceMeasure (N := N) μG ρ β) :=
          lintegral_mono_ae (hbound.mono fun z hz => by
            rw [hpt]
            exact ENNReal.ofReal_le_ofReal hz)
      _ = (∫⁻ z, ENNReal.ofReal
            (∫ z', ‖K (z, z')‖ ^ 2
              ∂(sliceMeasure (N := N) μG ρ β))
            ∂(sliceMeasure (N := N) μG ρ β))
          * ENNReal.ofReal (‖f‖ ^ 2) := by
          rw [← MeasureTheory.lintegral_mul_const'']
          · exact lintegral_congr_ae (Filter.Eventually.of_forall fun z =>
              ENNReal.ofReal_mul
                (integral_nonneg_of_ae
                  (Filter.Eventually.of_forall fun z' => by positivity)))
          · have hAM2 : AEMeasurable
                (fun z => ENNReal.ofReal
                  (∫ z', ‖K (z, z')‖ ^ 2
                    ∂(sliceMeasure (N := N) μG ρ β)))
                (sliceMeasure (N := N) μG ρ β) := by
              have hnorm2 : AEStronglyMeasurable
                  (fun p => ‖K p‖ ^ 2)
                  ((sliceMeasure (N := N) μG ρ β).prod
                    (sliceMeasure (N := N) μG ρ β)) :=
                (hK.aestronglyMeasurable.norm.mul
                  hK.aestronglyMeasurable.norm).congr
                  (Filter.Eventually.of_forall fun p =>
                    (pow_two ‖K p‖).symm)
              exact ENNReal.measurable_ofReal.comp_aemeasurable
                (hnorm2.integral_prod_right').aemeasurable
            exact hAM2
      _ = (∫⁻ p, ‖K p‖ₑ ^ 2
            ∂((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β)))
          * ENNReal.ofReal (‖f‖ ^ 2) := by
          congr 1
          have hAM : AEMeasurable (fun p => ‖K p‖ₑ ^ 2)
              ((sliceMeasure (N := N) μG ρ β).prod
                (sliceMeasure (N := N) μG ρ β)) := by
            simp only [pow_two]
            exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
              hK.aestronglyMeasurable.aemeasurable.enorm
          rw [MeasureTheory.lintegral_prod _ hAM]
          apply lintegral_congr_ae
          filter_upwards [memLp_section_ae μG ρ β hρcont hd hK]
            with z hz
          have hintz : Integrable (fun z' => ‖K (z, z')‖ ^ 2)
              (sliceMeasure (N := N) μG ρ β) := by
            have h := hz.integrable_norm_rpow (p := (2 : ℝ≥0∞))
              (by norm_num) (by simp)
            have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
            rw [h2] at h
            simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast] using h
          rw [ofReal_integral_eq_lintegral_ofReal hintz
            (Filter.Eventually.of_forall fun z' => by positivity)]
          exact lintegral_congr_ae (Filter.Eventually.of_forall fun z' =>
            (hpt (K (z, z'))).symm)
      _ = (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))) ^ 2
          * ENNReal.ofReal (‖f‖ ^ 2) := by
          rw [eLpNorm_two_sq _ hK.aestronglyMeasurable]
  have hfin2 : (eLpNorm (kernelFun μG ρ β K ⇑f) 2
        (sliceMeasure (N := N) μG ρ β)) ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top hK.ne)
        ENNReal.ofReal_lt_top.ne) hle
  by_contra htop
  push_neg at htop
  have hEq : eLpNorm (kernelFun μG ρ β K ⇑f) 2
      (sliceMeasure (N := N) μG ρ β) = ∞ := le_antisymm le_top htop
  rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfin2
  exact hfin2 rfl

/-- **Squared seminorm of a tensor kernel factor:**
for `V p = conj (g p.1) * f p.2` on the product slice space,
`(eLpNorm V 2)²` is the product of the squared seminorms —
the tensor factor separates under Tonelli. -/
theorem eLpNorm_tensor_sq (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (g f : osSpace μG ρ β) :
    (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))) ^ 2
      = ((eLpNorm (⇑g) 2 (sliceMeasure (N := N) μG ρ β))
        * (eLpNorm (⇑f) 2 (sliceMeasure (N := N) μG ρ β))) ^ 2 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hpt : ∀ y : ℂ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have hgA : AEStronglyMeasurable (⇑g)
      (sliceMeasure (N := N) μG ρ β) :=
    MeasureTheory.Lp.aestronglyMeasurable g
  have hfA : AEStronglyMeasurable (⇑f)
      (sliceMeasure (N := N) μG ρ β) :=
    MeasureTheory.Lp.aestronglyMeasurable f
  have hV : AEStronglyMeasurable
      (fun p => star (⇑g p.1) * ⇑f p.2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    (continuous_star.comp_aestronglyMeasurable hgA.comp_fst).mul
      hfA.comp_snd
  rw [eLpNorm_two_sq _ hV, mul_pow, eLpNorm_two_sq _ hgA,
    eLpNorm_two_sq _ hfA]
  have hAM : AEMeasurable
      (fun p => ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    ((hgA.aemeasurable.comp_fst).enorm.pow_const 2).mul
      ((hfA.aemeasurable.comp_snd).enorm.pow_const 2)
  calc ∫⁻ p, ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))
      = ∫⁻ p, ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
          show ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2
            = ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2
          rw [hpt, hpt (⇑g p.1), hpt (⇑f p.2), ← ENNReal.ofReal_mul
            (by positivity)]
          congr 1
          rw [norm_mul, norm_star, mul_pow])
    _ = (∫⁻ z, ‖⇑g z‖ₑ ^ 2 ∂(sliceMeasure (N := N) μG ρ β))
        * (∫⁻ z', ‖⇑f z'‖ₑ ^ 2
          ∂(sliceMeasure (N := N) μG ρ β)) := by
        rw [MeasureTheory.lintegral_prod _ hAM]
        exact MeasureTheory.lintegral_lintegral_mul
          (hgA.aemeasurable.enorm.pow_const 2)
          (hfA.aemeasurable.enorm.pow_const 2)

/-- Tensor factors are `L²` on the product slice space. -/
theorem memLp_tensor (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (g f : osSpace μG ρ β) :
    MemLp (fun p => star (⇑g p.1) * ⇑f p.2) 2
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hsq := eLpNorm_tensor_sq μG ρ β hρcont hd g f
  show eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
    ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)) < ∞
  by_contra htop
  push Not at htop
  have hEq : eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) = ∞ :=
    le_antisymm le_top htop
  rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  have hfin : ((eLpNorm (⇑g) 2 (sliceMeasure (N := N) μG ρ β))
      * (eLpNorm (⇑f) 2 (sliceMeasure (N := N) μG ρ β))) ^ 2
      ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top
      (MeasureTheory.Lp.memLp g).ne (MeasureTheory.Lp.memLp f).ne)
  exact hfin hsq.symm

/-- The `L²` seminorm of a tensor factor, in real form:
`(eLpNorm V 2).toReal = ‖g‖ * ‖f‖`. -/
theorem eLpNorm_tensor_toReal (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (g f : osSpace μG ρ β) :
    (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal
      = ‖g‖ * ‖f‖ := by
  have hsq := eLpNorm_tensor_sq μG ρ β hρcont hd g f
  have h1 : ((eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal) ^ 2
      = (‖g‖ * ‖f‖) ^ 2 := by
    have h2 : ((eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
          ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))) ^ 2).toReal
        = (((eLpNorm (⇑g) 2 (sliceMeasure (N := N) μG ρ β))
          * (eLpNorm (⇑f) 2 (sliceMeasure (N := N) μG ρ β)))
          ^ 2).toReal := congrArg ENNReal.toReal hsq
    rw [ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_mul,
      ← MeasureTheory.Lp.norm_def, ← MeasureTheory.Lp.norm_def] at h2
    exact h2
  have h := (sq_eq_sq₀ (ENNReal.toReal_nonneg)
    (mul_nonneg (norm_nonneg g) (norm_nonneg f))).mp h1
  exact h

/-- **Additivity of the partial integral** in the `L²`
argument, a.e. on the slice space. -/
theorem kernelFun_add_ae (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    {K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ}
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f g : osSpace (N := N) μG ρ β) :
    kernelFun μG ρ β K ⇑(f + g)
      =ᵐ[sliceMeasure (N := N) μG ρ β]
        kernelFun μG ρ β K ⇑f + kernelFun μG ρ β K ⇑g := by
  filter_upwards [integrable_kernelFun_integrand_ae μG ρ β hρcont
      hd hK f, integrable_kernelFun_integrand_ae μG ρ β hρcont hd
      hK g] with z hfz hgz
  have hcoe : ⇑(f + g) =ᵐ[sliceMeasure (N := N) μG ρ β] ⇑f + ⇑g :=
    MeasureTheory.Lp.coeFn_add f g
  show (∫ z', K (z, z') * ⇑(f + g) z'
      ∂(sliceMeasure (N := N) μG ρ β))
    = (∫ z', K (z, z') * ⇑f z' ∂(sliceMeasure (N := N) μG ρ β))
      + (∫ z', K (z, z') * ⇑g z'
        ∂(sliceMeasure (N := N) μG ρ β))
  have e1 : (∫ z', K (z, z') * ⇑(f + g) z'
        ∂(sliceMeasure (N := N) μG ρ β))
      = ∫ z', (K (z, z') * ⇑f z' + K (z, z') * ⇑g z')
        ∂(sliceMeasure (N := N) μG ρ β) := by
    apply integral_congr_ae
    filter_upwards [hcoe] with z' hz'
    rw [hz', Pi.add_apply, mul_add]
  rw [e1, integral_add hfz hgz]

/-- **Homogeneity of the partial integral** in the `L²`
argument, a.e. on the slice space. -/
theorem kernelFun_smul_ae (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    {K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ}
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (c : ℂ) (f : osSpace (N := N) μG ρ β) :
    kernelFun μG ρ β K ⇑(c • f)
      =ᵐ[sliceMeasure (N := N) μG ρ β]
        c • kernelFun μG ρ β K ⇑f := by
  have hcoe : ⇑(c • f) =ᵐ[sliceMeasure (N := N) μG ρ β] c • ⇑f :=
    MeasureTheory.Lp.coeFn_smul c f
  apply Filter.Eventually.of_forall
  intro z
  show (∫ z', K (z, z') * ⇑(c • f) z'
      ∂(sliceMeasure (N := N) μG ρ β))
    = c • (∫ z', K (z, z') * ⇑f z'
      ∂(sliceMeasure (N := N) μG ρ β))
  have e1 : (∫ z', K (z, z') * ⇑(c • f) z'
        ∂(sliceMeasure (N := N) μG ρ β))
      = ∫ z', c * (K (z, z') * ⇑f z')
        ∂(sliceMeasure (N := N) μG ρ β) := by
    apply integral_congr_ae
    filter_upwards [hcoe] with z' hz'
    rw [hz', Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, integral_const_mul, smul_eq_mul]

/-- The `L²` element of the partial integral. -/
noncomputable def kernelRep (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) : osSpace (N := N) μG ρ β :=
  (memLp_kernelFun μG ρ β hρcont hd hK f).toLp
    (kernelFun μG ρ β K ⇑f)

/-- Representatives of `kernelRep` are the partial integrals. -/
theorem coeFn_kernelRep (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) :
    ⇑(kernelRep μG ρ β hρcont hd K hK f)
      =ᵐ[sliceMeasure (N := N) μG ρ β] kernelFun μG ρ β K ⇑f :=
  MemLp.coeFn_toLp _

/-- **The kernel operator as a linear map** on the OS space:
`kernelLinMap K f` is the partial integral against `K`. -/
noncomputable def kernelLinMap (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))) :
    osSpace (N := N) μG ρ β →ₗ[ℂ] osSpace (N := N) μG ρ β where
  toFun f := kernelRep μG ρ β hρcont hd K hK f
  map_add' f g := by
    rw [MeasureTheory.Lp.ext_iff]
    calc ⇑(kernelRep μG ρ β hρcont hd K hK (f + g))
        =ᵐ[sliceMeasure (N := N) μG ρ β] kernelFun μG ρ β K ⇑(f + g) :=
          coeFn_kernelRep μG ρ β hρcont hd K hK (f + g)
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          kernelFun μG ρ β K ⇑f + kernelFun μG ρ β K ⇑g :=
          kernelFun_add_ae μG ρ β hρcont hd hK f g
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          ⇑(kernelRep μG ρ β hρcont hd K hK f)
            + ⇑(kernelRep μG ρ β hρcont hd K hK g) :=
          (coeFn_kernelRep μG ρ β hρcont hd K hK f).symm.add
            (coeFn_kernelRep μG ρ β hρcont hd K hK g).symm
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          ⇑(kernelRep μG ρ β hρcont hd K hK f
            + kernelRep μG ρ β hρcont hd K hK g) :=
          (MeasureTheory.Lp.coeFn_add _ _).symm
  map_smul' c f := by
    rw [MeasureTheory.Lp.ext_iff]
    calc ⇑(kernelRep μG ρ β hρcont hd K hK (c • f))
        =ᵐ[sliceMeasure (N := N) μG ρ β] kernelFun μG ρ β K ⇑(c • f) :=
          coeFn_kernelRep μG ρ β hρcont hd K hK (c • f)
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          c • kernelFun μG ρ β K ⇑f :=
          kernelFun_smul_ae μG ρ β hρcont hd hK c f
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          c • ⇑(kernelRep μG ρ β hρcont hd K hK f) :=
          (coeFn_kernelRep μG ρ β hρcont hd K hK f).symm.const_smul c
      _ =ᵐ[sliceMeasure (N := N) μG ρ β]
          ⇑(c • kernelRep μG ρ β hρcont hd K hK f) :=
          (MeasureTheory.Lp.coeFn_smul c _).symm

/-- Representatives of `kernelLinMap K f` are the partial
integrals. -/
theorem coeFn_kernelLinMap (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) :
    ⇑(kernelLinMap μG ρ β hρcont hd K hK f)
      =ᵐ[sliceMeasure (N := N) μG ρ β] kernelFun μG ρ β K ⇑f :=
  coeFn_kernelRep μG ρ β hρcont hd K hK f

/-- Integrability of the kernel pairing integrand
`p ↦ star (g p.1) * (K p * f p.2)` on the product slice space:
it is the product of the kernel with a tensor factor. -/
theorem integrable_kernel_pairing (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (g f : osSpace (N := N) μG ρ β) :
    Integrable (fun p => star (⇑g p.1) * (K p * ⇑f p.2))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have h1 : Integrable (K * (fun p => star (⇑g p.1) * ⇑f p.2))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    memLp_one_iff_integrable.mp
      (hK.mul (memLp_tensor μG ρ β hρcont hd g f))
  refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.mul_apply]
  ring

/-- **The form of the kernel operator is the kernel pairing:**
`⟪g, kernelOp K f⟫ = ∫∫ star (g z) * K (z, z') * f z'`. -/
theorem kernelLinMap_inner (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (g f : osSpace (N := N) μG ρ β) :
    inner ℂ g (kernelLinMap μG ρ β hρcont hd K hK f)
      = ∫ p, star (⇑g p.1) * (K p * ⇑f p.2)
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have h1 : inner ℂ g (kernelLinMap μG ρ β hρcont hd K hK f)
      = ∫ z, star (⇑g z) * kernelFun μG ρ β K ⇑f z
        ∂(sliceMeasure (N := N) μG ρ β) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_kernelLinMap μG ρ β hρcont hd K hK f]
      with z hz
    rw [hz, RCLike.inner_apply]
    show kernelFun μG ρ β K ⇑f z * (starRingEnd ℂ) (⇑g z)
      = star (⇑g z) * kernelFun μG ρ β K ⇑f z
    rw [starRingEnd_apply, mul_comm]
  have h2 : (∫ z, star (⇑g z) * kernelFun μG ρ β K ⇑f z
        ∂(sliceMeasure (N := N) μG ρ β))
      = ∫ z, ∫ z', star (⇑g z) * (K (z, z') * ⇑f z')
        ∂(sliceMeasure (N := N) μG ρ β)
        ∂(sliceMeasure (N := N) μG ρ β) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    exact (integral_const_mul (star (⇑g z))
      (fun z' => K (z, z') * ⇑f z')).symm
  rw [h1, h2]
  exact MeasureTheory.integral_integral
    (integrable_kernel_pairing μG ρ β hρcont hd K hK g f)

/-- **Cauchy–Schwarz bound for the kernel form:**
`|⟪g, kernelOp K f⟫| ≤ ‖K‖₂ ‖g‖ ‖f‖`, where `‖K‖₂` is the
real `L²` norm of the kernel on the product slice space. -/
theorem kernelLinMap_inner_abs_le (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (g f : osSpace (N := N) μG ρ β) :
    ‖inner ℂ g (kernelLinMap μG ρ β hρcont hd K hK f)‖
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal * ‖g‖ * ‖f‖ := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hΦint : Integrable
      (fun p => star (⇑g p.1) * (K p * ⇑f p.2))
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    integrable_kernel_pairing μG ρ β hρcont hd K hK g f
  have hV : AEStronglyMeasurable
      (fun p => star (⇑g p.1) * ⇑f p.2)
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)) :=
    (continuous_star.comp_aestronglyMeasurable
      (MeasureTheory.Lp.aestronglyMeasurable g).comp_fst).mul
      (MeasureTheory.Lp.aestronglyMeasurable f).comp_snd
  have key : ENNReal.ofReal
        (∫ p, ‖star (⇑g p.1) * (K p * ⇑f p.2)‖
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)))
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))
        * (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
          ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hΦint]
    have hpt : ∀ p, ‖star (⇑g p.1) * (K p * ⇑f p.2)‖ₑ
        = ‖K p‖ₑ * ‖star (⇑g p.1) * ⇑f p.2‖ₑ := by
      intro p
      have e : star (⇑g p.1) * (K p * ⇑f p.2)
          = K p * (star (⇑g p.1) * ⇑f p.2) := by ring
      rw [e, enorm_mul]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
      ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β))
      ((Real.holderConjugate_iff (p := 2) (q := 2)).mpr
        ⟨by norm_num, by norm_num⟩)
      (hK.aestronglyMeasurable.aemeasurable.enorm)
      (hV.aemeasurable.enorm)
    refine hH.trans ?_
    have h2r : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by simp) hK.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by simp) hV, h2r]
  have hfin : ENNReal.ofReal
        (∫ p, ‖star (⇑g p.1) * (K p * ⇑f p.2)‖
          ∂((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)))
      ≤ ENNReal.ofReal
        ((eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))).toReal
          * (‖g‖ * ‖f‖)) := by
    refine key.trans_eq ?_
    have eK : (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))
        = ENNReal.ofReal
          (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))).toReal :=
      (ENNReal.ofReal_toReal hK.ne).symm
    have eV : (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
          ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β)))
        = ENNReal.ofReal
          (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
            ((sliceMeasure (N := N) μG ρ β).prod
              (sliceMeasure (N := N) μG ρ β))).toReal :=
      (ENNReal.ofReal_toReal
        (memLp_tensor μG ρ β hρcont hd g f).ne).symm
    nth_rewrite 1 [eK]
    rw [eV, eLpNorm_tensor_toReal μG ρ β hρcont hd g f]
    exact (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  have hle : (∫ p, ‖star (⇑g p.1) * (K p * ⇑f p.2)‖
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal
        * (‖g‖ * ‖f‖) :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (norm_nonneg g) (norm_nonneg f)))).mp hfin
  calc ‖inner ℂ g (kernelLinMap μG ρ β hρcont hd K hK f)‖
      = ‖∫ p, star (⇑g p.1) * (K p * ⇑f p.2)
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))‖ := by
        rw [kernelLinMap_inner]
    _ ≤ ∫ p, ‖star (⇑g p.1) * (K p * ⇑f p.2)‖
        ∂((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) :=
        norm_integral_le_integral_norm _
    _ ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal
        * (‖g‖ * ‖f‖) := hle
    _ = (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal * ‖g‖ * ‖f‖ := by
        rw [mul_assoc]

/-- **The Hilbert–Schmidt bound:** the kernel operator's
norm is at most the `L²` norm of its kernel. (Proved from
the form bound with `g := S f`; no Hilbert–Schmidt API
exists in Mathlib, so the identity `Σᵢ ‖S bᵢ‖² = ‖K‖²` is
replaced here by the form argument — the Parseval identity
for `S` itself is proved in §4 where compactness needs it.) -/
theorem kernelLinMap_norm_le (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) :
    ‖kernelLinMap μG ρ β hρcont hd K hK f‖
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal * ‖f‖ := by
  by_cases hf0 : kernelLinMap μG ρ β hρcont hd K hK f = 0
  · rw [hf0]
    simp [mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f)]
  have hpos : 0 < ‖kernelLinMap μG ρ β hρcont hd K hK f‖ :=
    norm_pos_iff.mpr hf0
  have hsq : ‖kernelLinMap μG ρ β hρcont hd K hK f‖
        * ‖kernelLinMap μG ρ β hρcont hd K hK f‖
      ≤ ((eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))).toReal * ‖f‖)
        * ‖kernelLinMap μG ρ β hρcont hd K hK f‖ := by
    have e1 : ‖kernelLinMap μG ρ β hρcont hd K hK f‖
          * ‖kernelLinMap μG ρ β hρcont hd K hK f‖
        = (inner ℂ (kernelLinMap μG ρ β hρcont hd K hK f)
            (kernelLinMap μG ρ β hρcont hd K hK f)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    rw [e1]
    refine (le_trans (le_abs_self _)
      (Complex.abs_re_le_norm _)).trans ?_
    have h := kernelLinMap_inner_abs_le μG ρ β hρcont hd K hK
      (kernelLinMap μG ρ β hρcont hd K hK f) f
    have e2 : (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal
        * ‖kernelLinMap μG ρ β hρcont hd K hK f‖ * ‖f‖
        = ((eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
            (sliceMeasure (N := N) μG ρ β))).toReal * ‖f‖)
          * ‖kernelLinMap μG ρ β hρcont hd K hK f‖ := by ring
    rw [e2] at h
    exact h
  exact le_of_mul_le_mul_right hsq hpos

/-- **The kernel operator** on the OS space, as a continuous
linear map: `kernelOp K f` is the partial integral
`z ↦ ∫ z', K (z, z') f z'`. -/
noncomputable def kernelOp (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  (kernelLinMap μG ρ β hρcont hd K hK).mkContinuous
    (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))).toReal
    (fun f => kernelLinMap_norm_le μG ρ β hρcont hd K hK f)

theorem kernelOp_apply (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) :
    kernelOp μG ρ β hρcont hd K hK f
      = kernelLinMap μG ρ β hρcont hd K hK f :=
  rfl

/-- The Hilbert–Schmidt bound for `kernelOp`, pointwise. -/
theorem kernelOp_apply_norm_le (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    (f : osSpace (N := N) μG ρ β) :
    ‖kernelOp μG ρ β hρcont hd K hK f‖
      ≤ (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal * ‖f‖ := by
  rw [kernelOp_apply]
  exact kernelLinMap_norm_le μG ρ β hρcont hd K hK f

end KernelOp

/-! ## §3. The density bridge (HDen)

The kernel of stage (a) in corpus terms is the two-slice
law of §1: the pairing `⟪g, T_β f⟫` is the integral of
`star (g z) * f z'` against the joint law of
`(restrictConfig sliceLinks, nextConfig)`. A kernel
operator represents `T_β` exactly when that joint law is
given by an `L²` density `K` with respect to the product
of its marginals (the slice measures). That assertion is
the hypothesis **(HDen)** below, stated as a form
identity. Its proof at general `(G, ρ)` needs the
disintegration of the Gibbs measure over the two-slice
reading together with `L²`-boundedness of the density —
**outside this brick's ground** (the corpus lands the
Gibbs density's continuity in the configuration variables,
not a slice-density bound); it is discharged here at
`β = 0`, where both pairings factorize. -/

section DensityBridge

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **(HDen) — the form-density hypothesis at coupling `β`:**
there is an `L²` kernel `K` on the product of the slice
measures whose kernel operator has the same form as the
transfer operator `T_β`. By §1 (`transferOp_inner_twoSlice`)
the transfer form is the two-slice pairing, so (HDen) is
the assertion that the two-slice law has an `L²` density
with respect to the product of its marginals. -/
def HDen (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    Prop :=
  ∃ K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ,
    ∃ hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β)),
    ∀ g f : osSpace (N := N) μG ρ β,
      inner ℂ g (kernelLinMap μG ρ β hρcont hd K hK f)
        = inner ℂ g (transferOp μG ρ hN2 hρcont β f)

/-- **The bridge:** under (HDen), the transfer operator is
a kernel operator. -/
theorem transferOp_eq_kernelOp_of_HDen (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (h : HDen μG ρ β hN2 hρcont hd) :
    ∃ (K : (↥(sliceLinks (N := N)) → G)
        × (↥(sliceLinks (N := N)) → G) → ℂ)
      (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
        (sliceMeasure (N := N) μG ρ β))),
      transferOp μG ρ hN2 hρcont β
        = kernelOp μG ρ β hρcont hd K hK := by
  obtain ⟨K, hK, hpair⟩ := h
  refine ⟨K, hK, ContinuousLinearMap.ext fun f => ?_⟩
  apply eq_of_forall_inner_left μG ρ β
  intro g
  rw [kernelOp_apply]
  exact (hpair g f).symm

/-- **(HDen) holds at `β = 0`**, with the constant kernel
`K ≡ 1`: at zero coupling both pairings factorize as
`(∫ star g) * (∫ f)` — the kernel side by Tonelli, the
transfer side by the landed `transferOp_zero_inner`. -/
theorem hden_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    HDen μG ρ 0 hN2 hρcont hd := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd 0
  refine ⟨fun _ => 1, memLp_const 1, fun g f => ?_⟩
  have hΦint : Integrable (fun p => star (⇑g p.1) * ⇑f p.2)
      ((sliceMeasure (N := N) μG ρ 0).prod
        (sliceMeasure (N := N) μG ρ 0)) := by
    refine ⟨?_, ?_⟩
    · exact (continuous_star.comp_aestronglyMeasurable
        (MeasureTheory.Lp.aestronglyMeasurable g).comp_fst).mul
        (MeasureTheory.Lp.aestronglyMeasurable f).comp_snd
    · show (∫⁻ p, ‖star (⇑g p.1) * ⇑f p.2‖ₑ
        ∂((sliceMeasure (N := N) μG ρ 0).prod
          (sliceMeasure (N := N) μG ρ 0))) < ∞
      have hpt : ∀ (p : (↥(sliceLinks (N := N)) → G)
          × (↥(sliceLinks (N := N)) → G)),
          ‖star (⇑g p.1) * ⇑f p.2‖ₑ
          = ‖⇑g p.1‖ₑ * ‖⇑f p.2‖ₑ := by
        intro p
        rw [enorm_mul]
        congr 1
        simp [enorm]
      have hAM : AEMeasurable
          (fun p => ‖⇑g p.1‖ₑ * ‖⇑f p.2‖ₑ)
          ((sliceMeasure (N := N) μG ρ 0).prod
            (sliceMeasure (N := N) μG ρ 0)) :=
        ((MeasureTheory.Lp.aestronglyMeasurable g).aemeasurable.comp_fst.enorm).mul
          ((MeasureTheory.Lp.aestronglyMeasurable f).aemeasurable.comp_snd.enorm)
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
        MeasureTheory.lintegral_prod _ hAM,
        MeasureTheory.lintegral_lintegral_mul
          ((MeasureTheory.Lp.aestronglyMeasurable g).aemeasurable.enorm)
          ((MeasureTheory.Lp.aestronglyMeasurable f).aemeasurable.enorm),
        ← eLpNorm_one_eq_lintegral_enorm
          (MeasureTheory.Lp.aestronglyMeasurable g),
        ← eLpNorm_one_eq_lintegral_enorm
          (MeasureTheory.Lp.aestronglyMeasurable f)]
      exact ENNReal.mul_lt_top
        ((MeasureTheory.Lp.memLp g).mono_exponent (by norm_num))
        ((MeasureTheory.Lp.memLp f).mono_exponent (by norm_num))
  have hL : inner ℂ g (kernelLinMap μG ρ 0 hρcont hd (fun _ => 1)
        (memLp_const 1) f)
      = (∫ z, star (⇑g z) ∂(sliceMeasure (N := N) μG ρ 0))
        * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)) := by
    rw [kernelLinMap_inner]
    have e : (∫ p, star (⇑g p.1) * ((fun _ => (1 : ℂ)) p * ⇑f p.2)
          ∂((sliceMeasure (N := N) μG ρ 0).prod
            (sliceMeasure (N := N) μG ρ 0)))
        = ∫ p, star (⇑g p.1) * ⇑f p.2
          ∂((sliceMeasure (N := N) μG ρ 0).prod
            (sliceMeasure (N := N) μG ρ 0)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp)
    rw [e, MeasureTheory.integral_prod _ hΦint]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
      integral_const_mul (star (⇑g z)) ⇑f)]
    exact integral_mul_const _ _
  have hR : inner ℂ g (transferOp μG ρ hN2 hρcont 0 f)
      = (∫ z, star (⇑g z) ∂(sliceMeasure (N := N) μG ρ 0))
        * (∫ z, ⇑f z ∂(sliceMeasure (N := N) μG ρ 0)) := by
    rw [transferOp_zero_inner μG ρ hN2 hρcont hd f g,
      show (∫ z, (starRingEnd ℂ) (⇑g z)
          ∂(sliceMeasure (N := N) μG ρ 0))
        = ∫ z, star (⇑g z) ∂(sliceMeasure (N := N) μG ρ 0) from
        integral_congr_ae (Filter.Eventually.of_forall fun z =>
          starRingEnd_apply (⇑g z))]
  rw [hL, hR]

end DensityBridge

/-! ## §4. Compactness of the kernel operator

No Hilbert–Schmidt API exists in this Mathlib, so the Hilbert–Schmidt
argument is hand-built: a Parseval identity for an arbitrary Hilbert
basis (real `tsum` form), the pointwise Hilbert–Schmidt identity for
the kernel's sections (a.e. in the first variable), the total identity
`∑' i, ‖S bᵢ‖² = ‖K‖²₂`, and finite-rank approximation of `S` by `S`
composed with the finite basis projections. The conclusion:
`kernelOp K` is compact for EVERY square-integrable kernel `K` — no
positivity anywhere. -/

/-- Summability of the squared Fourier coefficients of a vector in a
Hilbert basis. -/
theorem summable_inner_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*}
    (b : HilbertBasis ι ℂ E) (v : E) :
    Summable (fun i => ‖⟪b i, v⟫‖^2) := by
  have hfam : ∀ i, ⟪v, b i⟫ * ⟪b i, v⟫
      = ((‖⟪b i, v⟫‖^2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm]
    exact_mod_cast RCLike.conj_mul (⟪b i, v⟫ : ℂ)
  have hH : HasSum (fun i => ((‖⟪b i, v⟫‖^2 : ℝ) : ℂ)) ⟪v, v⟫ := by
    simpa only [hfam] using b.hasSum_inner_mul_inner v v
  exact Complex.summable_ofReal.mp hH.summable

/-- Parseval's identity for a Hilbert basis, as a real `tsum`. -/
theorem parseval_tsum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*}
    (b : HilbertBasis ι ℂ E) (v : E) :
    ∑' i, ‖⟪b i, v⟫‖^2 = ‖v‖^2 := by
  have hfam : ∀ i, ⟪v, b i⟫ * ⟪b i, v⟫
      = ((‖⟪b i, v⟫‖^2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm]
    exact_mod_cast RCLike.conj_mul (⟪b i, v⟫ : ℂ)
  have hH : HasSum (fun i => ((‖⟪b i, v⟫‖^2 : ℝ) : ℂ)) ⟪v, v⟫ := by
    simpa only [hfam] using b.hasSum_inner_mul_inner v v
  have key : ((∑' i, ‖⟪b i, v⟫‖^2 : ℝ) : ℂ) = ((‖v‖^2 : ℝ) : ℂ) := by
    have h2 : ((∑' i, ‖⟪b i, v⟫‖^2 : ℝ) : ℂ) = ⟪v, v⟫ := by
      rw [Complex.ofReal_tsum]
      exact hH.tsum_eq
    rw [h2]
    exact_mod_cast inner_self_eq_norm_sq_to_K v
  exact_mod_cast key

section Compactness

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] {ι : Type*} [Countable ι]

/-- The pointwise Hilbert–Schmidt identity: for a.e. first variable
`z`, the squared Fourier coefficients of the kernel operator's values
on basis vectors sum to the squared `L²` norm of the kernel's
section at `z`. -/
theorem hs_identity_ae (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      ∀ _hz : MemLp (fun z' => K (z, z')) 2 (sliceMeasure (N := N) μG ρ β),
        ∑' i, ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2
          = ∫⁻ z', ‖K (z, z')‖ₑ^2 ∂(sliceMeasure (N := N) μG ρ β) := by
  filter_upwards [memLp_section_ae μG ρ β hρcont hd hK] with z _hzsec hz
  have hpt : ∀ y : ℂ, ENNReal.ofReal (‖y‖^2) = ‖y‖ₑ^2 := fun y => by
    simp [enorm, ENNReal.ofReal_pow]
  have hsecstar : MemLp (fun z' => star (K (z, z'))) 2
      (sliceMeasure (N := N) μG ρ β) := hz.star
  set u : osSpace (N := N) μG ρ β := hsecstar.toLp _ with hu
  have hstep1 : ∀ i, kernelFun μG ρ β K (⇑(b i)) z
      = ⟪u, b i⟫ := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    show (∫ z', K (z, z') * ⇑(b i) z'
        ∂(sliceMeasure (N := N) μG ρ β))
      = ∫ z', ⟪⇑u z', ⇑(b i) z'⟫ ∂(sliceMeasure (N := N) μG ρ β)
    apply integral_congr_ae
    filter_upwards [hsecstar.coeFn_toLp] with z' hz'
    rw [RCLike.inner_apply, hz', starRingEnd_apply, star_star, mul_comm]
  have hnorm : ∀ i, ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2
      = ENNReal.ofReal (‖⟪b i, u⟫‖^2) := by
    intro i
    have hnn : ‖⟪u, b i⟫‖ = ‖⟪b i, u⟫‖ := by
      rw [← inner_conj_symm, starRingEnd_apply, norm_star]
    rw [← hpt, hstep1 i, hnn]
  rw [tsum_congr hnorm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
      (summable_inner_sq b u),
    parseval_tsum b u]
  have hnormE : ∫⁻ z', ‖K (z, z')‖ₑ^2 ∂(sliceMeasure (N := N) μG ρ β)
      = ∫⁻ z', ‖⇑u z'‖ₑ^2 ∂(sliceMeasure (N := N) μG ρ β) := by
    apply lintegral_congr_ae
    filter_upwards [hsecstar.coeFn_toLp] with z' hz'
    rw [hz', ← hpt, ← hpt, norm_star]
  rw [hnormE, ← eLpNorm_two_sq _ (MeasureTheory.Lp.aestronglyMeasurable u),
    MeasureTheory.Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp u).eLpNorm_lt_top.ne]

/-- The Hilbert–Schmidt identity: the squared operator norms of the
kernel operator on a Hilbert basis sum to the squared `L²` norm of
the kernel. -/
theorem hs_total (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    ∑' i, (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2
      = (eLpNorm K 2
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)))^2 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have h1 : ∀ i, (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2
      = ∫⁻ z, ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2
        ∂(sliceMeasure (N := N) μG ρ β) := by
    intro i
    rw [eLpNorm_two_sq _ (MeasureTheory.Lp.aestronglyMeasurable _)]
    apply lintegral_congr_ae
    have hcoe : ⇑(kernelOp μG ρ β hρcont hd K hK (b i))
        =ᵐ[sliceMeasure (N := N) μG ρ β]
        kernelFun μG ρ β K (⇑(b i)) := by
      rw [kernelOp_apply]
      exact coeFn_kernelRep μG ρ β hρcont hd K hK (b i)
    exact hcoe.mono fun z hz => by
      show ‖⇑(kernelOp μG ρ β hρcont hd K hK (b i)) z‖ₑ^2
        = ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2
      rw [hz]
  have hmeas : ∀ i, AEMeasurable
      (fun z => ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2)
      (sliceMeasure (N := N) μG ρ β) := by
    intro i
    have h := ((memLp_kernelFun μG ρ β hρcont hd hK (b i)).aestronglyMeasurable).aemeasurable.enorm
    exact (h.mul h).congr (Filter.Eventually.of_forall fun z => by
      show ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ * ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ
        = ‖kernelFun μG ρ β K (⇑(b i)) z‖ₑ^2
      rw [pow_two])
  rw [tsum_congr h1, ← lintegral_tsum hmeas]
  trans ∫⁻ z, ∫⁻ z', ‖K (z, z')‖ₑ^2 ∂(sliceMeasure (N := N) μG ρ β)
    ∂(sliceMeasure (N := N) μG ρ β)
  · apply lintegral_congr_ae
    filter_upwards [hs_identity_ae μG ρ β hρcont hd K hK b,
      memLp_section_ae μG ρ β hρcont hd hK] with z hid hz
    exact hid hz
  · have hKp : AEMeasurable (fun p => ‖K p‖ₑ^2)
        ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β)) := by
      have h := hK.aemeasurable.enorm
      exact (h.mul h).congr (Filter.Eventually.of_forall fun p => by
        show ‖K p‖ₑ * ‖K p‖ₑ = ‖K p‖ₑ^2
        rw [pow_two])
    rw [← MeasureTheory.lintegral_prod _ hKp,
      eLpNorm_two_sq _ hK.aestronglyMeasurable]

/-- The Hilbert–Schmidt sum is finite. -/
theorem hs_total_ne_top (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    (∑' i, (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2) ≠ ∞ := by
  rw [hs_total μG ρ β hρcont hd K hK b, pow_two]
  exact ENNReal.mul_ne_top hK.eLpNorm_lt_top.ne hK.eLpNorm_lt_top.ne

/-- Summability of the squared norms `‖S bᵢ‖²`. -/
theorem summable_norm_sq_kernelOp (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    Summable (fun i => ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2) := by
  have hsum := ENNReal.summable_toReal (hs_total_ne_top μG ρ β hρcont hd K hK b)
  refine hsum.congr fun i => ?_
  rw [ENNReal.toReal_pow, ← MeasureTheory.Lp.norm_def]

/-- The tail of the Hilbert–Schmidt sum outside a finite set `F`:
the `tsum` of `‖S bᵢ‖²` over the complement subtype. -/
noncomputable def tailSq (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι) : ℝ :=
  ∑' i : ↥(F : Set ι)ᶜ, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2

/-- The tail family is summable. -/
theorem summable_tailSq (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι) :
    Summable (fun i : ↥(F : Set ι)ᶜ =>
      ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2) := by
  have hsub : (∑' i : ↥(F : Set ι)ᶜ, (eLpNorm
      (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2) ≠ ∞ := by
    by_contra htop
    apply hs_total_ne_top μG ρ β hρcont hd K hK b
    rw [← ENNReal.sum_add_tsum_compl F
      (fun i => (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2), htop]
    simp
  refine (ENNReal.summable_toReal hsub).congr fun i => ?_
  rw [ENNReal.toReal_pow, ← MeasureTheory.Lp.norm_def]

/-- Finite partial sums of the Hilbert–Schmidt family over a finset
`A` disjoint from `F` are bounded by the tail outside `F`. -/
theorem sum_le_tailSq_of_subset (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F A : Finset ι)
    (hA : ∀ i ∈ A, i ∉ F) :
    ∑ i ∈ A, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2
      ≤ tailSq μG ρ β hρcont hd K hK b F := by
  classical
  let s' : Finset ↥(F : Set ι)ᶜ := A.subtype (fun i => i ∉ F)
  have hsum : (∑ i ∈ A, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2)
      = ∑ x ∈ s', ‖kernelOp μG ρ β hρcont hd K hK (b x)‖^2 := by
    show (∑ i ∈ A, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2)
      = ∑ x ∈ A.subtype (fun i => i ∉ F),
          ‖kernelOp μG ρ β hρcont hd K hK (b x)‖^2
    rw [Finset.sum_subtype_eq_sum_filter
      (fun i => ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2)]
    congr 1
    exact (Finset.filter_true_of_mem hA).symm
  rw [hsum]
  exact Summable.sum_le_tsum s' (fun x _ => sq_nonneg _)
    (summable_tailSq μG ρ β hρcont hd K hK b F)

/-- The Hilbert–Schmidt tail vanishes along the finite sets. -/
theorem tailSq_tendsto_zero (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    Filter.Tendsto (tailSq μG ρ β hρcont hd K hK b) Filter.atTop (nhds 0) := by
  have hEq : ∀ F : Finset ι, tailSq μG ρ β hρcont hd K hK b F
      = (∑' i : ↥(F : Set ι)ᶜ, (eLpNorm
          (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2).toReal := by
    intro F
    show (∑' i : ↥(F : Set ι)ᶜ, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖^2)
      = (∑' i : ↥(F : Set ι)ᶜ, (eLpNorm
          (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2).toReal
    rw [ENNReal.tsum_toReal_eq (fun i => by
      rw [pow_two]
      exact ENNReal.mul_ne_top
        ((MeasureTheory.Lp.memLp _).eLpNorm_lt_top.ne)
        ((MeasureTheory.Lp.memLp _).eLpNorm_lt_top.ne))]
    apply tsum_congr
    intro i
    rw [ENNReal.toReal_pow, ← MeasureTheory.Lp.norm_def]
  have hfin : ∀ F : Finset ι, (∑' i : {x // x ∉ F}, (eLpNorm
        (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
          (sliceMeasure (N := N) μG ρ β))^2) ≠ ∞ := by
    intro F
    have hle : (∑' i : {x // x ∉ F}, (eLpNorm
          (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2)
        ≤ ∑' i, (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2 := by
      show (∑' i : ↥(F : Set ι)ᶜ, (eLpNorm
          (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2)
        ≤ ∑' i, (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
            (sliceMeasure (N := N) μG ρ β))^2
      rw [← ENNReal.sum_add_tsum_compl F
        (fun i => (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
          (sliceMeasure (N := N) μG ρ β))^2)]
      exact le_add_self
    exact ne_top_of_le_ne_top
      (hs_total_ne_top μG ρ β hρcont hd K hK b) hle
  have h2 : Filter.Tendsto (fun F : Finset ι => (∑' i : {x // x ∉ F},
        (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
          (sliceMeasure (N := N) μG ρ β))^2).toReal) Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfin).mpr
      (ENNReal.tendsto_tsum_compl_atTop_zero
        (hs_total_ne_top μG ρ β hρcont hd K hK b))
  refine Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun F => (hEq F).symm) ?_
  show Filter.Tendsto (fun F : Finset ι => (∑' i : {x // x ∉ F},
      (eLpNorm (⇑(kernelOp μG ρ β hρcont hd K hK (b i))) 2
        (sliceMeasure (N := N) μG ρ β))^2).toReal) Filter.atTop (nhds 0)
  exact h2

/-! ### §4b — finite-rank approximation and compactness

The Hilbert–Schmidt identity of §4a says the squared norms
`‖S bᵢ‖²` are summable with sum `‖K‖₂²`. Truncating the basis
expansion of the input at a finite set `F` therefore approximates
`S = kernelOp K` in operator norm, with error `√(tailSq F)`, and
each truncation has finite-dimensional range. A norm limit of
finite-rank operators is compact (`isCompactOperator_of_tendsto`). -/

/-- A continuous linear operator whose range lies in a
finite-dimensional subspace is compact: the closure of the image
of the unit ball is a closed bounded subset of that subspace,
hence compact (Heine–Borel in the subspace). -/
theorem isCompactOperator_of_range_le_finiteDimensional {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F)
    (M : Submodule ℂ F) (hM : FiniteDimensional ℂ M)
    (hle : LinearMap.range T.toLinearMap ≤ M) :
    IsCompactOperator ⇑T := by
  classical
  haveI := hM
  have hsubM : closure (⇑T '' Metric.ball 0 1) ⊆ (M : Set F) := by
    apply closure_minimal _ M.closed_of_finiteDimensional
    intro y hy
    obtain ⟨x, -, rfl⟩ := hy
    exact hle (LinearMap.mem_range_self T.toLinearMap x)
  have hsubB : closure (⇑T '' Metric.ball 0 1) ⊆ Metric.closedBall 0 ‖T‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ ‖T‖ := by
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        rw [Metric.mem_ball, dist_zero_right] at hx
        exact hx.le
  set A' : Set M := Subtype.val ⁻¹' closure (⇑T '' Metric.ball 0 1) with hA'
  have hA'closed : IsClosed A' := isClosed_closure.preimage continuous_subtype_val
  have hA'bdd : Bornology.IsBounded A' := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * ‖T‖, fun x hx y hy => ?_⟩
    have hx2 : ‖(x : F)‖ ≤ ‖T‖ := by
      have h := hsubB hx
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hy2 : ‖(y : F)‖ ≤ ‖T‖ := by
      have h := hsubB hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    calc dist x y = dist (x : F) (y : F) := Subtype.dist_eq x y
      _ = ‖(x : F) - (y : F)‖ := dist_eq_norm _ _
      _ ≤ ‖(x : F)‖ + ‖(y : F)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖T‖ := by linarith
  haveI : ProperSpace M := FiniteDimensional.proper ℂ M
  have hA'comp : IsCompact A' :=
    Metric.isCompact_of_isClosed_isBounded hA'closed hA'bdd
  have hAeq : Subtype.val '' A' = closure (⇑T '' Metric.ball 0 1) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      exact ⟨⟨y, hsubM hy⟩, hy, rfl⟩
  have hcomp : IsCompact (closure (⇑T '' Metric.ball 0 1)) := by
    rw [← hAeq]
    exact hA'comp.image continuous_subtype_val
  refine ⟨closure (⇑T '' Metric.ball 0 1), hcomp, ?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
    (fun x hx => subset_closure ⟨x, hx, rfl⟩)

/-- The finite basis projection: partial sum of the Fourier
expansion at the finite set `F`, as a continuous linear map. -/
noncomputable def projSum (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (b i)

theorem projSum_apply (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι)
    (x : osSpace (N := N) μG ρ β) :
    projSum μG ρ β hρcont hd b F x = ∑ i ∈ F, ⟪b i, x⟫ • (b i) := by
  show (∑ i ∈ F, (innerSL ℂ (b i)).smulRight (b i)) x = _
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- The Fourier coefficients of the residual `x - projSum F x`
vanish at indices in `F`. -/
theorem inner_projSum_residual_of_mem (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι)
    (x : osSpace (N := N) μG ρ β) {i : ι} (hi : i ∈ F) :
    ⟪b i, x - projSum μG ρ β hρcont hd b F x⟫ = 0 := by
  classical
  have hterm : ∀ j ∈ F, ⟪b i, ⟪b j, x⟫ • (b j)⟫
      = if j = i then ⟪b j, x⟫ else 0 := by
    intro j _
    rw [inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hj : j = i => h hj.symm)]
      simp
  rw [inner_sub_right, projSum_apply, inner_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hi]
  exact sub_self _

/-- The Fourier coefficients of the residual `x - projSum F x`
agree with those of `x` at indices outside `F`. -/
theorem inner_projSum_residual_of_not_mem (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι)
    (x : osSpace (N := N) μG ρ β) {i : ι} (hi : i ∉ F) :
    ⟪b i, x - projSum μG ρ β hρcont hd b F x⟫ = ⟪b i, x⟫ := by
  classical
  have hterm : ∀ j ∈ F, ⟪b i, ⟪b j, x⟫ • (b j)⟫
      = if j = i then ⟪b j, x⟫ else 0 := by
    intro j _
    rw [inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hj : j = i => h hj.symm)]
      simp
  rw [inner_sub_right, projSum_apply, inner_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_neg hi]
  exact sub_zero _

/-- The finite-rank approximation of the kernel operator:
project the input onto the first `F` basis vectors, then apply
the kernel operator. -/
noncomputable def approxOp (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι) :
    osSpace (N := N) μG ρ β →L[ℂ] osSpace (N := N) μG ρ β :=
  (kernelOp μG ρ β hρcont hd K hK) ∘L projSum μG ρ β hρcont hd b F

/-- The range of the finite-rank approximation lies in the span
of the finitely many vectors `S (b i)`, `i ∈ F`. -/
theorem approxOp_range_le (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι) :
    LinearMap.range (approxOp μG ρ β hρcont hd K hK b F).toLinearMap
      ≤ Submodule.span ℂ
          ((fun i => kernelOp μG ρ β hρcont hd K hK (b i)) '' (F : Set ι)) := by
  rintro y ⟨x, rfl⟩
  have h1 : approxOp μG ρ β hρcont hd K hK b F x
      = ∑ i ∈ F, ⟪b i, x⟫ • (kernelOp μG ρ β hρcont hd K hK (b i)) := by
    show kernelOp μG ρ β hρcont hd K hK
        (projSum μG ρ β hρcont hd b F x) = _
    rw [projSum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  show (approxOp μG ρ β hρcont hd K hK b F) x
    ∈ Submodule.span ℂ
        ((fun i => kernelOp μG ρ β hρcont hd K hK (b i)) '' (F : Set ι))
  rw [h1]
  apply sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (Submodule.subset_span
      (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hi)))

/-- The approximation error in operator-norm form, pointwise in
the input: `‖S x - approxOp F x‖ ≤ √(tailSq F) * ‖x‖`. The proof
runs the finite partial sums of the basis expansion of the
residual `y = x - projSum F x` through finite Cauchy–Schwarz and
Bessel, then passes to the limit along the finite sets. -/
theorem approxOp_bound (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) (F : Finset ι)
    (x : osSpace (N := N) μG ρ β) :
    ‖kernelOp μG ρ β hρcont hd K hK x
        - approxOp μG ρ β hρcont hd K hK b F x‖
      ≤ Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) * ‖x‖ := by
  classical
  set S := kernelOp μG ρ β hρcont hd K hK with hS
  set y := x - projSum μG ρ β hρcont hd b F x with hy
  have hdiff : S x - approxOp μG ρ β hρcont hd K hK b F x = S y := by
    show S x - S (projSum μG ρ β hρcont hd b F x) = S y
    rw [← map_sub]
  rw [hdiff]
  have hsum : HasSum (fun i => S ((b.repr y) i • b i)) (S y) :=
    (b.hasSum_repr y).mapL S
  have htend : Filter.Tendsto
      (fun A : Finset ι => ∑ i ∈ A, S ((b.repr y) i • b i))
      Filter.atTop (nhds (S y)) := hsum
  have hbound : ∀ A : Finset ι,
      ‖∑ i ∈ A, S ((b.repr y) i • b i)‖
        ≤ Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) * ‖x‖ := by
    intro A
    have hterm : ∀ i ∈ A, S ((b.repr y) i • b i)
        = ⟪b i, y⟫ • S (b i) := by
      intro i _
      rw [map_smul, HilbertBasis.repr_apply_apply]
    have hyi0 : ∀ i ∈ F, ⟪b i, y⟫ = 0 :=
      fun i hi => inner_projSum_residual_of_mem μG ρ β hρcont hd b F x hi
    have hyi1 : ∀ i ∉ F, ⟪b i, y⟫ = ⟪b i, x⟫ :=
      fun i hi => inner_projSum_residual_of_not_mem μG ρ β hρcont hd b F x hi
    have hA1 : (∑ i ∈ A, ⟪b i, y⟫ • S (b i))
        = ∑ i ∈ A \ F, ⟪b i, y⟫ • S (b i) := by
      symm
      apply Finset.sum_subset Finset.sdiff_subset
      intro i hiA hiAF
      have hiF : i ∈ F := by
        by_contra hniF
        exact hiAF (Finset.mem_sdiff.mpr ⟨hiA, hniF⟩)
      rw [hyi0 i hiF, zero_smul]
    have hA2 : (∑ i ∈ A \ F, ⟪b i, y⟫ • S (b i))
        = ∑ i ∈ A \ F, ⟪b i, x⟫ • S (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [hyi1 i hi.2]
    have hnormsum : ‖∑ i ∈ A \ F, ⟪b i, x⟫ • S (b i)‖
        ≤ ∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (A \ F)
      (fun i => ‖⟪b i, x⟫‖) (fun i => ‖S (b i)‖)
    have hP : (∑ i ∈ A \ F, ‖⟪b i, x⟫‖^2) ≤ ‖x‖^2 := by
      have h := Summable.sum_le_tsum (A \ F) (fun i _ => sq_nonneg _)
        (summable_inner_sq b x)
      rwa [parseval_tsum b x] at h
    have hQ : (∑ i ∈ A \ F, ‖S (b i)‖^2)
        ≤ tailSq μG ρ β hρcont hd K hK b F :=
      sum_le_tailSq_of_subset μG ρ β hρcont hd K hK b F (A \ F)
        (fun i hi => (Finset.mem_sdiff.mp hi).2)
    have hnn : 0 ≤ ∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖ :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hsqrtP : Real.sqrt (∑ i ∈ A \ F, ‖⟪b i, x⟫‖^2) ≤ ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg x)]
      exact Real.sqrt_le_sqrt hP
    have hstep : (∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖)
        ≤ Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) * ‖x‖ := by
      calc (∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖)
          = Real.sqrt ((∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖)^2) :=
            (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt ((∑ i ∈ A \ F, ‖⟪b i, x⟫‖^2)
              * (∑ i ∈ A \ F, ‖S (b i)‖^2)) := Real.sqrt_le_sqrt hCS
        _ = Real.sqrt (∑ i ∈ A \ F, ‖⟪b i, x⟫‖^2)
              * Real.sqrt (∑ i ∈ A \ F, ‖S (b i)‖^2) :=
            Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _)) _
        _ ≤ ‖x‖ * Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) :=
            mul_le_mul hsqrtP
              (Real.sqrt_le_sqrt hQ) (Real.sqrt_nonneg _) (norm_nonneg _)
        _ = Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) * ‖x‖ := mul_comm _ _
    calc ‖∑ i ∈ A, S ((b.repr y) i • b i)‖
        = ‖∑ i ∈ A \ F, ⟪b i, x⟫ • S (b i)‖ := by
          rw [Finset.sum_congr rfl hterm, hA1, hA2]
      _ ≤ ∑ i ∈ A \ F, ‖⟪b i, x⟫‖ * ‖S (b i)‖ := hnormsum
      _ ≤ Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) * ‖x‖ := hstep
  have hnorm : Filter.Tendsto
      (fun A : Finset ι => ‖∑ i ∈ A, S ((b.repr y) i • b i)‖)
      Filter.atTop (nhds ‖S y‖) :=
    (continuous_norm.tendsto _).comp htend
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall hbound)

/-- The finite-rank approximations converge to the kernel
operator in operator norm, since the Hilbert–Schmidt tail
vanishes along the finite sets (§4a). -/
theorem kernelOp_tendsto_approxOp (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    Filter.Tendsto (fun F : Finset ι => approxOp μG ρ β hρcont hd K hK b F)
      Filter.atTop (nhds (kernelOp μG ρ β hρcont hd K hK)) := by
  have hnormbound : ∀ F : Finset ι,
      ‖approxOp μG ρ β hρcont hd K hK b F - kernelOp μG ρ β hρcont hd K hK‖
        ≤ Real.sqrt (tailSq μG ρ β hρcont hd K hK b F) := by
    intro F
    have h := ContinuousLinearMap.opNorm_le_bound
      (kernelOp μG ρ β hρcont hd K hK - approxOp μG ρ β hρcont hd K hK b F)
      (Real.sqrt_nonneg _) (fun x => by
        rw [sub_apply]
        exact approxOp_bound μG ρ β hρcont hd K hK b F x)
    rwa [norm_sub_rev] at h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun F => Real.sqrt
    (tailSq μG ρ β hρcont hd K hK b F)) (fun F => dist_nonneg) (fun F => ?_) ?_
  · rw [dist_eq_norm]
    exact hnormbound F
  · have h := (Real.continuous_sqrt.tendsto 0).comp
      (tailSq_tendsto_zero μG ρ β hρcont hd K hK b)
    simpa only [Real.sqrt_zero, Function.comp_def] using h

/-- **Compactness of the kernel operator.** Every continuous
kernel operator on the slice space is compact: it is the
operator-norm limit of its finite-rank basis truncations.
Positivity is nowhere used. -/
theorem kernelOp_compact (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G) → ℂ)
    (hK : MemLp K 2
      ((sliceMeasure (N := N) μG ρ β).prod (sliceMeasure (N := N) μG ρ β)))
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    IsCompactOperator ⇑(kernelOp μG ρ β hρcont hd K hK) := by
  apply isCompactOperator_of_tendsto
    (F := fun F : Finset ι => approxOp μG ρ β hρcont hd K hK b F)
    (f := kernelOp μG ρ β hρcont hd K hK)
    (kernelOp_tendsto_approxOp μG ρ β hρcont hd K hK b)
  apply Filter.Eventually.of_forall
  intro F
  exact isCompactOperator_of_range_le_finiteDimensional _
    (Submodule.span ℂ
      ((fun i => kernelOp μG ρ β hρcont hd K hK (b i)) '' (F : Set ι)))
    (FiniteDimensional.span_of_finite ℂ
      ((Finset.finite_toSet F).image _))
    (approxOp_range_le μG ρ β hρcont hd K hK b F)

/-- **Compactness of the transfer operator, conditional on the
density hypothesis `HDen`.** Wherever the two-slice law has an
`L²` density against the product of its marginals, the transfer
operator is that kernel operator, hence compact. Positivity is
nowhere used. -/
theorem transferOp_compact_of_HDen (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (h : HDen μG ρ β hN2 hρcont hd)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β) := by
  obtain ⟨K, hK, heq⟩ := transferOp_eq_kernelOp_of_HDen μG ρ β hN2 hρcont hd h
  rw [heq]
  exact kernelOp_compact μG ρ β hρcont hd K hK b

/-- **Compactness of the transfer operator at `β = 0`,
unconditional.** At zero coupling the density hypothesis is
discharged (§3), so the transfer operator is compact at every
`(G, ρ)`. -/
theorem transferOp_compact_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ 0)) :
    IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont 0) :=
  transferOp_compact_of_HDen μG ρ 0 hN2 hρcont hd
    (hden_zero μG ρ hN2 hρcont hd) b

end Compactness

/-! ## §5 — the spectral package and the gap

For the compact operator `T_β` (compactness supplied by §4
wherever `HDen` holds, unconditionally at `β = 0`), the spectrum
away from `0` consists of eigenvalues, finitely many above any
positive threshold (self-adjointness at `Even N` is the landed
1b-D symmetry). The **gap** — a uniform distance of the spectrum
from `1`, off the vacuum eigenvalue — is proved **conditional on
the named hypothesis `TransferFormPos`** (operator positivity of
the form on all of `osSpace`, plus simplicity of the vacuum
eigenvalue): classically both follow from pointwise strict
positivity of the two-slice Gibbs kernel (Perron–Frobenius /
Jentzsch). The corpus lands form positivity only on slice
observables (`transferOp_form_nonneg`); the implication to
`TransferFormPos` at general `(G, ρ)` is exactly Stage 1b-B's
open positivity content, and is **not** asserted here. At
`β = 0` the gap is unconditional with `δ = 1`, read off the
landed rank-one form of `T₀`. -/

section Spectral

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] {ι : Type*} [Countable ι]

/-- The transfer form is symmetric at `Even N` (landed
reflection invariance, 1b-D). -/
theorem transfer_inner_symm (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    (x y : osSpace (N := N) μG ρ β) :
    inner ℂ (transferOp μG ρ hN2 hρcont β x) y
      = inner ℂ x (transferOp μG ρ hN2 hρcont β y) := by
  have h := ContinuousLinearMap.adjoint_inner_left
    (transferOp μG ρ hN2 hρcont β) y x
  rwa [transferOp_adjoint μG ρ hN2 hρcont hN β] at h

/-- Eigenvalues of `T_β` at `Even N` are real. -/
theorem transfer_eigenvalue_star (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    {lam : ℂ} {v : osSpace (N := N) μG ρ β} (hv : v ≠ 0)
    (hlam : transferOp μG ρ hN2 hρcont β v = lam • v) :
    star lam = lam := by
  have h1 : inner ℂ (transferOp μG ρ hN2 hρcont β v) v
      = inner ℂ v (transferOp μG ρ hN2 hρcont β v) :=
    transfer_inner_symm μG ρ β hN2 hρcont hN v v
  rw [hlam, inner_smul_left, inner_smul_right] at h1
  have hvv : (inner ℂ v v) ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact pow_ne_zero 2
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))
  have h2 := mul_right_cancel₀ hvv h1
  rwa [starRingEnd_apply] at h2

/-- Eigenvalues of `T_β` have norm at most `1` (contraction). -/
theorem transfer_eigenvalue_norm_le_one (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g)
    {lam : ℂ} {v : osSpace (N := N) μG ρ β} (hv : v ≠ 0)
    (hlam : transferOp μG ρ hN2 hρcont β v = lam • v) :
    ‖lam‖ ≤ 1 := by
  have hpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : ‖lam‖ * ‖v‖ ≤ 1 * ‖v‖ := by
    calc ‖lam‖ * ‖v‖ = ‖lam • v‖ := (norm_smul lam v).symm
      _ = ‖transferOp μG ρ hN2 hρcont β v‖ := by rw [hlam]
      _ ≤ ‖transferOp μG ρ hN2 hρcont β‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ v
      _ ≤ 1 * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
          exact transferOp_norm_le μG ρ hN2 hρcont β
  by_contra hcon
  push Not at hcon
  have h2 : (1 : ℝ) * ‖v‖ < ‖lam‖ * ‖v‖ :=
    mul_lt_mul_of_pos_right hcon hpos
  rw [one_mul] at h1 h2
  linarith

/-- Eigenvectors of `T_β` for eigenvalues `≠ 1` are orthogonal
to the vacuum. -/
theorem transfer_eigenvalue_inner_vacuum (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN : Even N)
    {lam : ℂ} (hlam1 : lam ≠ 1)
    {v : osSpace (N := N) μG ρ β}
    (hlam : transferOp μG ρ hN2 hρcont β v = lam • v) :
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v = 0 := by
  have key : lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
      = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v := by
    calc lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
        = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) (lam • v) :=
          (inner_smul_right _ _ _).symm
      _ = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β)
            (transferOp μG ρ hN2 hρcont β v) := by rw [hlam]
      _ = inner ℂ (transferOp μG ρ hN2 hρcont β
            (osVacuum (N := N) μG ρ hρcont hd β)) v :=
          (transfer_inner_symm μG ρ β hN2 hρcont hN _ _).symm
      _ = inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v := by
          rw [transferOp_vacuum μG ρ hN2 hρcont hd β]
  have hsub : (lam - 1) * inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) v
      = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact key
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (eq_of_sub_eq_zero h) hlam1
  · exact h

/-- Eigenvectors for distinct eigenvalues of `T_β` at `Even N`
are orthogonal. -/
theorem transfer_eigen_orthogonal (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    {lam μ : ℂ} {v w : osSpace (N := N) μG ρ β}
    (hw : w ≠ 0)
    (hlam : transferOp μG ρ hN2 hρcont β v = lam • v)
    (hμ : transferOp μG ρ hN2 hρcont β w = μ • w)
    (hlamμ : lam ≠ μ) :
    inner ℂ w v = 0 := by
  have hμstar : star μ = μ :=
    transfer_eigenvalue_star μG ρ β hN2 hρcont hN hw hμ
  have key : lam * inner ℂ w v = μ * inner ℂ w v := by
    calc lam * inner ℂ w v
        = inner ℂ w (transferOp μG ρ hN2 hρcont β v) := by
          rw [hlam, inner_smul_right]
      _ = inner ℂ (transferOp μG ρ hN2 hρcont β w) v :=
          (transfer_inner_symm μG ρ β hN2 hρcont hN w v).symm
      _ = μ * inner ℂ w v := by
          rw [hμ, inner_smul_left, starRingEnd_apply, hμstar]
  have hsub : (lam - μ) * inner ℂ w v = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact key
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (eq_of_sub_eq_zero h) hlamμ
  · exact h

/-- **Finiteness of the eigenvalues above a threshold.** A compact
self-adjoint operator has only finitely many eigenvalues of norm
`≥ ε`, for every `ε > 0`: unit eigenvectors for distinct
eigenvalues are pairwise orthogonal, so their images under `T`
are pairwise `√2 ε`-separated, and a compact set contains no
infinite separated family. -/
theorem transfer_eigenvalues_finite_above (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN : Even N)
    (hT : IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β))
    {ε : ℝ} (hε : 0 < ε) :
    {lam : ℂ | (∃ v : osSpace (N := N) μG ρ β, v ≠ 0 ∧
        transferOp μG ρ hN2 hρcont β v = lam • v) ∧ ε ≤ ‖lam‖}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  let e := Set.Infinite.natEmbedding _ hinf
  have heig : ∀ n : ℕ, ∃ v : osSpace (N := N) μG ρ β,
      v ≠ 0 ∧ transferOp μG ρ hN2 hρcont β v = (e n).1 • v
        ∧ ε ≤ ‖(e n).1‖ := by
    intro n
    obtain ⟨⟨v, hv, hTv⟩, hεn⟩ := (e n).2
    exact ⟨v, hv, hTv, hεn⟩
  choose v hv using heig
  -- normalize the eigenvectors
  let c : ℕ → ℂ := fun n => ((‖v n‖⁻¹ : ℝ) : ℂ)
  have hcn : ∀ n, ‖c n‖ = ‖v n‖⁻¹ := by
    intro n
    show ‖((‖v n‖⁻¹ : ℝ) : ℂ)‖ = ‖v n‖⁻¹
    rw [Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hu_norm : ∀ n, ‖c n • v n‖ = 1 := by
    intro n
    rw [norm_smul, hcn n,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv n).1)]
  have hu_eig : ∀ n, transferOp μG ρ hN2 hρcont β (c n • v n)
      = (e n).1 • (c n • v n) := by
    intro n
    rw [map_smul, (hv n).2.1]
    exact smul_comm (c n) ((e n).1) (v n)
  have horth : ∀ n m : ℕ, n ≠ m →
      inner ℂ (c n • v n) (c m • v m) = 0 := by
    intro n m hnm
    have hne : (e n).1 ≠ (e m).1 := by
      intro hcon
      apply hnm
      exact e.injective (Subtype.ext hcon)
    have h0 : inner ℂ (v n) (v m) = 0 :=
      transfer_eigen_orthogonal μG ρ β hN2 hρcont hN (hv n).1
        (hv m).2.1 (hv n).2.1 (Ne.symm hne)
    rw [inner_smul_left, inner_smul_right, h0, mul_zero, mul_zero]
  -- the images are pairwise `√2 ε`-separated
  have hdist : ∀ n m : ℕ, n ≠ m →
      Real.sqrt 2 * ε ≤ dist
        (transferOp μG ρ hN2 hρcont β (c n • v n))
        (transferOp μG ρ hN2 hρcont β (c m • v m)) := by
    intro n m hnm
    have hinner : inner ℂ ((e n).1 • (c n • v n))
        ((e m).1 • (c m • v m)) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth n m hnm,
        mul_zero, mul_zero]
    have hsq : 2 * ε^2 ≤ ‖transferOp μG ρ hN2 hρcont β (c n • v n)
        - transferOp μG ρ hN2 hρcont β (c m • v m)‖^2 := by
      rw [hu_eig n, hu_eig m, norm_sub_sq (𝕜 := ℂ),
        RCLike.re_to_complex, hinner]
      simp only [Complex.zero_re, mul_zero, sub_zero]
      have h1 : ε^2 ≤ ‖(e n).1 • (c n • v n)‖^2 := by
        rw [norm_smul, hu_norm n, mul_one]
        exact pow_le_pow_left₀ hε.le (hv n).2.2 2
      have h2 : ε^2 ≤ ‖(e m).1 • (c m • v m)‖^2 := by
        rw [norm_smul, hu_norm m, mul_one]
        exact pow_le_pow_left₀ hε.le (hv m).2.2 2
      linarith
    have hsqrt : Real.sqrt (2 * ε^2) = Real.sqrt 2 * ε := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq hε.le]
    rw [← hsqrt, dist_eq_norm,
      ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  -- compactness: a convergent subsequence, contradicting separation
  have hC : IsCompact (closure (⇑(transferOp μG ρ hN2 hρcont β)
      '' Metric.closedBall 0 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hmem : ∀ n, transferOp μG ρ hN2 hρcont β (c n • v n)
      ∈ closure (⇑(transferOp μG ρ hN2 hρcont β)
        '' Metric.closedBall 0 1) := by
    intro n
    apply subset_closure
    refine ⟨c n • v n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hu_norm n).le
  obtain ⟨a, -, φ, hφ, hlim⟩ := hC.tendsto_subseq hmem
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hlim) _
    (by have h2 : (0 : ℝ) < Real.sqrt 2 :=
          Real.sqrt_pos_of_pos (by norm_num)
        have h3 : (0 : ℝ) < Real.sqrt 2 * ε := mul_pos h2 hε
        linarith : (0 : ℝ) < Real.sqrt 2 * ε / 2)
  have hdN : dist (transferOp μG ρ hN2 hρcont β (c (φ N0) • v (φ N0))) a
      < Real.sqrt 2 * ε / 2 := hN0 N0 (le_refl N0)
  have hdN1 : dist
      (transferOp μG ρ hN2 hρcont β (c (φ (N0 + 1)) • v (φ (N0 + 1)))) a
      < Real.sqrt 2 * ε / 2 := hN0 (N0 + 1) (Nat.le_succ N0)
  have hne : φ N0 ≠ φ (N0 + 1) :=
    fun hcon => (by omega : N0 ≠ N0 + 1) (hφ.injective hcon)
  have hsep := hdist (φ N0) (φ (N0 + 1)) hne
  have htri : dist (transferOp μG ρ hN2 hρcont β (c (φ N0) • v (φ N0)))
        (transferOp μG ρ hN2 hρcont β (c (φ (N0 + 1)) • v (φ (N0 + 1))))
      ≤ dist (transferOp μG ρ hN2 hρcont β (c (φ N0) • v (φ N0))) a
        + dist a
          (transferOp μG ρ hN2 hρcont β
            (c (φ (N0 + 1)) • v (φ (N0 + 1)))) :=
    dist_triangle _ _ _
  rw [dist_comm a _] at htri
  have hlt2 : dist (transferOp μG ρ hN2 hρcont β (c (φ N0) • v (φ N0)))
        (transferOp μG ρ hN2 hρcont β (c (φ (N0 + 1)) • v (φ (N0 + 1))))
      < Real.sqrt 2 * ε :=
    lt_of_le_of_lt htri (by linarith [hdN, hdN1])
  exact absurd (lt_of_le_of_lt hsep hlt2) (lt_irrefl _)

/-- Nonzero spectral points of the compact transfer operator
are eigenvalues (Fredholm alternative). -/
theorem transfer_eigen_of_mem_spectrum (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hT : IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β))
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β))
    (hlam0 : lam ≠ 0) :
    ∃ v : osSpace (N := N) μG ρ β, v ≠ 0 ∧
      transferOp μG ρ hN2 hρcont β v = lam • v := by
  have hEv := (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
    hT hlam0).mpr hlam
  obtain ⟨v, hvE, hv0⟩ := (Submodule.ne_bot_iff _).mp hEv
  exact ⟨v, hv0, Module.End.mem_eigenspace_iff.mp hvE⟩

/-- **Discreteness of the spectrum above any threshold.** For
the compact transfer operator at `Even N`, the spectral points
of norm `≥ ε` are finite in number, for every `ε > 0`. -/
theorem transfer_spectrum_finite_above (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN : Even N)
    (hT : IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β))
    {ε : ℝ} (hε : 0 < ε) :
    {lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β)
      | ε ≤ ‖lam‖}.Finite := by
  apply Set.Finite.subset
    (transfer_eigenvalues_finite_above μG ρ β hN2 hρcont hd hN hT hε)
  intro lam hlam
  obtain ⟨hlamS, hεlam⟩ := hlam
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hεlam
    linarith
  exact ⟨transfer_eigen_of_mem_spectrum μG ρ β hN2 hρcont hT
    hlamS hlam0, hεlam⟩

/-- **The named positivity package (H-PF).** (a) The transfer
form is positive on *every* vector of `osSpace`; (b) the vacuum
is the unique (up to scalar) fixed vector. Classically both
follow from pointwise strict positivity of the two-slice Gibbs
kernel (Perron–Frobenius / Jentzsch). The corpus lands form
positivity only on slice observables
(`transferOp_form_nonneg`); the implication to (H-PF) at general
`(G, ρ)` is exactly the open Stage 1b-B positivity content, and
is not asserted anywhere in this module. -/
def TransferFormPos (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    Prop :=
  (∀ f : osSpace (N := N) μG ρ β,
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re) ∧
  (∀ v : osSpace (N := N) μG ρ β,
    transferOp μG ρ hN2 hρcont β v = v →
    v ∈ Submodule.span ℂ {osVacuum (N := N) μG ρ hρcont hd β})

/-- **The gap, conditional on (H-PF).** For the compact transfer
operator at `Even N` satisfying `TransferFormPos`, the spectrum
stays a uniform distance below `1` off the vacuum eigenvalue:
there is `δ > 0` with `‖lam‖ ≤ 1 - δ` for every spectral point
`lam ≠ 1`. The proof: eigenvalues are real, lie in `[0, 1]`
((H-PF)(a) gives the sign, contraction the bound), only
finitely many exceed `1/2` (compactness), and (H-PF)(b) keeps
`1` itself simple, so the rest are bounded by the largest
remaining one, resp. `1/2`. -/
theorem transfer_gap_of_formPos (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hN : Even N)
    (hT : IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β))
    (hPF : TransferFormPos μG ρ β hN2 hρcont hd) :
    ∃ δ > 0, ∀ lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β),
      lam ≠ 1 → ‖lam‖ ≤ 1 - δ := by
  have hΛfin : {lam : ℂ | (∃ v : osSpace (N := N) μG ρ β, v ≠ 0 ∧
        transferOp μG ρ hN2 hρcont β v = lam • v)
        ∧ (1 / 2 : ℝ) ≤ ‖lam‖}.Finite :=
    transfer_eigenvalues_finite_above μG ρ β hN2 hρcont hd hN hT
      (by norm_num)
  have heig : ∀ lam : ℂ, (∃ v : osSpace (N := N) μG ρ β, v ≠ 0 ∧
        transferOp μG ρ hN2 hρcont β v = lam • v) →
      star lam = lam ∧ 0 ≤ lam.re ∧ ‖lam‖ ≤ 1 ∧ ‖lam‖ = lam.re := by
    intro lam ⟨v, hv, hTv⟩
    have hstar := transfer_eigenvalue_star μG ρ β hN2 hρcont hN hv hTv
    have hnorm := transfer_eigenvalue_norm_le_one μG ρ β hN2
      hρcont hv hTv
    have hpos := hPF.1 v
    have hre_vv : (inner ℂ v v).re = ‖v‖^2 := by
      rw [← RCLike.re_to_complex]
      exact (norm_sq_eq_re_inner v).symm
    have him_vv : (inner ℂ v v).im = 0 := by
      rw [← RCLike.im_to_complex]
      exact inner_self_im v
    rw [hTv, inner_smul_right, Complex.mul_re, hre_vv, him_vv,
      mul_zero, sub_zero] at hpos
    have hre : 0 ≤ lam.re :=
      nonneg_of_mul_nonneg_left hpos
        (pow_pos (norm_pos_iff.mpr hv) 2)
    have him : lam.im = 0 :=
      Complex.conj_eq_iff_im.mp (by
        rw [starRingEnd_apply]
        exact hstar)
    have hnormeq : ‖lam‖ = lam.re := by
      have hlam_eq : lam = (lam.re : ℂ) := by
        have h := (Complex.re_add_im lam).symm
        rw [him] at h
        simpa using h
      have h2 : ‖lam‖ = ‖(lam.re : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖z‖) hlam_eq
      rw [h2, Complex.norm_real, Real.norm_of_nonneg hre]
    exact ⟨hstar, hre, hnorm, hnormeq⟩
  set R : Set ℝ := (fun lam : ℂ => lam.re)
      '' {lam ∈ {lam : ℂ | (∃ v : osSpace (N := N) μG ρ β, v ≠ 0 ∧
          transferOp μG ρ hN2 hρcont β v = lam • v)
          ∧ (1 / 2 : ℝ) ≤ ‖lam‖} | lam ≠ 1} ∪ {1 / 2} with hR
  have hRfin : R.Finite :=
    ((hΛfin.subset (fun lam h => h.1)).image _).union
      (Set.finite_singleton _)
  have hRne : R.Nonempty := ⟨1 / 2, by simp [hR]⟩
  have hr12 : (1 / 2 : ℝ) ≤ sSup R :=
    le_csSup hRfin.bddAbove (by simp [hR])
  have hr_mem : sSup R ∈ R := hRne.csSup_mem hRfin
  have hr_lt : sSup R < 1 := by
    rcases hr_mem with ⟨lam, hlam, hlamre⟩ | h
    · rw [← hlamre]
      show lam.re < 1
      obtain ⟨hstar, hre, hnorm, hnormeq⟩ := heig lam hlam.1.1
      by_contra hcon
      push Not at hcon
      have hre1 : lam.re = 1 := le_antisymm (hnormeq ▸ hnorm) hcon
      have him : lam.im = 0 :=
        Complex.conj_eq_iff_im.mp (by
          rw [starRingEnd_apply]
          exact hstar)
      exact hlam.2 (by
        apply Complex.ext
        · simp [hre1]
        · simp [him])
    · have h12 : sSup R = 1 / 2 := Set.mem_singleton_iff.mp h
      linarith
  refine ⟨1 - sSup R, by linarith [hr_lt], ?_⟩
  intro lam hlamS hlam1
  by_cases hlam0 : lam = 0
  · subst hlam0
    simp only [norm_zero]
    linarith [hr12]
  · obtain ⟨v, hv, hTv⟩ := transfer_eigen_of_mem_spectrum μG ρ β
      hN2 hρcont hT hlamS hlam0
    obtain ⟨hstar, hre, hnorm, hnormeq⟩ := heig lam ⟨v, hv, hTv⟩
    by_cases hbig : (1 / 2 : ℝ) ≤ ‖lam‖
    · have hlamR : lam.re ∈ R :=
        Set.mem_union_left _
          (Set.mem_image_of_mem _
            ⟨⟨⟨v, hv, hTv⟩, hbig⟩, hlam1⟩)
      have hle := le_csSup hRfin.bddAbove hlamR
      linarith [hle, hnormeq]
    · push Not at hbig
      linarith [hr12]

/-- The vacuum is a unit vector: `⟪Ω, Ω⟫ = 1` (its
representative is a.e. constant `1` and the slice measure is a
probability measure). -/
theorem inner_osVacuum_self
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
      (osVacuum (N := N) μG ρ hρcont hd 0) = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd 0
  rw [inner_osVacuum_left μG ρ hρcont hd 0]
  have hvac : ⇑(osVacuum (N := N) μG ρ hρcont hd 0)
      =ᵐ[sliceMeasure (N := N) μG ρ 0] fun _ => (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ 0)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ 0] fun _ => (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  rw [integral_congr_ae hvac]
  simp

/-- **The spectrum at `β = 0`.** Together with compactness at
`β = 0` (which needs no density hypothesis), the Fredholm
alternative forces every spectral point to be an eigenvalue,
and `transferOp_zero_apply` — `T₀` is exactly the vacuum
projection — leaves only `0` and `1`. -/
theorem transfer_spectrum_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ 0)) :
    spectrum ℂ (transferOp μG ρ hN2 hρcont 0) ⊆ {0, 1} := by
  intro lam hlam
  by_cases hlam0 : lam = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hlam0)
  · have hT := transferOp_compact_zero μG ρ hN2 hρcont hd b
    obtain ⟨v, hv, hTv⟩ := transfer_eigen_of_mem_spectrum μG ρ 0
      hN2 hρcont hT hlam hlam0
    have hT0v : transferOp μG ρ hN2 hρcont 0 v
        = (inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v)
          • osVacuum (N := N) μG ρ hρcont hd 0 :=
      transferOp_zero_apply μG ρ hN2 hρcont hd v
    have hpair : lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v
        = inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v := by
      have e1 : inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
            (transferOp μG ρ hN2 hρcont 0 v)
          = lam * inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v := by
        rw [hTv, inner_smul_right]
      have e2 : inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0)
            (transferOp μG ρ hN2 hρcont 0 v)
          = inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v := by
        rw [hT0v, inner_smul_right,
          inner_osVacuum_self μG ρ hρcont hd, mul_one]
      rw [e2] at e1
      exact e1.symm
    by_cases hc : inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v = 0
    · rw [hT0v, hc, zero_smul] at hTv
      rcases smul_eq_zero.mp hTv.symm with h | h
      · exact absurd h hlam0
      · exact absurd h hv
    · have hsub0 : (lam - 1)
          * inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) v = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact hpair
      rcases mul_eq_zero.mp hsub0 with h | h
      · exact Set.mem_insert_iff.mpr (Or.inr (by
          rw [Set.mem_singleton_iff]
          exact sub_eq_zero.mp h))
      · exact absurd h hc

/-- **The gap at `β = 0`, unconditional, with `δ = 1`.** The
spectrum is contained in `{0, 1}`, so every spectral point other
than the vacuum eigenvalue `1` has norm `0 = 1 - 1`: the lattice
gap at zero coupling is exactly `1`, the `β = 0` shadow of
`bdry_zero` (the boundary decouples, `NullStart`-style silence).
No positivity hypothesis is consumed: at `β = 0` the transfer
operator *is* the vacuum projection. -/
theorem transfer_gap_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ 0)) :
    ∃ δ > 0, ∀ lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont 0),
      lam ≠ 1 → ‖lam‖ ≤ 1 - δ := by
  refine ⟨1, one_pos, ?_⟩
  intro lam hlam hlam1
  have hsub := transfer_spectrum_zero μG ρ hN2 hρcont hd b hlam
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with rfl | h
  · simp
  · exact absurd h hlam1

end Spectral

end ThetLogos
