/-
# Q3-1 — October Route B, brick T1: the layer Gram-series criterion
# (working label — naming is Jeff's)

Menu item **Q3-1** of the Q3 distance scoping
(`~/workspace/your_files/q3-distance-scoping-2026-11-06.md`, §5 Q3-1
and §1 R2), building bricks **T0 + T1 only** of October Route B.
This module is the `layerKernel`-shaped analog of the landed
finite certificate ⇒ `LayerKernelPos` discharge
(`LayerKernelGramCert.lean`, G-0) and of the OS-side integrated
criterion `osForm_nonneg_of_gram_integrated`
(`LatticeGramSeries.lean`): a dominated Gram **series**
certificate (PIN-G of the Gram/SOS scoping
`~/workspace/your_files/gram-sos-lkp-scoping-2026-11-05.md`, §2
and §4 G-2) for the layer pairing.

## T0 — SETTLED PAPER, no Lean content

Route B's T0 is **settled paper** and is NOT built here: the
October scoping's §2 obstructions (i) (a finite Gram sum does not
fit the Wilson weight — the stratum variables are forgotten by
the split) and (ii) (finite rank / Peter–Weyl support forces a
series, not a finite sum, at a continuous group) were confirmed
by the Route C build (`LatticeGramSeries.lean`, whose header
records both halves: the finite hypothesis `hgram` of
`osForm_nonneg_of_gram` is not satisfiable by the Wilson weight,
and the integrated kernel's Gram expansion is a series with all
Fourier coefficients `> 0` at `β > 0`).  Citations: Q3 scoping
§1 R2; Gram/SOS scoping §1.1.  This brick therefore builds **T1
only**.

## What is built (T1)

* **(T1-a) The criterion variant** (`LayerGramSeriesCert`): a
  countable index type `ι`; weights `w j ≥ 0`; measurable
  features `Φ j`; sup bounds `B j` with `‖Φ j u‖ ≤ B j`;
  domination `Summable (fun j => w j * (B j)^2)`; and the kernel
  identity
  `layerKernel μG ρ β u u' = ∑' j, w j * (Φ j u * conj (Φ j u'))`.
  The Gram pairing computation is **proved** for every
  **integrable** observable `F`
  (`LayerGramSeriesCert.pairing_eq_of_integrable`):
  the pairing is the cast of `∑' j, w j * ‖Z j‖² ≥ 0`, where
  `Z j = ∫ u, conj (Φ j u) * F u` is `gramSeriesObs`; and the
  nonnegativity corollary
  (`pairing_re_nonneg_of_integrable`) and the conditional
  discharge to `LayerKernelPos`
  (`layerKernelPos_of_integrable_obs`, under the explicit
  observable-regularity hypothesis that every gauge-invariant
  observable is integrable) are proved from it.
* **(T1-b) Domination infrastructure** (scalar level, for the
  future T4/G-2 assembly): absolute summability of the
  per-column exponential series at `‖z‖ ≤ 1`
  (`summable_pow_div_factorial_mul_norm_pow`,
  `summable_exp_complex_terms_of_norm_le_one`) and the `tsum`
  identity `∑' k, (β * z)^k / k! = Complex.exp (β * z)`
  (`tsum_exp_mul_eq_exp_of_norm_le_one`, via the pin's
  `NormedSpace.expSeries_div_hasSum_exp` and
  `Complex.exp_eq_exp_ℂ`).  `β ≥ 0` is spent only where
  coefficient nonnegativity needs it.

## The one named obstruction (priced, at full rank)

The unconditional headline `cert ⇒ LayerKernelPos` for
**arbitrary** observables is NOT closed in this brick, and no
`sorry` stands in its place.  The exact missing lemma:
**the iterated `integral_tsum` swap for the layer pairing at a
non-integrable observable** — in the pin (Mathlib
v4.35.0-rc3), both `MeasureTheory.integral_tsum` and
`MeasureTheory.hasSum_integral_of_summable_integral_norm`
require `Integrable` of *every* summand, and the summands here
are `w j • (conj F · Φ j) ⊗ (conj (Φ j) · F)`, whose
integrability is exactly the integrability of `conj (Φ j) * F`
— not available for an arbitrary (gauge-invariant) `F`, whose
pairing is defined by the Bochner junk-value convention.
Extending the proved integrable-observable computation to all
`F` by that convention is a standalone analytic lemma; it is
named here, not hacked around.  The corpus precedent for the
conditional form landed here is
`Span3SeatSchurGateConsume`'s `*_of_integrable` discharges.

## Fences

* **T2 is NOT this brick**: the averaging-projection lemma
  already landed in-tree as `AveragingProjection.lean`
  (Haar averaging = orthogonal projection onto the invariant
  subspace, for unitary representations) — cited here, never
  rebuilt.  **T3/T4 are NOT commissioned** and are not built.
  **Route A (Peter–Weyl) is DO NOT COMMISSION** — untouched
  under any framing.
* **No existence claim anywhere**: the criterion is an
  implication, exactly like the landed finite cert.  Existence
  of a `LayerGramSeriesCert` at general `(N, G, ρ)`, `β > 0`,
  is T2/T3/G-2 territory and stays **OPEN**.
* **K-GRAM-DEGEN is armed at general level** (Gram/SOS scoping
  §2.2): it concerns *constructions* that force the kernel
  constant.  A criterion implication cannot fire it — this
  brick records it as **armed, not engaged by a criterion
  brick**.  The F3-style detector is carried over:
  `LayerGramSeriesCert.layerKernel_const_of_features_constant`
  proves constant features force a constant kernel.
* This brick shortens R2's critical path by landing its front
  end; **R2 itself remains open** (T2 exists in-tree as
  `AveragingProjection.lean`; T3/T4 and the separation
  identities do not).

NO CLAIM; dials 0/4; Dial 3 = 0.
-/

import ThetLogos.LayerKernelGramCert
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Matrix ENNReal NNReal Nat

namespace ThetLogos

/-! ## T1-b — scalar domination infrastructure (for T4/G-2)

The per-column exponential series at a unit-disk direction:
absolute summability of the real majorant series and the `tsum`
identity against `Complex.exp`.  Scalar level only; no
representation theory. -/

/-- **The real majorant series of the exponential at `‖z‖ ≤ 1`**
(the domination T4/G-2 will consume): for `β ≥ 0`,
`∑' k, β^k / k! * ‖z‖^k` converges absolutely, by comparison
with the exponential series `Real.summable_pow_div_factorial`. -/
theorem summable_pow_div_factorial_mul_norm_pow {β : ℝ} (hβ : 0 ≤ β)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => β ^ k / (k ! : ℝ) * ‖z‖ ^ k := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (Real.summable_pow_div_factorial β)
  · exact mul_nonneg
      (div_nonneg (pow_nonneg hβ _) (Nat.cast_nonneg _))
      (pow_nonneg (norm_nonneg _) _)
  · have h1 : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    have h2 : 0 ≤ β ^ k / (k ! : ℝ) :=
      div_nonneg (pow_nonneg hβ _) (Nat.cast_nonneg _)
    calc β ^ k / (k ! : ℝ) * ‖z‖ ^ k
        ≤ β ^ k / (k ! : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = β ^ k / (k ! : ℝ) := mul_one _

/-- **Absolute summability of the complex exponential terms**
`k ↦ (β * z)^k / k!` at `‖z‖ ≤ 1`, `β ≥ 0`: the norm series is
exactly the real majorant of
`summable_pow_div_factorial_mul_norm_pow`. -/
theorem summable_exp_complex_terms_of_norm_le_one {β : ℝ} (hβ : 0 ≤ β)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => ((β : ℂ) * z) ^ k / (k ! : ℂ) := by
  refine Summable.of_norm_bounded
    (summable_pow_div_factorial_mul_norm_pow hβ z hz) (fun k => ?_)
  rw [norm_div, norm_pow, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg hβ, norm_natCast]
  apply le_of_eq
  ring

/-- **The exponential series at `‖z‖ ≤ 1`, `HasSum` form**:
`∑ k, (β * z)^k / k! = Complex.exp (β * z)`, via the pin's
`NormedSpace.expSeries_div_hasSum_exp`. -/
theorem hasSum_exp_mul_of_norm_le_one {β : ℝ} (hβ : 0 ≤ β)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ => ((β : ℂ) * z) ^ k / (k ! : ℂ))
      (Complex.exp ((β : ℂ) * z)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((β : ℂ) * z)
  have h2 : Complex.exp ((β : ℂ) * z)
      = NormedSpace.exp ((β : ℂ) * z) :=
    congrFun Complex.exp_eq_exp_ℂ _
  rwa [h2]

/-- **The exponential series at `‖z‖ ≤ 1`, `tsum` form**:
`∑' k, (β * z)^k / k! = Complex.exp (β * z)`. -/
theorem tsum_exp_mul_eq_exp_of_norm_le_one {β : ℝ} (hβ : 0 ≤ β)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∑' k : ℕ, ((β : ℂ) * z) ^ k / (k ! : ℂ))
      = Complex.exp ((β : ℂ) * z) :=
  (hasSum_exp_mul_of_norm_le_one hβ z hz).tsum_eq

/-! ## T1-a — the layer Gram-series certificate (PIN-G) -/

section GramSeriesSection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (β : ℝ) {ι : Type*} [Countable ι]

/-- **A dominated Gram-series certificate for `𝒜` at
`(N, G, ρ, β)`** — the PIN-G analog of the finite
`LayerKernelSOSCert` (G-0): a countable index `ι`, nonnegative
weights `w`, measurable features `feat` with sup bounds
`bound`, domination `Summable (fun j => w j * (bound j)^2)`,
and the assembled kernel identity as a `tsum`.  An implication
device only: no field asserts that such a certificate exists
at any `(N, G, ρ, β)`. -/
structure LayerGramSeriesCert where
  /-- The Gram-series weights `w j`. -/
  w : ι → ℝ
  /-- All weights are nonnegative. -/
  w_nonneg : ∀ j, 0 ≤ w j
  /-- The separated features `Φ j`: measurable functions of the
  layer data alone. -/
  feat : ι → (LayerLink N → G) → ℂ
  /-- Each feature is measurable (strongly, for the product
  Haar probability measure on layer configurations). -/
  feat_meas : ∀ j, AEStronglyMeasurable (feat j)
    (Measure.pi fun _ : LayerLink N => μG)
  /-- The sup bounds `B j` of the features. -/
  bound : ι → ℝ
  /-- The sup bound: `‖Φ j u‖ ≤ B j` for every configuration. -/
  feat_bound : ∀ j u, ‖feat j u‖ ≤ bound j
  /-- **Domination (PIN-G)**: the weight-bound series
  converges. -/
  domination : Summable fun j => w j * (bound j) ^ 2
  /-- **(PIN-G)** The assembled kernel identity: the layer
  kernel is the Gram series over `ι`. -/
  kernel_eq : ∀ u u' : LayerLink N → G,
    layerKernel μG ρ β u u'
      = ∑' j, ((w j : ℝ) : ℂ) * feat j u
          * (starRingEnd ℂ) (feat j u')

namespace LayerGramSeriesCert

variable (cert : LayerGramSeriesCert (N := N) (ι := ι) μG ρ β)

/-- The sup bounds are nonnegative (read off the feature bound
at the constant-`1` configuration). -/
theorem bound_nonneg (j : ι) : 0 ≤ cert.bound j :=
  (norm_nonneg _).trans (cert.feat_bound j (fun _ => 1))

/-- The kernel's Gram terms are summable at every pair of
configurations (domination spent pointwise). -/
theorem summable_kernel_terms (u u' : LayerLink N → G) :
    Summable fun j => ((cert.w j : ℝ) : ℂ) * cert.feat j u
      * (starRingEnd ℂ) (cert.feat j u') := by
  refine Summable.of_norm_bounded cert.domination (fun j => ?_)
  rw [norm_mul, norm_mul, starRingEnd_apply, norm_star,
    Complex.norm_real, Real.norm_of_nonneg (cert.w_nonneg j)]
  calc cert.w j * ‖cert.feat j u‖ * ‖cert.feat j u'‖
      ≤ cert.w j * cert.bound j * cert.bound j :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (cert.feat_bound j u)
            (cert.w_nonneg j))
          (cert.feat_bound j u') (norm_nonneg _)
          (mul_nonneg (cert.w_nonneg j) (bound_nonneg (μG := μG) (ρ := ρ) (β := β) cert j))
    _ = cert.w j * (cert.bound j) ^ 2 := by ring

/-- The kernel is dominated by the weight-bound series:
`‖𝒜(u, u')‖ ≤ ∑' j, w j * (B j)^2`. -/
theorem layerKernel_norm_le (u u' : LayerLink N → G) :
    ‖layerKernel μG ρ β u u'‖
      ≤ ∑' j, cert.w j * (cert.bound j) ^ 2 := by
  have hbound : ∀ j, ‖((cert.w j : ℝ) : ℂ) * cert.feat j u
        * (starRingEnd ℂ) (cert.feat j u')‖
      ≤ cert.w j * (cert.bound j) ^ 2 := by
    intro j
    rw [norm_mul, norm_mul, starRingEnd_apply, norm_star,
      Complex.norm_real, Real.norm_of_nonneg (cert.w_nonneg j)]
    calc cert.w j * ‖cert.feat j u‖ * ‖cert.feat j u'‖
        ≤ cert.w j * cert.bound j * cert.bound j :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cert.feat_bound j u)
              (cert.w_nonneg j))
            (cert.feat_bound j u') (norm_nonneg _)
            (mul_nonneg (cert.w_nonneg j)
              (bound_nonneg (μG := μG) (ρ := ρ) (β := β) cert j))
      _ = cert.w j * (cert.bound j) ^ 2 := by ring
  have hnorm : Summable fun j =>
      ‖((cert.w j : ℝ) : ℂ) * cert.feat j u
        * (starRingEnd ℂ) (cert.feat j u')‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound
      cert.domination
  rw [cert.kernel_eq]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (Summable.tsum_le_tsum hbound hnorm cert.domination)

/-- **The F3 degeneracy test, series form.**  If a
certificate's features are all constant in the configuration,
its kernel is constant — the FACT/`β = 0` shape.  At `β > 0`
such a certificate is exactly what **K-GRAM-DEGEN** fires on;
the kill is armed, not engaged by this criterion brick. -/
theorem layerKernel_const_of_features_constant
    (hconst : gramFeaturesConstant cert.feat) :
    ∃ K₀ : ℂ, ∀ u u' : LayerLink N → G,
      layerKernel μG ρ β u u' = K₀ := by
  refine ⟨∑' j, ((cert.w j : ℝ) : ℂ) * cert.feat j 1
      * (starRingEnd ℂ) (cert.feat j 1), fun u u' => ?_⟩
  rw [cert.kernel_eq]
  refine tsum_congr fun j => ?_
  rw [hconst j u 1, hconst j u' 1]

end LayerGramSeriesCert

/-- **The Gram observation of a series feature family at an
observable `F`**: `Z j = ∫ u, conj (Φ j u) * F u` against the
product Haar probability measure, so that the pairing's
`j`-term is `w j * conj (Z j) * Z j`. -/
noncomputable def gramSeriesObs {ι : Type*}
    (cert : LayerGramSeriesCert (N := N) (ι := ι) μG ρ β)
    (F : (LayerLink N → G) → ℂ) (j : ι) : ℂ :=
  ∫ u, (starRingEnd ℂ) (cert.feat j u) * F u
    ∂(Measure.pi fun _ : LayerLink N => μG)

namespace LayerGramSeriesCert

variable (cert : LayerGramSeriesCert (N := N) (ι := ι) μG ρ β)
variable (F : (LayerLink N → G) → ℂ)

/-- **Summability of the real Gram series** at an integrable
observable: `∑' j, w j * ‖Z j‖²` converges, dominated by
`(∫ ‖F‖)^2 • ∑' j, w j * (B j)^2`. -/
theorem summable_gramSeriesObs_sq (hF : Integrable F
    (Measure.pi fun _ : LayerLink N => μG)) :
    Summable fun j => cert.w j
      * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 := by
  classical
  set πμ : Measure (LayerLink N → G) :=
    Measure.pi fun _ : LayerLink N => μG with hπμ
  set L : ℝ := ∫ u, ‖F u‖ ∂πμ with hL
  have hBint : ∀ j, Integrable
      (fun u => (starRingEnd ℂ) (cert.feat j u) * F u) πμ := by
    intro j
    have hmeas : AEStronglyMeasurable
        (fun u => (starRingEnd ℂ) (cert.feat j u)) πμ := by
      have h := (RCLike.continuous_conj).comp_aestronglyMeasurable
        (cert.feat_meas j)
      simpa only [Function.comp_def, starRingEnd_apply] using h
    exact hF.bdd_mul hmeas
      (ae_of_all _ fun u => by
        rw [starRingEnd_apply, norm_star]
        exact cert.feat_bound j u)
  have hBnorm : ∀ j, ∫ u, ‖(starRingEnd ℂ) (cert.feat j u) * F u‖ ∂πμ
      ≤ cert.bound j * L := by
    intro j
    calc ∫ u, ‖(starRingEnd ℂ) (cert.feat j u) * F u‖ ∂πμ
        ≤ ∫ u, ‖F u‖ * cert.bound j ∂πμ :=
          integral_mono (hBint j).norm (hF.norm.mul_const _)
            (fun u => by
              rw [norm_mul, starRingEnd_apply, norm_star]
              exact (mul_le_mul_of_nonneg_right
                  (cert.feat_bound j u) (norm_nonneg _)).trans_eq
                (mul_comm _ _))
      _ = L * cert.bound j := integral_mul_const _ _
      _ = cert.bound j * L := mul_comm _ _
  have hZ : ∀ j, ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ≤ cert.bound j * L :=
    fun j => (norm_integral_le_integral_norm _).trans (hBnorm j)
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (cert.w_nonneg j)
      (pow_nonneg (norm_nonneg _) _)) (fun j => ?_)
    (cert.domination.mul_left (L ^ 2))
  calc cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2
      ≤ cert.w j * (cert.bound j * L) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hZ j) _)
          (cert.w_nonneg j)
    _ = (L ^ 2) * (cert.w j * (cert.bound j) ^ 2) := by ring

/-- **The Gram pairing computation (T1-a), for integrable
observables.**  If `F` is integrable against the product Haar
probability measure, the `LayerKernelPos` pairing at `F` is
the cast of the nonnegative real series
`∑' j, w j * ‖Z j‖²`.  The two `integral_tsum` swaps are
dominated by `w j * (B j)^2 * (∫ ‖F‖)^2`, from the
certificate's domination.  For non-integrable `F` the swap is
the named obstruction on this module's face — no statement
about it is made here. -/
theorem pairing_eq_of_integrable (hF : Integrable F
    (Measure.pi fun _ : LayerLink N => μG)) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = ((∑' j, cert.w j
          * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set πμ : Measure (LayerLink N → G) :=
    Measure.pi fun _ : LayerLink N => μG with hπμ
  -- The `L¹` size of `F`, the single scalar the domination consumes.
  set L : ℝ := ∫ u, ‖F u‖ ∂πμ with hL
  have hLnn : 0 ≤ L :=
    integral_nonneg_of_ae (ae_of_all _ fun u => norm_nonneg _)
  -- Measurability of the conjugated features.
  have hconjmeas : ∀ j, AEStronglyMeasurable
      (fun u => (starRingEnd ℂ) (cert.feat j u)) πμ := by
    intro j
    have h := (RCLike.continuous_conj).comp_aestronglyMeasurable
      (cert.feat_meas j)
    simpa only [Function.comp_def, starRingEnd_apply] using h
  -- Integrability of the two half-pairing functions.
  have hBint : ∀ j, Integrable
      (fun u => (starRingEnd ℂ) (cert.feat j u) * F u) πμ :=
    fun j => hF.bdd_mul (hconjmeas j)
      (ae_of_all _ fun u => by
        rw [starRingEnd_apply, norm_star]
        exact cert.feat_bound j u)
  -- Conjugation preserves integrability (measurability plus
  -- the norm-based finite-integral characterization).
  have hconjInt : ∀ g : (LayerLink N → G) → ℂ, Integrable g πμ →
      Integrable (fun u => (starRingEnd ℂ) (g u)) πμ := by
    intro g hg
    refine ⟨?_, ?_⟩
    · have h := (RCLike.continuous_conj).comp_aestronglyMeasurable hg.1
      simpa only [Function.comp_def, starRingEnd_apply] using h
    · exact hg.2.congr' (ae_of_all _ fun u => by
        rw [starRingEnd_apply, norm_star])
  have hAint : ∀ j, Integrable
      (fun u => (starRingEnd ℂ) (F u) * cert.feat j u) πμ := by
    intro j
    have hfun : (fun u => (starRingEnd ℂ) (F u) * cert.feat j u)
        = fun u => (starRingEnd ℂ)
            ((starRingEnd ℂ) (cert.feat j u) * F u) := by
      funext u
      simp only [starRingEnd_apply, map_mul, star_star]
      ring
    rw [hfun]
    exact hconjInt _ (hBint j)
  -- Norm-integral bounds for both halves.
  have hBnorm : ∀ j, ∫ u, ‖(starRingEnd ℂ) (cert.feat j u) * F u‖ ∂πμ
      ≤ cert.bound j * L := by
    intro j
    calc ∫ u, ‖(starRingEnd ℂ) (cert.feat j u) * F u‖ ∂πμ
        ≤ ∫ u, ‖F u‖ * cert.bound j ∂πμ :=
          integral_mono (hBint j).norm (hF.norm.mul_const _)
            (fun u => by
              rw [norm_mul, starRingEnd_apply, norm_star]
              exact (mul_le_mul_of_nonneg_right
                  (cert.feat_bound j u) (norm_nonneg _)).trans_eq
                (mul_comm _ _))
      _ = L * cert.bound j := integral_mul_const _ _
      _ = cert.bound j * L := mul_comm _ _
  have hAnorm : ∀ j, ∫ u, ‖(starRingEnd ℂ) (F u) * cert.feat j u‖ ∂πμ
      ≤ cert.bound j * L := by
    intro j
    calc ∫ u, ‖(starRingEnd ℂ) (F u) * cert.feat j u‖ ∂πμ
        ≤ ∫ u, ‖F u‖ * cert.bound j ∂πμ :=
          integral_mono (hAint j).norm (hF.norm.mul_const _)
            (fun u => by
              rw [norm_mul, starRingEnd_apply, norm_star]
              exact mul_le_mul_of_nonneg_left
                (cert.feat_bound j u) (norm_nonneg _))
      _ = L * cert.bound j := integral_mul_const _ _
      _ = cert.bound j * L := mul_comm _ _
  have hZ : ∀ j, ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ≤ cert.bound j * L :=
    fun j => (norm_integral_le_integral_norm _).trans (hBnorm j)
  -- The inner swap, at a fixed first configuration.
  have hInner : ∀ u : LayerLink N → G,
      (∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂πμ)
        = ∑' j, ((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u)
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j := by
    intro u
    have hpt : (fun u' => (starRingEnd ℂ) (F u)
          * layerKernel μG ρ β u u' * F u')
        = fun u' => ∑' j, (((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u))
            * ((starRingEnd ℂ) (cert.feat j u') * F u') := by
      funext u'
      rw [cert.kernel_eq]
      calc (starRingEnd ℂ) (F u)
            * (∑' j, ((cert.w j : ℝ) : ℂ) * cert.feat j u
                * (starRingEnd ℂ) (cert.feat j u')) * F u'
          = ((∑' j, ((cert.w j : ℝ) : ℂ) * cert.feat j u
                * (starRingEnd ℂ) (cert.feat j u'))
              * (starRingEnd ℂ) (F u)) * F u' := by ring
        _ = ∑' j, ((((cert.w j : ℝ) : ℂ) * cert.feat j u
                * (starRingEnd ℂ) (cert.feat j u'))
              * (starRingEnd ℂ) (F u)) * F u' := by
            rw [← tsum_mul_right, ← tsum_mul_right]
        _ = ∑' j, (((cert.w j : ℝ) : ℂ)
              * ((starRingEnd ℂ) (F u) * cert.feat j u))
              * ((starRingEnd ℂ) (cert.feat j u') * F u') :=
            tsum_congr fun j => by ring
    rw [hpt]
    have hInt : ∀ j, Integrable
        (fun u' => (((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u))
            * ((starRingEnd ℂ) (cert.feat j u') * F u')) πμ :=
      fun j => (hBint j).const_mul _
    have hSum : Summable fun j => ∫ u',
        ‖(((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u))
            * ((starRingEnd ℂ) (cert.feat j u') * F u')‖ ∂πμ := by
      refine Summable.of_nonneg_of_le
        (fun j => integral_nonneg_of_ae
          (ae_of_all _ fun u' => norm_nonneg _)) (fun j => ?_)
        (cert.domination.mul_left (‖F u‖ * L))
      calc ∫ u', ‖(((cert.w j : ℝ) : ℂ)
              * ((starRingEnd ℂ) (F u) * cert.feat j u))
              * ((starRingEnd ℂ) (cert.feat j u') * F u')‖ ∂πμ
          ≤ ∫ u', ‖(starRingEnd ℂ) (cert.feat j u') * F u'‖
              * (cert.w j * (‖F u‖ * cert.bound j)) ∂πμ :=
            integral_mono (hInt j).norm
              ((hBint j).norm.mul_const _) (fun u' => by
                have e : ‖(((cert.w j : ℝ) : ℂ)
                      * ((starRingEnd ℂ) (F u) * cert.feat j u))
                      * ((starRingEnd ℂ) (cert.feat j u') * F u')‖
                    = ‖(starRingEnd ℂ) (cert.feat j u') * F u'‖
                      * (cert.w j * (‖F u‖ * ‖cert.feat j u‖)) := by
                  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
                    Real.norm_of_nonneg (cert.w_nonneg j), norm_mul,
                    starRingEnd_apply, norm_star,
                    starRingEnd_apply, norm_star]
                  ring
                rw [e]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (cert.feat_bound j u) (norm_nonneg _))
                    (cert.w_nonneg j))
                  (norm_nonneg _))
        _ = (∫ u', ‖(starRingEnd ℂ) (cert.feat j u') * F u'‖ ∂πμ)
              * (cert.w j * (‖F u‖ * cert.bound j)) :=
            integral_mul_const _ _
        _ ≤ (cert.bound j * L)
              * (cert.w j * (‖F u‖ * cert.bound j)) :=
            mul_le_mul_of_nonneg_right (hBnorm j)
              (mul_nonneg (cert.w_nonneg j)
                (mul_nonneg (norm_nonneg _) (bound_nonneg (μG := μG) (ρ := ρ) (β := β) cert j)))
        _ = (‖F u‖ * L) * (cert.w j * (cert.bound j) ^ 2) := by ring
    calc (∫ u', ∑' j, (((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u))
            * ((starRingEnd ℂ) (cert.feat j u') * F u') ∂πμ)
        = ∑' j, ∫ u', (((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u))
            * ((starRingEnd ℂ) (cert.feat j u') * F u') ∂πμ :=
          (hasSum_integral_of_summable_integral_norm hInt hSum).tsum_eq.symm
      _ = ∑' j, ((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u)
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j := by
          refine tsum_congr fun j => ?_
          rw [integral_const_mul]
          rfl
  -- The outer swap.
  have hOuterInt : ∀ j, Integrable
      (fun u => ((cert.w j : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u) * cert.feat j u)
          * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j) πμ := by
    intro j
    have hfun : (fun u => ((cert.w j : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u) * cert.feat j u)
          * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
        = fun u => (((cert.w j : ℝ) : ℂ) * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
            * ((starRingEnd ℂ) (F u) * cert.feat j u) := by
      funext u
      ring
    rw [hfun]
    exact (hAint j).const_mul _
  have hOuterSum : Summable fun j => ∫ u,
      ‖((cert.w j : ℝ) : ℂ)
          * ((starRingEnd ℂ) (F u) * cert.feat j u)
          * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ∂πμ := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg_of_ae
        (ae_of_all _ fun u => norm_nonneg _)) (fun j => ?_)
      (cert.domination.mul_left (L ^ 2))
    calc ∫ u, ‖((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u)
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ∂πμ
        ≤ ∫ u, ‖F u‖ * (cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖
            * cert.bound j) ∂πμ :=
          integral_mono (hOuterInt j).norm (hF.norm.mul_const _)
            (fun u => by
              have e : ‖((cert.w j : ℝ) : ℂ)
                    * ((starRingEnd ℂ) (F u) * cert.feat j u)
                    * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖
                  = (‖F u‖ * ‖cert.feat j u‖)
                    * (cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖) := by
                rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
                  Real.norm_of_nonneg (cert.w_nonneg j),
                  starRingEnd_apply, norm_star]
                ring
              rw [e]
              refine (mul_le_mul
                (mul_le_mul_of_nonneg_left (cert.feat_bound j u)
                  (norm_nonneg _))
                (le_refl _)
                (mul_nonneg (cert.w_nonneg j) (norm_nonneg _))
                (mul_nonneg (norm_nonneg _)
                  (bound_nonneg (μG := μG) (ρ := ρ) (β := β) cert j))).trans_eq (by ring))
      _ = L * (cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ * cert.bound j) :=
          integral_mul_const _ _
      _ ≤ L * (cert.w j * (cert.bound j * L) * cert.bound j) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hZ j) (cert.w_nonneg j))
              (bound_nonneg (μG := μG) (ρ := ρ) (β := β) cert j)) hLnn
      _ = (L ^ 2) * (cert.w j * (cert.bound j) ^ 2) := by ring
  -- Assemble: pairing = ∑' j, w j * conj (Z j) * Z j = cast of ∑' w j ‖Z j‖².
  calc (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = ∫ u, ∑' j, ((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u)
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j ∂πμ :=
        integral_congr_ae (ae_of_all _ fun u => hInner u)
    _ = ∑' j, ∫ u, ((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (F u) * cert.feat j u)
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j ∂πμ :=
        (hasSum_integral_of_summable_integral_norm
          hOuterInt hOuterSum).tsum_eq.symm
    _ = ∑' j, ((cert.w j : ℝ) : ℂ)
            * ((starRingEnd ℂ) (gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j))
            * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j := by
        refine tsum_congr fun j => ?_
        have hfun : (fun u => ((cert.w j : ℝ) : ℂ)
              * ((starRingEnd ℂ) (F u) * cert.feat j u)
              * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
            = fun u => (((cert.w j : ℝ) : ℂ)
                * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
                * ((starRingEnd ℂ) (F u) * cert.feat j u) := by
          funext u
          ring
        rw [hfun, integral_const_mul]
        have hIA : ∫ u, (starRingEnd ℂ) (F u) * cert.feat j u ∂πμ
            = (starRingEnd ℂ) (gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j) := by
          have hfun2 : (fun u => (starRingEnd ℂ) (F u) * cert.feat j u)
              = fun u => (starRingEnd ℂ)
                  ((starRingEnd ℂ) (cert.feat j u) * F u) := by
            funext u
            simp only [starRingEnd_apply, map_mul, star_star]
            ring
          rw [hfun2]
          exact integral_conj
        rw [hIA]
        ring
    _ = ∑' j, ((cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 : ℝ) : ℂ) := by
        refine tsum_congr fun j => ?_
        have hcc : (starRingEnd ℂ) (gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
              * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j
            = ((‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 : ℝ) : ℂ) :=
          (mul_comm _ _).trans
            ((RCLike.mul_conj _).trans (Complex.ofReal_pow _ _).symm)
        calc ((cert.w j : ℝ) : ℂ)
              * ((starRingEnd ℂ) (gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j))
              * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j
            = ((cert.w j : ℝ) : ℂ)
                * ((starRingEnd ℂ) (gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j)
                    * gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j) := by ring
          _ = ((cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 : ℝ) : ℂ) := by
              rw [hcc, ← Complex.ofReal_mul]
    _ = ((∑' j, cert.w j * ‖gramSeriesObs (μG := μG) (ρ := ρ) (β := β) cert F j‖ ^ 2 : ℝ) : ℂ) :=
        (Complex.ofReal_tsum _).symm

include cert in
/-- **Nonnegativity of the pairing at integrable observables**
(the T1-a headline, integrable form): a Gram-series
certificate makes the layer pairing's real part nonnegative
at every integrable observable `F`. -/
theorem pairing_re_nonneg_of_integrable (hF : Integrable F
    (Measure.pi fun _ : LayerLink N => μG)) :
    0 ≤ (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG)).re := by
  rw [pairing_eq_of_integrable (μG := μG) (ρ := ρ) (β := β) cert F hF, Complex.ofReal_re]
  exact tsum_nonneg
    (fun j => mul_nonneg (cert.w_nonneg j)
      (pow_nonneg (norm_nonneg _) _))

include cert in
/-- **The conditional discharge to `LayerKernelPos`.**  A
Gram-series certificate yields `LayerKernelPos μG ρ β` under
the explicit observable-regularity hypothesis that every
gauge-invariant observable is integrable against the product
Haar probability measure.  The hypothesis is the named
obstruction of this module's face in hypothesis form: at
finite seats it is automatic (the pairing is a finite sum);
at a general seat it is exactly the analytic input the
unconditional swap lemma would supply. -/
theorem layerKernelPos_of_integrable_obs
    (hreg : ∀ F : (LayerLink N → G) → ℂ, GaugeInvariantLayerObs F →
      Integrable F (Measure.pi fun _ : LayerLink N => μG)) :
    LayerKernelPos (N := N) μG ρ β := by
  intro F hF
  exact pairing_re_nonneg_of_integrable (μG := μG) (ρ := ρ) (β := β) cert F (hreg F hF)

end LayerGramSeriesCert

end GramSeriesSection

end ThetLogos
