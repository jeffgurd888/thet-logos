/-
# Lattice correlation functions and the Elitzur theorem (Pitch 4, Stage 1a)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-lattice level** — machine-checked theorems
about one fixed finite lattice, exactly the Stage 0 setting of
`ThetLogos.LatticeGauge`, whose devices are consumed unchanged: links
valued in a compact group `G`, the Wilson action `S_β`, the product
Haar measure `configMeasure`, and expectations `gibbsExpect` defined
there as ratios of integrals against that measure.

This is Pitch 4 **Stage 1a** (lattice correlation functions and the
Elitzur vanishing theorem), scoped in §6.2 of
`whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md`. It builds:
(1) the Gibbs probability measure as an actual measure (a normalized
density against `configMeasure`), with Stage 0's ratio-of-integrals
expectation *proved equal* to the integral against this measure;
(2) the expectation algebra for observables; (3) the real covariance
package, including variance nonnegativity and the Cauchy–Schwarz
bound; (4) the **Elitzur theorem**: a gauge-variant observable of the
left-covariant single-link / open-line form has Gibbs expectation
zero at **every** `β`, at general `(G, ρ)` with `ρ` free of nonzero
fixed vectors; (5) β = 0 factorization: at the product Haar measure,
observables depending on disjoint link sets are independent; (6) the
Wilson-loop two-point function as a defined object, with its basic
properties inherited — and **no decay claim of any kind**.

## 0.1 Mandatory clauses (Pitch 4 scoping §8, binding on this module)

**(i) Finite-lattice clause.** Every statement is at fixed finite
`Λ`. No limit is taken or asserted. Link variables, plaquettes,
Wilson loops, and expectations are finite combinatorial objects.

**(ii) Gap clause.** No theorem in this module asserts or implies a
spectral gap, a mass, an exponential decay, or a correlation length.
The word "correlation" here means exactly a Gibbs expectation of a
product of observables on the finite lattice — nothing more. Decay of
correlations is Stage 1c's priced content (XL) and is **not** claimed
here, in either direction.

**(iii) Gauge clause (the Elitzur discipline — this module's
organizing rule).** Correlations are formed **only** for
gauge-invariant observables. Gauge-variant observables appear solely
as the subject of the Elitzur theorem, which proves their expectation
vanishes. There is no gauge fixing anywhere in the module: the
vanishing is forced by the exact gauge invariance of the measure and
the action (Stage 0), not by a gauge choice.

**(iv) RG clause (included early; it binds Stage 2 and later).**
Nothing here is a renormalization-group statement; `β` remains a
bare parameter throughout.

**(v) Standing charter.** **Parts of the official Clay Yang–Mills
statement closed by this module: 0.** The module is scaffolding on
the lattice side of the lattice ↔ continuum pair, at fixed lattice
spacing, with no continuum statement attempted.

## 0.2 What is NOT claimed (Stage 1a fence)

* No reflection positivity (Stage 1b, priced L–XL — the next stage,
  which is why the Gibbs *measure*, not only the ratio device, is
  constructed here: 1b consumes the measure).
* No clustering, no decay, no correlation length, no mass (Stage 1c,
  priced XL).
* No continuum limit, no scaling limit, no Euclidean field theory.
* No statement about `β ≠ 0` factorization: at `β ≠ 0` correlations
  do **not** factor, and nothing in this module suggests they do.
  Factorization is proved at `β = 0` only, where it is the exact
  independence of coordinates under a product measure.
* No interaction with matter, no fermions, no continuum Poincaré.

## 0.3 Devices and disclosed choices

* **The Gibbs measure (device).** `gibbsMeasure σ μG ρ β` is
  `Z⁻¹ • (configMeasure μG).withDensity (density)`, with the
  ℝ≥0-valued density `U ↦ exp(−S_β U)` (`gibbsDensity`) and
  `Z = gibbsPartition σ μG ρ β` the Stage 0 denominator integral.
  It is proved to be a probability measure for **every** real `β`
  (`gibbsPartition_pos` uses `|S_β| ≤ |β|·C`, so no `β ≥ 0`
  hypothesis is needed). The headline connection theorem
  `gibbsExpect_eq_integral` proves Stage 0's ratio definition equal
  to the integral against this measure. Stage 0's `haarProb` is the
  running instantiation, but everything is stated at general
  `(μG, ρ)` with Stage 0's hypotheses.
* **Scalar fields (disclosed per item).** Stage 0's `gibbsExpect`
  is ℂ-valued; the expectation algebra is proved for it in ℂ. The
  real expectation `gibbsExpectR` is *defined* as the integral
  against the Gibbs measure and *proved* equal to the analogous
  real ratio of integrals; the covariance package is real
  (`cov(F,H) = ⟨FH⟩ − ⟨F⟩⟨H⟩`, no conjugate — the real form). The
  compatibility `⟨(F : ℂ)⟩ = (⟨F⟩ : ℂ)` for real `F` is proved.
  Elitzur and the β = 0 factorization are stated in ℂ (Wilson loops
  are ℂ-valued traces).
* **Elitzur's shape.** The general theorem
  (`expectMatrix_eq_zero_of_left_covariant`) covers any measurable
  `Φ : Config → G` satisfying the left-covariance identity
  `Φ (U^{update 1 y h}) = h · Φ U`; the single-link insertion and
  open Wilson lines are corollaries, as is the open three-link
  plaquette path. Plaquette *matrix* entries are **not** Elitzur
  subjects: they are intertwiners, stated and proved as such
  (`expectMatrix_plaquette_intertwines`) — they do not vanish in
  general, and this module never claims they do.
* **Dependence (device).** "`F` depends only on links in `s`" is
  formalized as `DependsOnlyOn F s`: there is a function of the
  restricted configuration `↥s → G` reproducing `F`. Factorization
  is landed in two strengths: the split form (links in `s` versus
  links in `sᶜ`) and, from it, the disjoint-pair form; Wilson loops
  come with a proved support (`loopLinks`), so the two-point
  function at `β = 0` factors for loops with disjoint supports.
  The β = 0 factorization identities carry **no integrability
  hypotheses**: at the level of Bochner integrals they hold for
  arbitrary factor maps `f, h` by the junk-value convention
  (`MeasurePreserving.integral_comp` and `integral_prod_mul` are
  unconditional, and non-integrability makes both sides `0`
  consistently). Integrability enters this module where it is
  genuinely needed (the expectation algebra and covariance, whose
  side conditions are discharged for Wilson loops by boundedness).
* **Instance hypothesis (Elitzur section).** §4 carries a
  `[DecidableEq Λ]` instance hypothesis, needed to form the
  `Function.update` gauge transformations supported at one site.
  The concrete torus sites `Fin 4 → ZMod N` have it (Pi and `ZMod`
  instances), as the instance corollaries there confirm.
* **Not in the root import list.** Like all post-Rung-8 modules,
  this module is verified by targeted build and is *not* added to
  `ThetLogos.lean`'s imports; that wiring is a separate decision,
  unchanged here.

## 0.4 Relation to the literature (orientation only)

The Elitzur theorem is Elitzur's theorem (1975): local gauge
invariance cannot break spontaneously; the expectation of any
gauge-non-invariant quantity vanishes identically. The finite-volume
lattice form proved here is the textbook argument (Haar invariance
forces the expectation to be a fixed vector of the representation;
a fixed-vector-free representation has only the zero fixed vector),
carried out against Stage 0's product Haar measure. β = 0
factorization is the independence of coordinates of a product
measure — the free point of the lattice theory, and the reason
strong-coupling expansions start from factorized expectations.
-/

import ThetLogos.LatticeGauge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The Gibbs probability measure

Stage 0 defined `gibbsExpect` as a ratio of integrals against the
product Haar measure and proved the denominator positive for
`0 ≤ β`. This section constructs the normalized Gibbs **measure**
behind that ratio, for every real `β`, and proves the two devices
define the same expectation. Everything is at Stage 0's general
`(Λ, G, σ, μG, ρ)`; `hρcont` (continuity of `ρ`'s matrix entries) and
`0 < d` are consumed exactly as Stage 0 consumes them. -/

section GibbsMeasure

variable {Λ : Type*} [Fintype Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The Gibbs density as an `ℝ≥0`-valued function:
`U ↦ exp (−S_β U)`. (The `ℝ≥0` form is the one Mathlib's
`integral_withDensity_eq_integral_smul` consumes.) -/
noncomputable def gibbsDensity (β : ℝ) (U : Config Λ G) : ℝ≥0 :=
  ⟨Real.exp (- wilsonAction σ ρ β U), Real.exp_nonneg _⟩

/-- The partition integral: Stage 0's expectation denominator,
`Z = ∫ U, exp (−S_β U) ∂(configMeasure μG)`, named. -/
noncomputable def gibbsPartition (β : ℝ) : ℝ :=
  ∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG)

/-- The Gibbs probability measure at coupling `β`: the normalized
density `exp (−S_β) / Z` against the product Haar measure. -/
noncomputable def gibbsMeasure (β : ℝ) : Measure (Config Λ G) :=
  (ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹ •
    (configMeasure μG).withDensity (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))

/-- The density, coerced to `ℝ≥0∞`, is `ENNReal.ofReal` of the
exponential. -/
theorem gibbsDensity_coe (β : ℝ) (U : Config Λ G) :
    (gibbsDensity σ ρ β U : ℝ≥0∞)
      = ENNReal.ofReal (Real.exp (- wilsonAction σ ρ β U)) :=
  (ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)).symm

/-- The Gibbs density is measurable. -/
theorem measurable_gibbsDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable (gibbsDensity σ ρ β) :=
  Measurable.subtype_mk
    (Real.measurable_exp.comp (measurable_wilsonAction σ ρ hρcont β).neg)

/-- The partition integral is positive for **every** real `β` (the
lower bound `exp (−S_β U) ≥ exp (−|β| · C)` comes from Stage 0's
`wilsonAction_abs_le`, so the `0 ≤ β` hypothesis of Stage 0's
`gibbsDenom_pos` is not needed). -/
theorem gibbsPartition_pos
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    0 < gibbsPartition σ μG ρ β := by
  have hC : ∀ U : Config Λ G,
      Real.exp (- (|β| * (2 * (16 * (Fintype.card Λ : ℝ)))))
        ≤ Real.exp (- wilsonAction σ ρ β U) := by
    intro U
    apply Real.exp_monotone
    have h := wilsonAction_abs_le σ ρ hd β U
    linarith [le_abs_self (wilsonAction σ ρ β U)]
  calc (0 : ℝ) < Real.exp (- (|β| * (2 * (16 * (Fintype.card Λ : ℝ))))) :=
        Real.exp_pos _
    _ = ∫ _U : Config Λ G,
          Real.exp (- (|β| * (2 * (16 * (Fintype.card Λ : ℝ)))))
            ∂(configMeasure μG) := by
        rw [integral_const, Measure.real, measure_univ,
          ENNReal.toReal_one, one_smul]
    _ ≤ ∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) :=
        integral_mono_ae (integrable_const _)
          (integrable_exp_neg_wilsonAction σ μG ρ hρcont hd β)
          (ae_of_all _ hC)
    _ = gibbsPartition σ μG ρ β := rfl

/-- The unnormalized Gibbs density has total mass `Z`. -/
theorem withDensity_gibbs_univ
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    (configMeasure μG).withDensity (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))
        Set.univ
      = ENNReal.ofReal (gibbsPartition σ μG ρ β) := by
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hcongr : (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))
      = fun U => ENNReal.ofReal (Real.exp (- wilsonAction σ ρ β U)) :=
    funext fun U => gibbsDensity_coe σ ρ β U
  rw [hcongr,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_neg_wilsonAction σ μG ρ hρcont hd β)
      (ae_of_all _ fun U => Real.exp_nonneg _)]
  rfl

/-- **The Gibbs measure is a probability measure**, for every
real `β`. -/
theorem isProbabilityMeasure_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    IsProbabilityMeasure (gibbsMeasure σ μG ρ β) := by
  have hZ := gibbsPartition_pos σ μG ρ hρcont hd β
  refine ⟨?_⟩
  show ((ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹
      • (configMeasure μG).withDensity
          (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))) Set.univ = 1
  rw [Measure.smul_apply, withDensity_gibbs_univ σ μG ρ hρcont hd β,
    smul_eq_mul, ENNReal.inv_mul_cancel]
  · exact (ENNReal.ofReal_pos.mpr hZ).ne'
  · exact ENNReal.ofReal_ne_top

/-- **Headline (the campaign's foundation stone).** Stage 0's
ratio-of-integrals expectation *is* the integral against the Gibbs
probability measure, for every observable `F` — both sides vanish
(by the Bochner convention) when `F` is not integrable, so no
integrability hypothesis is needed. -/
theorem gibbsExpect_eq_integral
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℂ) :
    gibbsExpect σ μG ρ β F = ∫ U, F U ∂(gibbsMeasure σ μG ρ β) := by
  have hZ := gibbsPartition_pos σ μG ρ hρcont hd β
  have htoReal : (ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹.toReal
      = (gibbsPartition σ μG ρ β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  have hInt : ∫ U, F U ∂(gibbsMeasure σ μG ρ β)
      = (gibbsPartition σ μG ρ β)⁻¹
        • ∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U
            ∂(configMeasure μG) := by
    show ∫ U, F U ∂((ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹
        • (configMeasure μG).withDensity
          (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))) = _
    rw [integral_smul_measure, htoReal,
      integral_withDensity_eq_integral_smul
        (measurable_gibbsDensity σ ρ hρcont β) F]
    congr 1
  rw [hInt]
  show (∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U
        ∂(configMeasure μG))
      / (gibbsPartition σ μG ρ β : ℂ)
    = (gibbsPartition σ μG ρ β)⁻¹
      • ∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U
          ∂(configMeasure μG)
  rw [div_eq_mul_inv, mul_comm, ← Complex.ofReal_inv, ← Complex.real_smul]

end GibbsMeasure

/-! ## §2. The expectation algebra

For ℂ-valued observables the expectation is Stage 0's `gibbsExpect`,
transported to the Gibbs measure by §1's connection theorem. For
ℝ-valued observables the expectation `gibbsExpectR` is defined
directly as the Gibbs-measure integral and proved equal to the
analogous real ratio of integrals. Bounded measurable observables
are integrable against the Gibbs measure (`Integrable.of_bound`
against a probability measure). -/

section ExpectationAlgebra

variable {Λ : Type*} [Fintype Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The real Gibbs expectation of a real observable: its integral
against the Gibbs probability measure. -/
noncomputable def gibbsExpectR (β : ℝ) (F : Config Λ G → ℝ) : ℝ :=
  ∫ U, F U ∂(gibbsMeasure σ μG ρ β)

/-- The real expectation is the real ratio of integrals (the
`gibbsExpectR` analogue of §1's connection theorem). -/
theorem gibbsExpectR_eq_ratio
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℝ) :
    gibbsExpectR σ μG ρ β F
      = (∫ U, Real.exp (- wilsonAction σ ρ β U) * F U ∂(configMeasure μG))
        / gibbsPartition σ μG ρ β := by
  have hZ := gibbsPartition_pos σ μG ρ hρcont hd β
  have htoReal : (ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹.toReal
      = (gibbsPartition σ μG ρ β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  show ∫ U, F U ∂((ENNReal.ofReal (gibbsPartition σ μG ρ β))⁻¹
      • (configMeasure μG).withDensity
        (fun U => (gibbsDensity σ ρ β U : ℝ≥0∞))) = _
  rw [integral_smul_measure, htoReal,
    integral_withDensity_eq_integral_smul
      (measurable_gibbsDensity σ ρ hρcont β) F,
    div_eq_inv_mul, smul_eq_mul]
  congr 1

/-- `⟨1⟩ = 1` (ℂ form). -/
theorem gibbsExpect_one
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    gibbsExpect σ μG ρ β (fun _ => 1) = 1 := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  rw [gibbsExpect_eq_integral σ μG ρ hρcont hd β, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- `⟨c⟩ = c` for constant observables (ℂ form). -/
theorem gibbsExpect_const
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (c : ℂ) :
    gibbsExpect σ μG ρ β (fun _ => c) = c := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  rw [gibbsExpect_eq_integral σ μG ρ hρcont hd β, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- Linearity of the ℂ expectation (additivity). -/
theorem gibbsExpect_add
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    {F H : Config Λ G → ℂ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β))
    (hH : Integrable H (gibbsMeasure σ μG ρ β)) :
    gibbsExpect σ μG ρ β (fun U => F U + H U)
      = gibbsExpect σ μG ρ β F + gibbsExpect σ μG ρ β H := by
  simp only [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact integral_add hF hH

/-- Constant multiples pull out of the ℂ expectation (left). -/
theorem gibbsExpect_const_mul
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (c : ℂ) {F : Config Λ G → ℂ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β)) :
    gibbsExpect σ μG ρ β (fun U => c * F U)
      = c * gibbsExpect σ μG ρ β F := by
  simp only [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact integral_const_mul c F

/-- Constant multiples pull out of the ℂ expectation (right). -/
theorem gibbsExpect_mul_const
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    {F : Config Λ G → ℂ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β)) (c : ℂ) :
    gibbsExpect σ μG ρ β (fun U => F U * c)
      = gibbsExpect σ μG ρ β F * c := by
  simp only [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact integral_mul_const c F

/-- Finite sums pass through the ℂ expectation. -/
theorem gibbsExpect_finsetSum
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    {ι : Type*} (s : Finset ι) (F : ι → Config Λ G → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i) (gibbsMeasure σ μG ρ β)) :
    gibbsExpect σ μG ρ β (fun U => ∑ i ∈ s, F i U)
      = ∑ i ∈ s, gibbsExpect σ μG ρ β (F i) := by
  simp only [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact integral_finsetSum s hF

/-- Compatibility: the ℂ expectation of a real observable is the
cast of its real expectation. -/
theorem gibbsExpect_ofReal
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℝ) :
    gibbsExpect σ μG ρ β (fun U => (F U : ℂ))
      = (gibbsExpectR σ μG ρ β F : ℂ) := by
  rw [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact integral_ofReal

/-- The norm bound `‖⟨F⟩‖ ≤ ⟨‖F‖⟩` (ℂ expectation against the real
expectation of the pointwise norm). -/
theorem norm_gibbsExpect_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℂ) :
    ‖gibbsExpect σ μG ρ β F‖
      ≤ gibbsExpectR σ μG ρ β (fun U => ‖F U‖) := by
  rw [gibbsExpect_eq_integral σ μG ρ hρcont hd β]
  exact norm_integral_le_integral_norm F

/-- Bounded AE-strongly-measurable observables are integrable
against the Gibbs measure. -/
theorem integrable_gibbsMeasure_of_bounded
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Config Λ G → E)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (C : ℝ) (hC : ∀ U, ‖F U‖ ≤ C) :
    Integrable F (gibbsMeasure σ μG ρ β) := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  exact Integrable.of_bound hF C (ae_of_all _ hC)

/-- `⟨c⟩ = c` for constant real observables. -/
theorem gibbsExpectR_const
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (c : ℝ) :
    gibbsExpectR σ μG ρ β (fun _ => c) = c := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  show ∫ _U : Config Λ G, c ∂(gibbsMeasure σ μG ρ β) = c
  rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul]

/-- Additivity of the real expectation. -/
theorem gibbsExpectR_add (β : ℝ) {F H : Config Λ G → ℝ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β))
    (hH : Integrable H (gibbsMeasure σ μG ρ β)) :
    gibbsExpectR σ μG ρ β (fun U => F U + H U)
      = gibbsExpectR σ μG ρ β F + gibbsExpectR σ μG ρ β H :=
  integral_add hF hH

/-- Subtraction for the real expectation. -/
theorem gibbsExpectR_sub (β : ℝ) {F H : Config Λ G → ℝ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β))
    (hH : Integrable H (gibbsMeasure σ μG ρ β)) :
    gibbsExpectR σ μG ρ β (fun U => F U - H U)
      = gibbsExpectR σ μG ρ β F - gibbsExpectR σ μG ρ β H :=
  integral_sub hF hH

/-- Constant multiples pull out of the real expectation (left). -/
theorem gibbsExpectR_const_mul (β : ℝ) (c : ℝ) {F : Config Λ G → ℝ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β)) :
    gibbsExpectR σ μG ρ β (fun U => c * F U)
      = c * gibbsExpectR σ μG ρ β F :=
  integral_const_mul c F

/-- Constant multiples pull out of the real expectation (right). -/
theorem gibbsExpectR_mul_const (β : ℝ) {F : Config Λ G → ℝ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β)) (c : ℝ) :
    gibbsExpectR σ μG ρ β (fun U => F U * c)
      = gibbsExpectR σ μG ρ β F * c :=
  integral_mul_const c F

/-- Monotonicity of the real expectation. -/
theorem gibbsExpectR_mono (β : ℝ) {F H : Config Λ G → ℝ}
    (hF : Integrable F (gibbsMeasure σ μG ρ β))
    (hH : Integrable H (gibbsMeasure σ μG ρ β))
    (hle : ∀ U, F U ≤ H U) :
    gibbsExpectR σ μG ρ β F ≤ gibbsExpectR σ μG ρ β H :=
  integral_mono hF hH hle

/-- The real expectation of a pointwise nonnegative observable is
nonnegative. -/
theorem gibbsExpectR_nonneg (β : ℝ) (F : Config Λ G → ℝ)
    (hF : ∀ U, 0 ≤ F U) :
    0 ≤ gibbsExpectR σ μG ρ β F :=
  integral_nonneg_of_ae (ae_of_all _ hF)

end ExpectationAlgebra

/-! ## §3. The covariance package (real observables)

`cov(F, H) = ⟨F·H⟩ − ⟨F⟩·⟨H⟩` and `var(F) = cov(F, F)` for the real
Gibbs expectation. Everything is proved from the expectation algebra
of §2 applied to bounded measurable observables (boundedness is what
makes all products integrable against the probability measure). The
Cauchy–Schwarz bound is the discriminant argument on
`var(F + tH) ≥ 0`. No complex covariance is stated: the package is
real, as disclosed in the header. -/

section Covariance

variable {Λ : Type*} [Fintype Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The Gibbs covariance of two real observables. -/
noncomputable def gibbsCov (β : ℝ) (F H : Config Λ G → ℝ) : ℝ :=
  gibbsExpectR σ μG ρ β (fun U => F U * H U)
    - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H

/-- The Gibbs variance of a real observable. -/
noncomputable def gibbsVar (β : ℝ) (F : Config Λ G → ℝ) : ℝ :=
  gibbsCov σ μG ρ β F F

/-- Covariance is symmetric (real case; no hypotheses — the two
sides are expectations of pointwise-equal products). -/
theorem gibbsCov_comm (β : ℝ) (F H : Config Λ G → ℝ) :
    gibbsCov σ μG ρ β F H = gibbsCov σ μG ρ β H F := by
  show gibbsExpectR σ μG ρ β (fun U => F U * H U)
        - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H
      = gibbsExpectR σ μG ρ β (fun U => H U * F U)
        - gibbsExpectR σ μG ρ β H * gibbsExpectR σ μG ρ β F
  congr 1
  · congr 1
    funext U
    exact mul_comm _ _
  · exact mul_comm _ _

/-- The centered form of covariance:
`cov(F, H) = ⟨(F − ⟨F⟩)·(H − ⟨H⟩)⟩`. -/
theorem gibbsCov_centered
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F H : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C)
    (hH : AEStronglyMeasurable H (gibbsMeasure σ μG ρ β))
    (hHb : ∃ C, ∀ U, ‖H U‖ ≤ C) :
    gibbsCov σ μG ρ β F H
      = gibbsExpectR σ μG ρ β
          (fun U => (F U - gibbsExpectR σ μG ρ β F)
            * (H U - gibbsExpectR σ μG ρ β H)) := by
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CH, hCH⟩ := hHb
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  have intF : Integrable F (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β F hF CF hCF
  have intH : Integrable H (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β H hH CH hCH
  have intFH : Integrable (fun U => F U * H U) (gibbsMeasure σ μG ρ β) :=
    intH.bdd_mul hF (ae_of_all _ hCF)
  have hfun : (fun U => (F U - gibbsExpectR σ μG ρ β F)
        * (H U - gibbsExpectR σ μG ρ β H))
      = fun U => ((F U * H U - F U * gibbsExpectR σ μG ρ β H)
          - gibbsExpectR σ μG ρ β F * H U)
        + gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H :=
    funext fun U => by ring
  have hX : Integrable
      (fun U => (F U * H U - F U * gibbsExpectR σ μG ρ β H)
        - gibbsExpectR σ μG ρ β F * H U) (gibbsMeasure σ μG ρ β) :=
    (intFH.sub (intF.mul_const _)).sub (intH.const_mul _)
  have hY : Integrable
      (fun U => F U * H U - F U * gibbsExpectR σ μG ρ β H)
        (gibbsMeasure σ μG ρ β) :=
    intFH.sub (intF.mul_const _)
  have key : gibbsExpectR σ μG ρ β
        (fun U => ((F U * H U - F U * gibbsExpectR σ μG ρ β H)
            - gibbsExpectR σ μG ρ β F * H U)
          + gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H)
      = ((gibbsExpectR σ μG ρ β (fun U => F U * H U)
            - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H)
          - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H)
        + gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H := by
    rw [gibbsExpectR_add σ μG ρ β hX (integrable_const _),
      gibbsExpectR_sub σ μG ρ β hY (intH.const_mul _),
      gibbsExpectR_sub σ μG ρ β intFH (intF.mul_const _),
      gibbsExpectR_mul_const σ μG ρ β intF _,
      gibbsExpectR_const_mul σ μG ρ β _ intH,
      gibbsExpectR_const σ μG ρ hρcont hd β _]
  show gibbsExpectR σ μG ρ β (fun U => F U * H U)
        - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H
      = gibbsExpectR σ μG ρ β
          (fun U => (F U - gibbsExpectR σ μG ρ β F)
            * (H U - gibbsExpectR σ μG ρ β H))
  rw [hfun, key]
  ring

/-- The variance is the expectation of the centered square. -/
theorem gibbsVar_eq_centered_sq
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C) :
    gibbsVar σ μG ρ β F
      = gibbsExpectR σ μG ρ β
          (fun U => (F U - gibbsExpectR σ μG ρ β F) ^ 2) := by
  have h := gibbsCov_centered σ μG ρ hρcont hd β F F hF hFb hF hFb
  show gibbsCov σ μG ρ β F F = _
  rw [h]
  congr 1
  funext U
  rw [pow_two]

/-- **Variance is nonnegative.** -/
theorem gibbsVar_nonneg
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C) :
    0 ≤ gibbsVar σ μG ρ β F := by
  rw [gibbsVar_eq_centered_sq σ μG ρ hρcont hd β F hF hFb]
  exact gibbsExpectR_nonneg σ μG ρ β _ fun U => sq_nonneg _

/-- Covariance against a constant observable vanishes. -/
theorem gibbsCov_const_right
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C) (c : ℝ) :
    gibbsCov σ μG ρ β F (fun _ => c) = 0 := by
  obtain ⟨CF, hCF⟩ := hFb
  have intF : Integrable F (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β F hF CF hCF
  show gibbsExpectR σ μG ρ β (fun U => F U * c)
        - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β (fun _ => c) = 0
  rw [gibbsExpectR_mul_const σ μG ρ β intF c,
    gibbsExpectR_const σ μG ρ hρcont hd β c, sub_self]

/-- The variance of `F + t • H` as a quadratic in `t` (the expansion
the Cauchy–Schwarz discriminant argument consumes). -/
theorem gibbsVar_add_smul
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F H : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C)
    (hH : AEStronglyMeasurable H (gibbsMeasure σ μG ρ β))
    (hHb : ∃ C, ∀ U, ‖H U‖ ≤ C) (t : ℝ) :
    gibbsVar σ μG ρ β (fun U => F U + t * H U)
      = gibbsVar σ μG ρ β F + 2 * t * gibbsCov σ μG ρ β F H
        + t ^ 2 * gibbsVar σ μG ρ β H := by
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CH, hCH⟩ := hHb
  have intF : Integrable F (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β F hF CF hCF
  have intH : Integrable H (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β H hH CH hCH
  have intFF : Integrable (fun U => F U * F U) (gibbsMeasure σ μG ρ β) :=
    intF.bdd_mul hF (ae_of_all _ hCF)
  have intFH : Integrable (fun U => F U * H U) (gibbsMeasure σ μG ρ β) :=
    intH.bdd_mul hF (ae_of_all _ hCF)
  have intHH : Integrable (fun U => H U * H U) (gibbsMeasure σ μG ρ β) :=
    intH.bdd_mul hH (ae_of_all _ hCH)
  have e1 : gibbsExpectR σ μG ρ β (fun U => F U + t * H U)
      = gibbsExpectR σ μG ρ β F + t * gibbsExpectR σ μG ρ β H := by
    rw [gibbsExpectR_add σ μG ρ β intF (intH.const_mul t),
      gibbsExpectR_const_mul σ μG ρ β t intH]
  have e2 : gibbsExpectR σ μG ρ β
        (fun U => (F U + t * H U) * (F U + t * H U))
      = gibbsExpectR σ μG ρ β (fun U => F U * F U)
        + 2 * t * gibbsExpectR σ μG ρ β (fun U => F U * H U)
        + t ^ 2 * gibbsExpectR σ μG ρ β (fun U => H U * H U) := by
    have step1 : gibbsExpectR σ μG ρ β
          (fun U => (F U + t * H U) * (F U + t * H U))
        = gibbsExpectR σ μG ρ β
            (fun U => (F U * F U + (2 * t) * (F U * H U))
              + (t ^ 2) * (H U * H U)) := by
      congr 1
      funext U
      ring
    have step2 : gibbsExpectR σ μG ρ β
          (fun U => (F U * F U + (2 * t) * (F U * H U))
            + (t ^ 2) * (H U * H U))
        = gibbsExpectR σ μG ρ β (fun U => F U * F U + (2 * t) * (F U * H U))
          + gibbsExpectR σ μG ρ β (fun U => (t ^ 2) * (H U * H U)) :=
      gibbsExpectR_add σ μG ρ β (intFF.add (intFH.const_mul _))
        (intHH.const_mul _)
    have step3 : gibbsExpectR σ μG ρ β
          (fun U => F U * F U + (2 * t) * (F U * H U))
        = gibbsExpectR σ μG ρ β (fun U => F U * F U)
          + gibbsExpectR σ μG ρ β (fun U => (2 * t) * (F U * H U)) :=
      gibbsExpectR_add σ μG ρ β intFF (intFH.const_mul _)
    have step4 : gibbsExpectR σ μG ρ β (fun U => (2 * t) * (F U * H U))
        = (2 * t) * gibbsExpectR σ μG ρ β (fun U => F U * H U) :=
      gibbsExpectR_const_mul σ μG ρ β _ intFH
    have step5 : gibbsExpectR σ μG ρ β (fun U => (t ^ 2) * (H U * H U))
        = (t ^ 2) * gibbsExpectR σ μG ρ β (fun U => H U * H U) :=
      gibbsExpectR_const_mul σ μG ρ β _ intHH
    rw [step1, step2, step3, step4, step5]
  show gibbsExpectR σ μG ρ β
        (fun U => (F U + t * H U) * (F U + t * H U))
      - gibbsExpectR σ μG ρ β (fun U => F U + t * H U)
        * gibbsExpectR σ μG ρ β (fun U => F U + t * H U)
    = (gibbsExpectR σ μG ρ β (fun U => F U * F U)
        - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β F)
      + 2 * t * (gibbsExpectR σ μG ρ β (fun U => F U * H U)
        - gibbsExpectR σ μG ρ β F * gibbsExpectR σ μG ρ β H)
      + t ^ 2 * (gibbsExpectR σ μG ρ β (fun U => H U * H U)
        - gibbsExpectR σ μG ρ β H * gibbsExpectR σ μG ρ β H)
  rw [e1, e2]
  ring

/-- The discriminant step, as a standalone real lemma: a quadratic
`A + 2tB + t²D` nonnegative for all `t`, with `A, D ≥ 0`, forces
`B² ≤ A · D`. -/
theorem sq_le_of_forall_quadratic_nonneg {A B D : ℝ} (hA : 0 ≤ A)
    (hD : 0 ≤ D) (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * D) :
    B ^ 2 ≤ A * D := by
  rcases eq_or_lt_of_le hD with rfl | hDpos
  · have hB : B = 0 := by
      by_contra hB
      have h1 := h (-(A + 1) / (2 * B))
      simp only [pow_two, mul_zero, add_zero] at h1
      have h2 : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by
        field_simp
      rw [h2] at h1
      linarith
    rw [hB]
    simp
  · have h1 := h (-B / D)
    have e : A + 2 * (-B / D) * B + (-B / D) ^ 2 * D = A - B ^ 2 / D := by
      field_simp
      ring
    rw [e] at h1
    have hle : B ^ 2 / D ≤ A := by linarith
    rwa [div_le_iff₀ hDpos] at hle

/-- **Cauchy–Schwarz for the Gibbs covariance:**
`cov(F, H)² ≤ var(F) · var(H)`. -/
theorem gibbsCov_sq_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (F H : Config Λ G → ℝ)
    (hF : AEStronglyMeasurable F (gibbsMeasure σ μG ρ β))
    (hFb : ∃ C, ∀ U, ‖F U‖ ≤ C)
    (hH : AEStronglyMeasurable H (gibbsMeasure σ μG ρ β))
    (hHb : ∃ C, ∀ U, ‖H U‖ ≤ C) :
    gibbsCov σ μG ρ β F H ^ 2
      ≤ gibbsVar σ μG ρ β F * gibbsVar σ μG ρ β H := by
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CH, hCH⟩ := hHb
  apply sq_le_of_forall_quadratic_nonneg
    (gibbsVar_nonneg σ μG ρ hρcont hd β F hF ⟨CF, hCF⟩)
    (gibbsVar_nonneg σ μG ρ hρcont hd β H hH ⟨CH, hCH⟩)
  intro t
  have hX : AEStronglyMeasurable (fun U => F U + t * H U)
      (gibbsMeasure σ μG ρ β) :=
    hF.add (hH.const_smul t)
  have hXb : ∃ C, ∀ U, ‖F U + t * H U‖ ≤ C := by
    refine ⟨CF + |t| * CH, fun U => ?_⟩
    calc ‖F U + t * H U‖ ≤ ‖F U‖ + ‖t * H U‖ := norm_add_le _ _
      _ ≤ CF + |t| * CH := by
          apply add_le_add (hCF U)
          have h1 : ‖t * H U‖ = |t| * ‖H U‖ := by
            rw [norm_mul, Real.norm_eq_abs]
          rw [h1]
          exact mul_le_mul_of_nonneg_left (hCH U) (abs_nonneg t)
  have hvar := gibbsVar_nonneg σ μG ρ hρcont hd β
    (fun U => F U + t * H U) hX hXb
  rw [gibbsVar_add_smul σ μG ρ hρcont hd β F H hF ⟨CF, hCF⟩ hH
    ⟨CH, hCH⟩ t] at hvar
  exact hvar

end Covariance

/-! ## §4. The Elitzur theorem

The organizing rule of this module (header §0.1(iii)): correlations
are formed only for gauge-invariant observables; variant ones appear
solely here, as the subject of the vanishing theorem. The proof is
the textbook one, at general `(G, ρ)`: a gauge transformation
supported at one site `y` (the function `Function.update 1 y h`)
multiplies a left-covariant observable's value by `h` on the left,
while the Gibbs expectation is unchanged (exact invariance of the
measure and the action, Stage 0 — no gauge fixing). The expectation
matrix is therefore a fixed point of `ρ` on every column, and the
hypothesis that `ρ` has no nonzero fixed vectors — the same
hypothesis Stage 0's β = 0 theory consumes — forces it to vanish,
at **every** `β`. -/

section Elitzur

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Gibbs expectations are invariant under precomposition with a
gauge transformation (proved on Stage 0's ratio device: the
denominator is observable-independent, and the numerator is
transported by `integral_gaugeAction` plus the exact invariance of
the Wilson action). -/
theorem gibbsExpect_comp_gaugeAction
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (β : ℝ) (g : Λ → G) (F : Config Λ G → ℂ) (hF : Measurable F) :
    gibbsExpect σ μG ρ β (fun U => F (gaugeAction σ g U))
      = gibbsExpect σ μG ρ β F := by
  have hG₀ : AEStronglyMeasurable
      (fun U => (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U)
        (configMeasure μG) :=
    ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_wilsonAction σ ρ hρcont β).neg)).mul hF).aestronglyMeasurable
  have hpt : ∀ U : Config Λ G,
      (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F (gaugeAction σ g U)
        = (fun U => (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U)
            (gaugeAction σ g U) := by
    intro U
    show (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F (gaugeAction σ g U)
      = (Real.exp (- wilsonAction σ ρ β (gaugeAction σ g U)) : ℂ)
        * F (gaugeAction σ g U)
    rw [wilsonAction_gauge_invariant σ ρ hσ g β U]
  have key : (∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ)
        * F (gaugeAction σ g U) ∂(configMeasure μG))
      = ∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U
          ∂(configMeasure μG) := by
    rw [← integral_gaugeAction μG σ g _ hG₀]
    exact integral_congr_ae (ae_of_all _ hpt)
  show (∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ)
        * F (gaugeAction σ g U) ∂(configMeasure μG))
      / ((∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) : ℝ) : ℂ)
    = (∫ U, (Real.exp (- wilsonAction σ ρ β U) : ℂ) * F U
        ∂(configMeasure μG))
      / ((∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) : ℝ) : ℂ)
  rw [key]

/-- Matrix entries of `ρ ∘ Φ` are measurable when `Φ` is. -/
theorem measurable_repMatrix_entry_of_measurable
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (Φ : Config Λ G → G) (hΦ : Measurable Φ) (a b : Fin d) :
    Measurable fun U => repMatrix ρ (Φ U) a b :=
  (measurable_pi_apply b).comp
    ((measurable_pi_apply a).comp (hρcont.measurable.comp hΦ))

/-- Matrix entries of `ρ ∘ Φ` are integrable against the Gibbs
measure (entries of unitary matrices are bounded by `1`). -/
theorem integrable_repMatrix_entry_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ)
    (Φ : Config Λ G → G) (hΦ : Measurable Φ) (a b : Fin d) :
    Integrable (fun U => repMatrix ρ (Φ U) a b) (gibbsMeasure σ μG ρ β) := by
  have hAE : AEStronglyMeasurable (fun U => repMatrix ρ (Φ U) a b)
      (gibbsMeasure σ μG ρ β) :=
    Measurable.aestronglyMeasurable
      (measurable_repMatrix_entry_of_measurable ρ hρcont Φ hΦ a b)
  exact integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β _ hAE 1
    (fun U => abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ (Φ U)) a b)

/-- The expectation matrix of a `G`-valued observable `Φ` in the
representation `ρ`: `E i j = ⟨ρ(Φ U) i j⟩`. -/
noncomputable def expectMatrix (β : ℝ) (Φ : Config Λ G → G) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => gibbsExpect σ μG ρ β (fun U => repMatrix ρ (Φ U) i j)

theorem expectMatrix_apply (β : ℝ) (Φ : Config Λ G → G) (i j : Fin d) :
    expectMatrix σ μG ρ β Φ i j
      = gibbsExpect σ μG ρ β (fun U => repMatrix ρ (Φ U) i j) :=
  rfl

/-- **The Elitzur mechanism, general form.** If `Φ : Config → G` is
measurable and left-covariant under gauge transformations supported
at one site `y` — `Φ (U^{update 1 y h}) = h · Φ U` for all `h` and
`U` — and `ρ` has no nonzero fixed vectors, then the expectation
matrix of `Φ` vanishes identically, at every `β`. -/
theorem expectMatrix_eq_zero_of_left_covariant
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0)
    (β : ℝ) (Φ : Config Λ G → G) (hΦ : Measurable Φ) (y : Λ)
    (hcov : ∀ (h : G) (U : Config Λ G),
      Φ (gaugeAction σ (Function.update (1 : Λ → G) y h) U) = h * Φ U) :
    expectMatrix σ μG ρ β Φ = 0 := by
  have hmeas : ∀ a b, Measurable fun U => repMatrix ρ (Φ U) a b :=
    fun a b => measurable_repMatrix_entry_of_measurable ρ hρcont Φ hΦ a b
  have hint : ∀ a b, Integrable (fun U => repMatrix ρ (Φ U) a b)
      (gibbsMeasure σ μG ρ β) :=
    fun a b => integrable_repMatrix_entry_gibbsMeasure σ μG ρ hρcont hd β
      Φ hΦ a b
  have hId : ∀ h : G, repMatrix ρ h * expectMatrix σ μG ρ β Φ
      = expectMatrix σ μG ρ β Φ := by
    intro h
    ext i j
    have hsum : (∑ k, repMatrix ρ h i k * expectMatrix σ μG ρ β Φ k j)
        = gibbsExpect σ μG ρ β
            (fun U => ∑ k, repMatrix ρ h i k * repMatrix ρ (Φ U) k j) := by
      rw [gibbsExpect_finsetSum σ μG ρ hρcont hd β Finset.univ
          (fun k U => repMatrix ρ h i k * repMatrix ρ (Φ U) k j)
          (fun k _ => (hint k j).const_mul _)]
      apply Finset.sum_congr rfl
      intro k _
      rw [gibbsExpect_const_mul σ μG ρ hρcont hd β _ (hint k j),
        expectMatrix_apply]
    have hstep : (fun U => ∑ k, repMatrix ρ h i k * repMatrix ρ (Φ U) k j)
        = (fun U => repMatrix ρ
            (Φ (gaugeAction σ (Function.update (1 : Λ → G) y h) U)) i j) := by
      funext U
      rw [hcov h U, repMatrix_mul]
      simp only [Matrix.mul_apply]
    rw [Matrix.mul_apply, hsum, hstep]
    exact gibbsExpect_comp_gaugeAction σ μG ρ hρcont hσ β _
      (fun U => repMatrix ρ (Φ U) i j) (hmeas i j)
  ext i j
  have hcol : ∀ h : G, repMatrix ρ h *ᵥ (fun k => expectMatrix σ μG ρ β Φ k j)
      = (fun k => expectMatrix σ μG ρ β Φ k j) := by
    intro h
    funext a
    have h2 : (repMatrix ρ h *ᵥ (fun k => expectMatrix σ μG ρ β Φ k j)) a
        = (repMatrix ρ h * expectMatrix σ μG ρ β Φ) a j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h2, hId h]
  have hzero := hfixed (fun k => expectMatrix σ μG ρ β Φ k j) hcol
  have hEntry := congrFun hzero i
  simpa using hEntry

/-- **ELIZTUR (headline), single-link form.** The Gibbs expectation
of a single link's representation matrix entry vanishes at every
`β`, whenever the link's head site is moved by its own direction's
shift (`σ ℓ.2 ℓ.1 ≠ ℓ.1` — on the torus, for `2 ≤ N`, this always
holds) and `ρ` has no nonzero fixed vectors. -/
theorem elitzur_single_link
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0)
    (β : ℝ) (ℓ : Link Λ) (hne : σ ℓ.2 ℓ.1 ≠ ℓ.1) (i j : Fin d) :
    gibbsExpect σ μG ρ β (fun U => repMatrix ρ (U ℓ) i j) = 0 := by
  have hE : expectMatrix σ μG ρ β (fun U => U ℓ) = 0 :=
    expectMatrix_eq_zero_of_left_covariant σ μG ρ hρcont hd hσ hfixed β
      (fun U => U ℓ) (measurable_pi_apply ℓ) ℓ.1 (fun h U => by
        obtain ⟨x, μ⟩ := ℓ
        show (gaugeAction σ (Function.update (1 : Λ → G) x h) U) (x, μ)
          = h * U (x, μ)
        rw [gaugeAction_apply, Function.update_self,
          Function.update_of_ne hne, Pi.one_apply, inv_one, mul_one])
  have hEntry := Matrix.ext_iff.mpr hE i j
  simpa [expectMatrix] using hEntry

/-- Step factors are measurable. -/
theorem measurable_stepFactor (st : Step) (s : Λ) :
    Measurable fun U : Config Λ G => stepFactor σ U s st := by
  cases st with
  | fwd μ =>
      show Measurable fun U : Config Λ G => U (s, μ)
      exact measurable_pi_apply (s, μ)
  | bwd μ =>
      show Measurable fun U : Config Λ G => (U ((σ μ).symm s, μ))⁻¹
      exact (measurable_pi_apply ((σ μ).symm s, μ)).inv

/-- Loop products are measurable. -/
theorem measurable_loopProd :
    ∀ (steps : List Step) (s : Λ),
      Measurable fun U : Config Λ G => loopProd σ U s steps := by
  intro steps
  induction steps with
  | nil =>
      intro s
      show Measurable fun _U : Config Λ G => (1 : G)
      exact measurable_const
  | cons st t ih =>
      intro s
      show Measurable fun U => stepFactor σ U s st
        * loopProd σ U (stepSite σ s st) t
      exact (measurable_stepFactor σ st s).mul (ih _)

/-- **ELIZTUR (headline), open-Wilson-line form.** A Wilson line
along a non-closed path (`loopEnd σ s steps ≠ s`, in Stage 0's path
formalism) has Gibbs expectation zero at every `β`, under the same
fixed-vector-free hypothesis. -/
theorem elitzur_open_wilson_line
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0)
    (β : ℝ) (s : Λ) (steps : List Step) (hopen : loopEnd σ s steps ≠ s) :
    gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s steps) = 0 := by
  have hzero := expectMatrix_eq_zero_of_left_covariant σ μG ρ hρcont hd
    hσ hfixed β (fun U => loopProd σ U s steps)
    (measurable_loopProd σ steps s) s (fun h U => by
      rw [loopProd_gauge, Function.update_self,
        Function.update_of_ne hopen, Pi.one_apply, inv_one, mul_one])
  have htr : gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s steps)
      = ∑ i, gibbsExpect σ μG ρ β
          (fun U => repMatrix ρ (loopProd σ U s steps) i i) := by
    have hfun : (fun U => wilsonLoop σ ρ U s steps)
        = (fun U => ∑ i, repMatrix ρ (loopProd σ U s steps) i i) :=
      funext fun U => rfl
    rw [hfun]
    exact gibbsExpect_finsetSum σ μG ρ hρcont hd β Finset.univ _
      (fun i _ => integrable_repMatrix_entry_gibbsMeasure σ μG ρ hρcont
        hd β _ (measurable_loopProd σ steps s) i i)
  rw [htr, Finset.sum_eq_zero]
  intro i _
  have hEntry := Matrix.ext_iff.mpr hzero i i
  simpa [expectMatrix] using hEntry

/-- **ELIZTUR corollary: the open three-link plaquette path.** The
path `+μ, +ν, −μ` ends at `σ ν x ≠ x`, so its Wilson line vanishes
at every `β`. (The *closed* plaquette is gauge invariant and is
**not** an Elitzur subject; see the intertwiner statement below.) -/
theorem elitzur_open_plaquette_path
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (hfixed : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0)
    (β : ℝ) (x : Λ) (μ ν : Fin 4) (hνx : σ ν x ≠ x) :
    gibbsExpect σ μG ρ β
        (fun U => wilsonLoop σ ρ U x
          [Step.fwd μ, Step.fwd ν, Step.bwd μ]) = 0 := by
  have hEnd : loopEnd σ x [Step.fwd μ, Step.fwd ν, Step.bwd μ] = σ ν x := by
    rw [loopEnd_cons, loopEnd_cons, loopEnd_cons, loopEnd_nil]
    show (σ μ).symm (σ ν (σ μ x)) = σ ν x
    rw [← hσ μ ν x, Equiv.symm_apply_apply]
  exact elitzur_open_wilson_line σ μG ρ hρcont hd hσ hfixed β x _
    (by rwa [hEnd])

/-- **The contrast (NOT a vanishing theorem).** The expectation
matrix of a plaquette is an *intertwiner*: conjugation by `ρ h`
fixes it, i.e. `ρ h · E = E · ρ h`. Plaquette expectation matrices
do not vanish in general — Stage 0's β = 0 value `tr P` is the
standing example — and this module never claims they do. -/
theorem expectMatrix_plaquette_intertwines
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (β : ℝ) (x : Λ) (μ ν : Fin 4) (h : G) :
    repMatrix ρ h * expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν)
      = expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν)
        * repMatrix ρ h := by
  have hE : expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν)
      = repMatrix ρ h * expectMatrix σ μG ρ β
          (fun U => plaquette σ U x μ ν) * repMatrix ρ h⁻¹ := by
    ext i j
    have hmeas : Measurable fun U => repMatrix ρ (plaquette σ U x μ ν) i j :=
      measurable_repMatrix_plaquette_entry σ ρ hρcont x μ ν i j
    have hinv : gibbsExpect σ μG ρ β
          (fun U => repMatrix ρ (plaquette σ U x μ ν) i j)
        = gibbsExpect σ μG ρ β (fun U => repMatrix ρ
            (plaquette σ (gaugeAction σ (fun _ => h) U) x μ ν) i j) :=
      (gibbsExpect_comp_gaugeAction σ μG ρ hρcont hσ β (fun _ => h) _
        hmeas).symm
    have hfun : (fun U => repMatrix ρ
          (plaquette σ (gaugeAction σ (fun _ => h) U) x μ ν) i j)
        = (fun U => ∑ l, (∑ k, repMatrix ρ h i k
            * repMatrix ρ (plaquette σ U x μ ν) k l)
            * repMatrix ρ h⁻¹ l j) := by
      funext U
      rw [plaquette_gauge σ hσ (fun _ => h) U x μ ν, repMatrix_mul,
        repMatrix_mul]
      simp only [Matrix.mul_apply]
    have hInt : ∀ k l, Integrable
        (fun U => repMatrix ρ h i k
          * repMatrix ρ (plaquette σ U x μ ν) k l)
          (gibbsMeasure σ μG ρ β) :=
      fun k l => (integrable_repMatrix_entry_gibbsMeasure σ μG ρ hρcont
        hd β _ (measurable_plaquette σ x μ ν) k l).const_mul _
    have stepA : gibbsExpect σ μG ρ β
          (fun U => ∑ l, (∑ k, repMatrix ρ h i k
              * repMatrix ρ (plaquette σ U x μ ν) k l)
            * repMatrix ρ h⁻¹ l j)
        = ∑ l, (∑ k, repMatrix ρ h i k
            * expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν) k l)
            * repMatrix ρ h⁻¹ l j := by
      rw [gibbsExpect_finsetSum σ μG ρ hρcont hd β Finset.univ _
        (fun l _ => (integrable_finsetSum Finset.univ
          fun k _ => hInt k l).mul_const _)]
      apply Finset.sum_congr rfl
      intro l _
      rw [gibbsExpect_mul_const σ μG ρ hρcont hd β
          (integrable_finsetSum Finset.univ fun k _ => hInt k l) _,
        gibbsExpect_finsetSum σ μG ρ hρcont hd β Finset.univ _
          (fun k _ => hInt k l)]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [gibbsExpect_const_mul σ μG ρ hρcont hd β _
        (integrable_repMatrix_entry_gibbsMeasure σ μG ρ hρcont hd β _
          (measurable_plaquette σ x μ ν) k l), expectMatrix_apply]
    rw [expectMatrix_apply, hinv, hfun, stepA]
    simp only [Matrix.mul_apply]
  calc repMatrix ρ h * expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν)
      = (repMatrix ρ h * expectMatrix σ μG ρ β
            (fun U => plaquette σ U x μ ν) * repMatrix ρ h⁻¹)
          * repMatrix ρ h := by
        rw [Matrix.mul_assoc, ← repMatrix_mul, inv_mul_cancel,
          repMatrix_one, Matrix.mul_one]
    _ = expectMatrix σ μG ρ β (fun U => plaquette σ U x μ ν)
          * repMatrix ρ h := by
        rw [← hE]

end Elitzur

section ElitzurInstances

/-- Elitzur on the concrete torus, circle fundamental
representation: every single-link expectation vanishes at every
`β` (for `2 ≤ N` the torus shifts move every site). -/
theorem elitzur_circle_torus (N : ℕ) [NeZero N] (hN : 2 ≤ N) (β : ℝ)
    (x : Fin 4 → ZMod N) (μ : Fin 4) (i j : Fin 1) :
    gibbsExpect (torusShift N) (haarProb Circle) circleRep β
        (fun U => repMatrix circleRep (U (x, μ)) i j) = 0 :=
  elitzur_single_link (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous zero_lt_one (torusShift_comm N)
    circleRep_no_fixed β (x, μ) (torusShift_ne_self N hN μ x) i j

/-- Elitzur on the concrete torus, identity representation of the
full unitary group. -/
theorem elitzur_unitary_torus (d N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (hd : 0 < d) (β : ℝ) (x : Fin 4 → ZMod N) (μ : Fin 4)
    (i j : Fin d) :
    gibbsExpect (torusShift N)
        (haarProb ↥(Matrix.unitaryGroup (Fin d) ℂ)) (unitaryRep d) β
        (fun U => repMatrix (unitaryRep d) (U (x, μ)) i j) = 0 :=
  elitzur_single_link (torusShift N) _ (unitaryRep d)
    (unitaryRep_continuous d) hd (torusShift_comm N)
    (unitaryRep_no_fixed d) β (x, μ) (torusShift_ne_self N hN μ x) i j

end ElitzurInstances

/-! ## §5. β = 0 factorization (independence at the product measure)

At `β = 0` the Gibbs measure is the product Haar measure itself, and
coordinates are independent: an observable depending only on links
in `s` and one depending only on links in `sᶜ` factor. This section
first proves the general product-measure facts (splitting the
configuration space `(ι → G)` as `(↥s → G) × (↥sᶜ → G)` via
`MeasurableEquiv.piFinsetUnion` plus the index transport
`↥(s ∪ sᶜ) ≃ ι`), then transports them to `gibbsExpect` at `β = 0`
through Stage 0's `gibbsExpect_zero`. **Nothing here is asserted at
`β ≠ 0`** — at nonzero coupling the action couples the links and
factorization fails; the module claims independence exactly where
it is true: at the free point. -/

section PiFactorization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]

/-- The index equiv `↥(s ∪ sᶜ) ≃ ι` (the union of a finset and its
complement is everything). -/
def finsetUnionComplEquiv (s : Finset ι) : ↥(s ∪ sᶜ) ≃ ι :=
  ⟨fun x => x.1, fun i => ⟨i, by rw [Finset.union_compl]; exact Finset.mem_univ i⟩,
    fun x => Subtype.ext rfl, fun _ => rfl⟩

/-- The coordinate-splitting measurable equiv: a configuration is
the pair of its restrictions to `s` and to `sᶜ`. -/
noncomputable def splitEquiv (s : Finset ι) :
    (ι → G) ≃ᵐ ((↥s → G) × (↥sᶜ → G)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => G)
      (finsetUnionComplEquiv s)).symm.trans
    (MeasurableEquiv.piFinsetUnion (fun _ : ι => G) disjoint_compl_right).symm

/-- The splitting equiv preserves the product measure. -/
theorem measurePreserving_splitEquiv (s : Finset ι) :
    MeasurePreserving (splitEquiv s) (Measure.pi fun _ : ι => μG)
      ((Measure.pi fun _ : ↥s => μG).prod (Measure.pi fun _ : ↥sᶜ => μG)) :=
  (measurePreserving_piFinsetUnion disjoint_compl_right
    (fun _ : ι => μG)).symm.comp
    (measurePreserving_piCongrLeft (fun _ : ι => μG)
      (finsetUnionComplEquiv s)).symm

theorem splitEquiv_fst (s : Finset ι) (U : ι → G) :
    (splitEquiv s U).1 = fun ℓ : ↥s => U ℓ.1 := by
  funext ℓ
  rfl

theorem splitEquiv_snd (s : Finset ι) (U : ι → G) :
    (splitEquiv s U).2 = fun ℓ : ↥sᶜ => U ℓ.1 := by
  funext ℓ
  rfl

/-- Product observables factor over a coordinate split (the Fubini
content of independence). No integrability hypothesis: the identity
holds for arbitrary factors by the Bochner junk-value convention
(`MeasurePreserving.integral_comp` and `integral_prod_mul` are
unconditional). -/
theorem integral_pi_split_mul (s : Finset ι) (f : (↥s → G) → ℂ)
    (h : (↥sᶜ → G) → ℂ) :
    ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1) * h (fun ℓ : ↥sᶜ => U ℓ.1)
        ∂(Measure.pi fun _ : ι => μG)
      = (∫ v, f v ∂(Measure.pi fun _ : ↥s => μG))
        * (∫ w, h w ∂(Measure.pi fun _ : ↥sᶜ => μG)) := by
  have step : ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1)
        * h (fun ℓ : ↥sᶜ => U ℓ.1) ∂(Measure.pi fun _ : ι => μG)
      = ∫ z : (↥s → G) × (↥sᶜ → G), f z.1 * h z.2
          ∂((Measure.pi fun _ : ↥s => μG).prod
            (Measure.pi fun _ : ↥sᶜ => μG)) := by
    rw [← (measurePreserving_splitEquiv μG s).integral_comp
      (splitEquiv s).measurableEmbedding]
    apply integral_congr_ae
    filter_upwards with U
    show f (fun ℓ : ↥s => U ℓ.1) * h (fun ℓ : ↥sᶜ => U ℓ.1)
      = f (splitEquiv s U).1 * h (splitEquiv s U).2
    rw [splitEquiv_fst, splitEquiv_snd]
  rw [step, integral_prod_mul]

/-- Marginals: an observable depending only on the coordinates in
`s` integrates over the full product as it does over the
sub-product. -/
theorem integral_pi_restrict (s : Finset ι) (f : (↥s → G) → ℂ) :
    ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1) ∂(Measure.pi fun _ : ι => μG)
      = ∫ v, f v ∂(Measure.pi fun _ : ↥s => μG) := by
  have step : ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1)
        ∂(Measure.pi fun _ : ι => μG)
      = ∫ z : (↥s → G) × (↥sᶜ → G), f z.1
          ∂((Measure.pi fun _ : ↥s => μG).prod
            (Measure.pi fun _ : ↥sᶜ => μG)) := by
    rw [← (measurePreserving_splitEquiv μG s).integral_comp
      (splitEquiv s).measurableEmbedding]
    apply integral_congr_ae
    filter_upwards with U
    show f (fun ℓ : ↥s => U ℓ.1) = f (splitEquiv s U).1
    rw [splitEquiv_fst]
  rw [step]
  have h1 : ∫ z : (↥s → G) × (↥sᶜ → G), f z.1
        ∂((Measure.pi fun _ : ↥s => μG).prod (Measure.pi fun _ : ↥sᶜ => μG))
      = (∫ v, f v ∂(Measure.pi fun _ : ↥s => μG))
        * (∫ _w : ↥sᶜ → G, (1 : ℂ) ∂(Measure.pi fun _ : ↥sᶜ => μG)) := by
    rw [← integral_prod_mul f (fun _ => (1 : ℂ))]
    apply integral_congr_ae
    filter_upwards with z
    exact (mul_one (f z.1)).symm
  rw [h1, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, mul_one]

end PiFactorization

section BetaZero

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- "`F` depends only on the links in `s`": some function of the
restricted configuration reproduces `F`. (Disclosed device, header
§0.3.) -/
def DependsOnlyOn (F : Config Λ G → ℂ) (s : Finset (Link Λ)) : Prop :=
  ∃ f : (↥s → G) → ℂ, ∀ U, F U = f (fun ℓ : ↥s => U ℓ.1)

/-- At `β = 0`, the expectation of an `s`-dependent observable is
its integral over the sub-product. -/
theorem gibbsExpect_zero_of_dependsOnlyOn
    (F : Config Λ G → ℂ) (s : Finset (Link Λ)) (f : (↥s → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥s => U ℓ.1)) :
    gibbsExpect σ μG ρ 0 F = ∫ v, f v ∂(Measure.pi fun _ : ↥s => μG) := by
  rw [gibbsExpect_zero]
  have h2 : ∫ U, F U ∂(configMeasure μG)
      = ∫ U, f (fun ℓ : ↥s => U ℓ.1) ∂(configMeasure μG) :=
    integral_congr_ae (ae_of_all _ hF)
  rw [h2]
  exact integral_pi_restrict μG s f

/-- **β = 0 factorization (split form).** Observables depending on
complementary link sets are independent at `β = 0`. -/
theorem gibbsExpect_zero_mul_of_compl_dependsOnlyOn
    (F H : Config Λ G → ℂ) (s : Finset (Link Λ))
    (f : (↥s → G) → ℂ) (h : (↥sᶜ → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥s => U ℓ.1))
    (hH : ∀ U, H U = h (fun ℓ : ↥sᶜ => U ℓ.1)) :
    gibbsExpect σ μG ρ 0 (fun U => F U * H U)
      = gibbsExpect σ μG ρ 0 F * gibbsExpect σ μG ρ 0 H := by
  rw [gibbsExpect_zero σ μG ρ (fun U => F U * H U),
    gibbsExpect_zero σ μG ρ F, gibbsExpect_zero σ μG ρ H]
  have e1 : ∫ U, F U * H U ∂(configMeasure μG)
      = ∫ U, f (fun ℓ : ↥s => U ℓ.1) * h (fun ℓ : ↥sᶜ => U ℓ.1)
          ∂(configMeasure μG) :=
    integral_congr_ae (ae_of_all _ fun U => by
      show F U * H U = f (fun ℓ : ↥s => U ℓ.1)
        * h (fun ℓ : ↥sᶜ => U ℓ.1)
      rw [hF U, hH U])
  have e2 : ∫ U, F U ∂(configMeasure μG)
      = ∫ v, f v ∂(Measure.pi fun _ : ↥s => μG) :=
    (integral_congr_ae (ae_of_all _ hF)).trans
      (integral_pi_restrict μG s f)
  have e3 : ∫ U, H U ∂(configMeasure μG)
      = ∫ w, h w ∂(Measure.pi fun _ : ↥sᶜ => μG) :=
    (integral_congr_ae (ae_of_all _ hH)).trans
      (integral_pi_restrict μG sᶜ h)
  rw [e1, e2, e3]
  exact integral_pi_split_mul μG s f h

end BetaZero

section BetaZeroDisjoint

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **β = 0 factorization (disjoint form).** If `F` factors through
the links in `s₁` and `H` through the links in `s₂`, with
`s₁ ∩ s₂ = ∅`, then `⟨F · H⟩₀ = ⟨F⟩₀ · ⟨H⟩₀`. Proof: `H` also
factors through the complement of `s₁` (compose its factor map with
the inclusion `s₂ ↪ s₁ᶜ`), reducing to the split form. Like the
split form, the identity is unconditional. -/
theorem gibbsExpect_zero_mul_of_disjoint_dependsOnlyOn
    (F H : Config Λ G → ℂ) (s₁ s₂ : Finset (Link Λ))
    (hdisj : Disjoint s₁ s₂)
    (f₁ : (↥s₁ → G) → ℂ) (f₂ : (↥s₂ → G) → ℂ)
    (hF : ∀ U, F U = f₁ (fun ℓ : ↥s₁ => U ℓ.1))
    (hH : ∀ U, H U = f₂ (fun ℓ : ↥s₂ => U ℓ.1)) :
    gibbsExpect σ μG ρ 0 (fun U => F U * H U)
      = gibbsExpect σ μG ρ 0 F * gibbsExpect σ μG ρ 0 H := by
  have hmem : ∀ ℓ : ↥s₂, ℓ.1 ∈ s₁ᶜ := fun ℓ =>
    Finset.mem_compl.mpr (Finset.disjoint_left.mp hdisj.symm ℓ.2)
  apply gibbsExpect_zero_mul_of_compl_dependsOnlyOn σ μG ρ F H s₁ f₁
    (fun w : (↥s₁ᶜ → G) => f₂ (fun ℓ : ↥s₂ => w ⟨ℓ.1, hmem ℓ⟩)) hF
  intro U
  rw [hH U]

/-- **β = 0 factorization (disjoint form, `DependsOnlyOn`
packaging).** -/
theorem gibbsExpect_zero_mul_of_disjoint
    (F H : Config Λ G → ℂ) (s₁ s₂ : Finset (Link Λ))
    (hdisj : Disjoint s₁ s₂) (hF : DependsOnlyOn F s₁)
    (hH : DependsOnlyOn H s₂) :
    gibbsExpect σ μG ρ 0 (fun U => F U * H U)
      = gibbsExpect σ μG ρ 0 F * gibbsExpect σ μG ρ 0 H := by
  obtain ⟨f₁, hf₁⟩ := hF
  obtain ⟨f₂, hf₂⟩ := hH
  exact gibbsExpect_zero_mul_of_disjoint_dependsOnlyOn σ μG ρ F H s₁ s₂
    hdisj f₁ f₂ hf₁ hf₂

end BetaZeroDisjoint

/-! ## §6. Wilson-loop two-point functions (objects only)

For two closed loops the product observable is gauge invariant
(Stage 0), so the two-point function `⟨W_{C₁} W_{C₂}⟩_β` is a
legitimate correlation in the Elitzur discipline. This section
defines it, proves symmetry, gauge invariance of the integrand, a
norm bound at every `β`, and — the only factorization asserted —
the `β = 0` factorization for loops with DISJOINT link support,
with its corollary that the connected two-point function vanishes
at `β = 0` on disjoint supports. **No decay, clustering, or
correlation-length statement is made or implied at any `β`** (that
is Stage 1c, priced XL in §6.2 of the scoping draft); "separation"
in this module means exactly disjointness of finite link supports. -/

section WilsonTwoPoint

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The set of links a path reads: the link of each forward step,
and the link of each backward step (read against its orientation).
This is the finite combinatorial support of the path's observables —
the only notion of "support" or "separation" in this module. -/
def loopLinks : Λ → List Step → Finset (Link Λ)
  | _, [] => ∅
  | s, (Step.fwd μ) :: t => insert (s, μ) (loopLinks (σ μ s) t)
  | s, (Step.bwd μ) :: t => insert ((σ μ).symm s, μ)
      (loopLinks ((σ μ).symm s) t)

/-- The ordered product along a path depends only on the links in
`loopLinks`. -/
theorem loopProd_eq_of_agree (U V : Config Λ G) :
    ∀ (s : Λ) (steps : List Step),
      (∀ ℓ ∈ loopLinks σ s steps, U ℓ = V ℓ) →
      loopProd σ U s steps = loopProd σ V s steps := by
  intro s steps
  induction steps generalizing s with
  | nil => intro _; rfl
  | cons st t ih =>
    intro h
    cases st with
    | fwd μ =>
      have h1 : U (s, μ) = V (s, μ) :=
        h (s, μ) (show (s, μ) ∈ insert (s, μ) (loopLinks σ (σ μ s) t)
          from Finset.mem_insert_self _ _)
      have h2 : ∀ ℓ ∈ loopLinks σ (stepSite σ s (Step.fwd μ)) t,
          U ℓ = V ℓ :=
        fun ℓ hℓ => h ℓ (show ℓ ∈ insert (s, μ) (loopLinks σ (σ μ s) t)
          from Finset.mem_insert_of_mem hℓ)
      rw [loopProd_cons, loopProd_cons, ih _ h2]
      show U (s, μ) * _ = V (s, μ) * _
      rw [h1]
    | bwd μ =>
      have h1 : U ((σ μ).symm s, μ) = V ((σ μ).symm s, μ) :=
        h ((σ μ).symm s, μ)
          (show ((σ μ).symm s, μ) ∈ insert ((σ μ).symm s, μ)
            (loopLinks σ ((σ μ).symm s) t) from Finset.mem_insert_self _ _)
      have h2 : ∀ ℓ ∈ loopLinks σ (stepSite σ s (Step.bwd μ)) t,
          U ℓ = V ℓ :=
        fun ℓ hℓ => h ℓ
          (show ℓ ∈ insert ((σ μ).symm s, μ)
            (loopLinks σ ((σ μ).symm s) t) from Finset.mem_insert_of_mem hℓ)
      rw [loopProd_cons, loopProd_cons, ih _ h2]
      show (U ((σ μ).symm s, μ))⁻¹ * _ = (V ((σ μ).symm s, μ))⁻¹ * _
      rw [h1]

/-- A Wilson loop depends only on its path's link support. -/
theorem wilsonLoop_dependsOnlyOn (s : Λ) (steps : List Step) :
    DependsOnlyOn (fun U => wilsonLoop σ ρ U s steps)
      (loopLinks σ s steps) := by
  classical
  refine ⟨fun w => wilsonLoop σ ρ
    (fun ℓ => if hℓ : ℓ ∈ loopLinks σ s steps then w ⟨ℓ, hℓ⟩ else 1)
    s steps, fun U => ?_⟩
  have hprod : loopProd σ U s steps
      = loopProd σ (fun ℓ => if hℓ : ℓ ∈ loopLinks σ s steps
          then (fun ℓ' : ↥(loopLinks σ s steps) => U ℓ'.1) ⟨ℓ, hℓ⟩
          else 1) s steps :=
    loopProd_eq_of_agree σ U _ s steps (fun ℓ hℓ => by simp [hℓ])
  show wilsonLoop σ ρ U s steps
    = wilsonLoop σ ρ (fun ℓ => if hℓ : ℓ ∈ loopLinks σ s steps
        then (fun ℓ' : ↥(loopLinks σ s steps) => U ℓ'.1) ⟨ℓ, hℓ⟩
        else 1) s steps
  unfold wilsonLoop
  rw [hprod]

/-- Entries of the represented ordered product along a path are
measurable: inductively, products of step-factor entries, whose
measurability is the single-link entry measurability (forward) and
its conjugate (backward, via the unitary star). -/
theorem measurable_loopProd_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (s : Λ) (steps : List Step) (i j : Fin d) :
    Measurable fun U => repMatrix ρ (loopProd σ U s steps) i j := by
  induction steps generalizing s i j with
  | nil =>
    simp only [loopProd_nil, repMatrix_one]
    exact measurable_const
  | cons st t ih =>
    have hfac : ∀ a b, Measurable
        fun U => repMatrix ρ (stepFactor σ U s st) a b := by
      cases st with
      | fwd μ =>
        exact fun a b => measurable_repMatrix_entry_of_measurable
          ρ hρcont _ (measurable_pi_apply (s, μ)) a b
      | bwd μ =>
        intro a b
        have e1 : ∀ U : Config Λ G,
            repMatrix ρ (stepFactor σ U s (Step.bwd μ))
              = star (repMatrix ρ (U ((σ μ).symm s, μ))) := by
          intro U
          show (ρ ((U ((σ μ).symm s, μ))⁻¹)).1
            = star (ρ (U ((σ μ).symm s, μ))).1
          rw [map_inv, unitary_coe_inv]
        have hfun : (fun U => repMatrix ρ (stepFactor σ U s (Step.bwd μ)) a b)
            = fun U => star (repMatrix ρ (U ((σ μ).symm s, μ)) b a) := by
          funext U
          rw [e1 U, Matrix.star_apply]
        rw [hfun]
        exact continuous_star.measurable.comp
          (measurable_repMatrix_entry_of_measurable ρ hρcont _
            (measurable_pi_apply _) b a)
    have hprod : (fun U => repMatrix ρ (loopProd σ U s (st :: t)) i j)
        = fun U => ∑ k, repMatrix ρ (stepFactor σ U s st) i k
            * repMatrix ρ (loopProd σ U (stepSite σ s st) t) k j := by
      funext U
      rw [loopProd_cons, repMatrix_mul, Matrix.mul_apply]
    rw [hprod]
    exact Finset.measurable_sum _ fun k _ => (hfac i k).mul (ih _ k j)

/-- Wilson loops are measurable observables. -/
theorem measurable_wilsonLoop
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (s : Λ) (steps : List Step) :
    Measurable fun U => wilsonLoop σ ρ U s steps := by
  unfold wilsonLoop Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun i _ =>
    measurable_loopProd_entry σ ρ hρcont s steps i i

/-- The real part of a Wilson loop is a measurable real
observable. -/
theorem measurable_wilsonLoop_re
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (s : Λ) (steps : List Step) :
    Measurable fun U => (wilsonLoop σ ρ U s steps).re :=
  Complex.continuous_re.measurable.comp
    (measurable_wilsonLoop σ ρ hρcont s steps)

/-- A Wilson loop is bounded by the representation dimension:
`|W_C| ≤ d` (trace of a unitary). -/
theorem norm_wilsonLoop_le (hd : 0 < d) (U : Config Λ G) (s : Λ)
    (steps : List Step) : ‖wilsonLoop σ ρ U s steps‖ ≤ (d : ℝ) := by
  unfold wilsonLoop Matrix.trace Matrix.diag
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) i i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

/-- Pointwise bound for the real part of a Wilson loop. -/
theorem norm_wilsonLoop_re_le (hd : 0 < d) (U : Config Λ G) (s : Λ)
    (steps : List Step) :
    ‖(wilsonLoop σ ρ U s steps).re‖ ≤ (d : ℝ) := by
  rw [Real.norm_eq_abs]
  exact le_trans (Complex.abs_re_le_norm _)
    (norm_wilsonLoop_le σ ρ hd U s steps)

/-- Wilson loops are Gibbs-integrable at every `β` (bounded
measurable on a probability space). -/
theorem integrable_wilsonLoop_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (s : Λ) (steps : List Step) :
    Integrable (fun U => wilsonLoop σ ρ U s steps)
      (gibbsMeasure σ μG ρ β) :=
  integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β _
    (measurable_wilsonLoop σ ρ hρcont s steps).aestronglyMeasurable
    (d : ℝ) (fun U => norm_wilsonLoop_le σ ρ hd U s steps)

/-- The real part of a Wilson loop is a real Gibbs-integrable
observable at every `β` — so the real covariance package of §3
applies to Wilson loops verbatim. -/
theorem integrable_wilsonLoop_re_gibbsMeasure
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (s : Λ) (steps : List Step) :
    Integrable (fun U => (wilsonLoop σ ρ U s steps).re)
      (gibbsMeasure σ μG ρ β) :=
  integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β _
    (measurable_wilsonLoop_re σ ρ hρcont s steps).aestronglyMeasurable
    (d : ℝ) (fun U => norm_wilsonLoop_re_le σ ρ hd U s steps)

/-- **The Wilson-loop two-point function** `⟨W_{C₁} · W_{C₂}⟩_β`, as
an object. Defined for arbitrary paths (the integrand is
gauge invariant when both paths are closed — see
`wilsonTwoPoint_integrand_gauge_invariant`). No decay or clustering
property is asserted. -/
noncomputable def wilsonTwoPoint (β : ℝ) (s₁ : Λ) (steps₁ : List Step)
    (s₂ : Λ) (steps₂ : List Step) : ℂ :=
  gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s₁ steps₁
    * wilsonLoop σ ρ U s₂ steps₂)

/-- The two-point function is symmetric in its two loops. -/
theorem wilsonTwoPoint_symm (β : ℝ) (s₁ : Λ) (steps₁ : List Step)
    (s₂ : Λ) (steps₂ : List Step) :
    wilsonTwoPoint σ μG ρ β s₁ steps₁ s₂ steps₂
      = wilsonTwoPoint σ μG ρ β s₂ steps₂ s₁ steps₁ := by
  unfold wilsonTwoPoint
  congr 1
  funext U
  exact mul_comm _ _

/-- For two *closed* loops, the two-point integrand is gauge
invariant: the two-point function is a correlation of
gauge-invariant observables, as the Elitzur discipline requires. -/
theorem wilsonTwoPoint_integrand_gauge_invariant (g : Λ → G)
    (U : Config Λ G) (s₁ : Λ) (steps₁ : List Step)
    (h₁ : loopEnd σ s₁ steps₁ = s₁) (s₂ : Λ) (steps₂ : List Step)
    (h₂ : loopEnd σ s₂ steps₂ = s₂) :
    wilsonLoop σ ρ (gaugeAction σ g U) s₁ steps₁
        * wilsonLoop σ ρ (gaugeAction σ g U) s₂ steps₂
      = wilsonLoop σ ρ U s₁ steps₁ * wilsonLoop σ ρ U s₂ steps₂ := by
  rw [wilsonLoop_gauge_invariant σ ρ g U s₁ steps₁ h₁,
    wilsonLoop_gauge_invariant σ ρ g U s₂ steps₂ h₂]

/-- The two-point function is bounded at every `β`:
`|⟨W_{C₁} W_{C₂}⟩_β| ≤ d²`. -/
theorem norm_wilsonTwoPoint_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (s₁ : Λ) (steps₁ : List Step) (s₂ : Λ)
    (steps₂ : List Step) :
    ‖wilsonTwoPoint σ μG ρ β s₁ steps₁ s₂ steps₂‖ ≤ (d : ℝ) ^ 2 := by
  haveI := isProbabilityMeasure_gibbsMeasure σ μG ρ hρcont hd β
  have hnormMeas : Measurable
      fun U => ‖wilsonLoop σ ρ U s₁ steps₁
        * wilsonLoop σ ρ U s₂ steps₂‖ :=
    ((measurable_wilsonLoop σ ρ hρcont s₁ steps₁).mul
      (measurable_wilsonLoop σ ρ hρcont s₂ steps₂)).norm
  have hIntNorm : Integrable
      (fun U => ‖wilsonLoop σ ρ U s₁ steps₁
        * wilsonLoop σ ρ U s₂ steps₂‖) (gibbsMeasure σ μG ρ β) :=
    integrable_gibbsMeasure_of_bounded σ μG ρ hρcont hd β _
      (Measurable.aestronglyMeasurable hnormMeas)
      ((d : ℝ) ^ 2) (fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul,
          sq]
        exact mul_le_mul (norm_wilsonLoop_le σ ρ hd U s₁ steps₁)
          (norm_wilsonLoop_le σ ρ hd U s₂ steps₂) (norm_nonneg _)
          (by positivity))
  have step1 : ‖gibbsExpect σ μG ρ β
        (fun U => wilsonLoop σ ρ U s₁ steps₁
          * wilsonLoop σ ρ U s₂ steps₂)‖
      ≤ gibbsExpectR σ μG ρ β
          (fun U => ‖wilsonLoop σ ρ U s₁ steps₁
            * wilsonLoop σ ρ U s₂ steps₂‖) :=
    norm_gibbsExpect_le σ μG ρ hρcont hd β _
  have step2 : gibbsExpectR σ μG ρ β
        (fun U => ‖wilsonLoop σ ρ U s₁ steps₁
          * wilsonLoop σ ρ U s₂ steps₂‖)
      ≤ gibbsExpectR σ μG ρ β (fun _ => (d : ℝ) ^ 2) :=
    gibbsExpectR_mono σ μG ρ β hIntNorm (integrable_const _) (fun U => by
      rw [norm_mul, sq]
      exact mul_le_mul (norm_wilsonLoop_le σ ρ hd U s₁ steps₁)
        (norm_wilsonLoop_le σ ρ hd U s₂ steps₂) (norm_nonneg _)
        (by positivity))
  unfold wilsonTwoPoint
  exact le_trans step1 (le_trans step2
    (le_of_eq (gibbsExpectR_const σ μG ρ hρcont hd β ((d : ℝ) ^ 2))))

/-- **β = 0 factorization for Wilson loops:** at the free point,
loops with disjoint link supports factor. -/
theorem wilsonTwoPoint_zero_of_disjoint (s₁ : Λ) (steps₁ : List Step)
    (s₂ : Λ) (steps₂ : List Step)
    (hdisj : Disjoint (loopLinks σ s₁ steps₁) (loopLinks σ s₂ steps₂)) :
    wilsonTwoPoint σ μG ρ 0 s₁ steps₁ s₂ steps₂
      = gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U s₁ steps₁)
        * gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U s₂ steps₂) :=
  gibbsExpect_zero_mul_of_disjoint σ μG ρ _ _ (loopLinks σ s₁ steps₁)
    (loopLinks σ s₂ steps₂) hdisj (wilsonLoop_dependsOnlyOn σ ρ s₁ steps₁)
    (wilsonLoop_dependsOnlyOn σ ρ s₂ steps₂)

/-- The **connected** Wilson-loop two-point function (the ℂ-analog
of the covariance), as an object. -/
noncomputable def wilsonTwoPointConnected (β : ℝ) (s₁ : Λ)
    (steps₁ : List Step) (s₂ : Λ) (steps₂ : List Step) : ℂ :=
  wilsonTwoPoint σ μG ρ β s₁ steps₁ s₂ steps₂
    - gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s₁ steps₁)
      * gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s₂ steps₂)

/-- **β = 0 vanishing of the connected correlator on disjoint
supports** — the exact, and only, "clustering" content of this
module: at the free point, disjointly supported loops are exactly
uncorrelated. Nothing of the kind is claimed at `β ≠ 0` (Stage 1c,
priced XL, would be the `β ≠ 0` statement and it is not attempted
here). -/
theorem wilsonTwoPointConnected_zero_of_disjoint (s₁ : Λ)
    (steps₁ : List Step) (s₂ : Λ) (steps₂ : List Step)
    (hdisj : Disjoint (loopLinks σ s₁ steps₁) (loopLinks σ s₂ steps₂)) :
    wilsonTwoPointConnected σ μG ρ 0 s₁ steps₁ s₂ steps₂ = 0 := by
  unfold wilsonTwoPointConnected
  rw [wilsonTwoPoint_zero_of_disjoint σ μG ρ s₁ steps₁ s₂ steps₂ hdisj,
    sub_self]

/-- The §3 covariance package applied to Wilson loops: the
Cauchy–Schwarz bound for the real parts of two Wilson loops, at
every `β`, with the integrability side conditions discharged by
boundedness. -/
theorem gibbsCov_wilsonLoop_re_sq_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (s₁ : Λ) (steps₁ : List Step) (s₂ : Λ)
    (steps₂ : List Step) :
    (gibbsCov σ μG ρ β (fun U => (wilsonLoop σ ρ U s₁ steps₁).re)
      (fun U => (wilsonLoop σ ρ U s₂ steps₂).re)) ^ 2
    ≤ gibbsVar σ μG ρ β (fun U => (wilsonLoop σ ρ U s₁ steps₁).re)
      * gibbsVar σ μG ρ β (fun U => (wilsonLoop σ ρ U s₂ steps₂).re) :=
  gibbsCov_sq_le σ μG ρ hρcont hd β _ _
    (measurable_wilsonLoop_re σ ρ hρcont s₁ steps₁).aestronglyMeasurable
    ⟨(d : ℝ), fun U => norm_wilsonLoop_re_le σ ρ hd U s₁ steps₁⟩
    (measurable_wilsonLoop_re σ ρ hρcont s₂ steps₂).aestronglyMeasurable
    ⟨(d : ℝ), fun U => norm_wilsonLoop_re_le σ ρ hd U s₂ steps₂⟩

end WilsonTwoPoint

end ThetLogos
