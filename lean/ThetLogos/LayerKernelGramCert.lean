/-
# G-0 — Gram / SOS certificate infrastructure for `LayerKernelPos`

Menu item **G-0** of the Gram/SOS scoping
(`~/workspace/your_files/gram-sos-lkp-scoping-2026-11-05.md`, §2 pin
and §4 menu; commissioned as part of the enrolled Gram menu, after
the RL-P1 mechanics bricks).  This module is the certificate
infrastructure only: it states the §2 certificate as a Lean
structure and proves the discharge **cert ⇒ LayerKernelPos** ONCE,
generalized from the closing steps of `layerKernelPos_seat`
(binary seat) and `layerKernelPos_abelian_ge` (abelian family).
G-0b (the retrofit registering the three landed supports as
instances) is the companion module `LayerKernelGramCertInstances`.

**Scope fences (the scoping's, restated).**  This is the FINITE
regime (PIN-F): the certificate's type family `τ` and joint index
`ι` are `Fintype`s, so every sum is finite and the §2 domination
clause is vacuous.  The dominated-series regime (PIN-G) at a
general compact group is menu item G-2, which the scoping prices
ONLY as a dependent of the October Route B engine (averaging
projection) — it is not built here and nothing in this module
asserts it.  No existence claim is made: (PIN) at general
(N, G, ρ), β > 0, remains exactly as open as the scoping left it.

**How the §2 pin is carried.**
* *Column expansion* — fields `coeff`, `char`, `expansion`:
  `exp(−β·dens_ρ g) = ∑_τ coeff_τ · char_τ(g)` as class functions,
  with `coeff_τ ≥ 0` a field (`coeff_nonneg`).  Here
  `dens_ρ g = 1 − Re χ_ρ(g)/d` is `gramDens` below (the corpus's
  `colDensC` density read at a single group element).
* *Separation identities* — field `kernel_eq`: the kernel is the
  assembled Gram sum over the joint index `ι` (the scoping's
  multi-indices `τ̲` together with the separation identity's
  contraction index `k`, flattened into one finite index — the
  two sums of (PIN) are one finite sum over pairs `(τ̲, k)`).
  The weight of `j` is not free data: it is DEFINED as the
  product of column coefficients `∏_P coeff (τof j P)`
  (`gramColWeight`), so weight nonnegativity is a theorem
  (`gramColWeight_nonneg`), not an assumption.
* *Pairing form* — field `pairing_eq` with `pairScale ≥ 0`: the
  `LayerKernelPos` pairing integral in the regime's sum form.
  This is the one regime hypothesis the discharge consumes
  beyond `kernel_eq`; at every landed seat it is the seat's
  `seatIntegralPi`-type evaluation (supplied per instance in
  G-0b).  The Gram computation itself — term distribution, the
  swap, the factorization into `conj(Z)·Z`, the `‖Z‖²` reading —
  is proved once, here (`gram_pairing_eq` + `gram_form`).

**FACT-freeness (§2.2), as far as this module controls it.**
(F1) The structure's fields mention only: a representation's
character (through `gramDens`), real coefficients and their
signs, complex features, the column incidence `τof`, and the
kernel/pairing themselves.  No field or proof in this module
references `StratumColumnFactorization`, `zPolymer`, or
`LayerKernelPos` as an input.  (F2) The seat litmus is a
property of instances; it is discharged in G-0b, where the
binary seat — at which FACT is FALSE for every β > 0
(K-FACT-SEAT) — is registered as an instance of this structure.
(F3) Non-degeneracy is made checkable: `gramFeaturesConstant`
names the degenerate shape, and
`LayerKernelSOSCert.layerKernel_const_of_features_constant`
proves that constant features force a constant kernel — the
FACT/β = 0 shape.  **K-GRAM-DEGEN stays armed**: a construction
whose features are constant at β > 0 is exactly the degenerate
case this lemma detects.

NO CLAIM; dials 0/4.  `LayerKernelPos` in general at β > 0
remains OPEN.
-/

import ThetLogos.LayerKernelPos
import ThetLogos.PlaneCrossingBeta2

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section GramCertSection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The one-element density of the scoping's §2:
`dens_ρ(g) = 1 − Re χ_ρ(g)/d`, the corpus's column density
(`colDensC`) read at a single group element in place of a
column word. -/
noncomputable def gramDens (g : G) : ℝ :=
  1 - (charFn ρ g).re / (d : ℝ)

/-- The assembled weight of a joint index `j`: the product over
columns of the column coefficients of `j`'s types,
`∏_P coeff (τof j P)` — the `Π_P c_{τ_P}` of (PIN).  Defined,
not assumed: its nonnegativity is `gramColWeight_nonneg`. -/
noncomputable def gramColWeight {τ ι : Type*} [Fintype (LayerColumn N)]
    (coeff : τ → ℝ) (τof : ι → LayerColumn N → τ) (j : ι) : ℝ :=
  ∏ P : LayerColumn N, coeff (τof j P)

/-- Assembled weights are nonnegative when every column
coefficient is: the Gram sign of (PIN) is spent exactly here
(and in `pairScale_nonneg`). -/
theorem gramColWeight_nonneg {τ ι : Type*} [Fintype (LayerColumn N)]
    (coeff : τ → ℝ) (τof : ι → LayerColumn N → τ)
    (hcoeff : ∀ t, 0 ≤ coeff t) (j : ι) :
    0 ≤ gramColWeight coeff τof j :=
  Finset.prod_nonneg fun P _ => hcoeff _

/-- The Gram observation of a feature family at an observable
`F`: `Z_j = ∑_x conj(Φ_j x)⁻¹…` — precisely,
`Z_j = ∑_x star(Φ_j x) · F(x)`, so that the pairing's `j`-term
is `weight_j · conj(Z_j) · Z_j` (see `gram_pairing_eq`). -/
noncomputable def gramObs {X ι : Type*} [Fintype X] (Φ : ι → X → ℂ)
    (F : X → ℂ) (j : ι) : ℂ :=
  ∑ x, star (Φ j x) * F x

/-- **The Gram pairing computation, proved once** (the shared
closing steps of `layerKernelPos_seat` and
`layerKernelPos_abelian_ge`, at abstract finite `X, ι`): a
double sum against a finite Gram kernel is the cast of the
nonnegative real `∑_j w_j ‖Z_j‖²`.  No sign hypothesis is needed
for the identity itself; signs are spent only in the corollary
`gram_pairing_re_nonneg` and in the discharge. -/
theorem gram_pairing_eq {X ι : Type*} [Fintype X] [Fintype ι]
    (w : ι → ℝ) (Φ : ι → X → ℂ) (F : X → ℂ) :
    (∑ x, ∑ x', (starRingEnd ℂ) (F x)
        * (∑ j, ((w j : ℂ)) * Φ j x * star (Φ j x')) * F x')
      = ((∑ j, w j * ‖gramObs Φ F j‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ x x', (starRingEnd ℂ) (F x)
        * (∑ j, ((w j : ℂ)) * Φ j x * star (Φ j x')) * F x'
      = ∑ j, (starRingEnd ℂ) (F x)
          * (((w j : ℂ)) * Φ j x * star (Φ j x')) * F x' := by
    intro x x'
    rw [Finset.mul_sum, Finset.sum_mul]
  have hswap : ∀ g : X → X → ι → ℂ,
      (∑ x, ∑ x', ∑ j, g x x' j) = ∑ j, ∑ x, ∑ x', g x x' j := by
    intro g
    calc (∑ x, ∑ x', ∑ j, g x x' j)
        = ∑ x, ∑ j, ∑ x', g x x' j :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ j, ∑ x, ∑ x', g x x' j := Finset.sum_comm
  have hfac : ∀ j, (∑ x, ∑ x', (starRingEnd ℂ) (F x)
        * (((w j : ℂ)) * Φ j x * star (Φ j x')) * F x')
      = ((w j : ℂ))
        * ((starRingEnd ℂ) (gramObs Φ F j) * gramObs Φ F j) := by
    intro j
    have h1 : ∀ x x', (starRingEnd ℂ) (F x)
          * (((w j : ℂ)) * Φ j x * star (Φ j x')) * F x'
        = (((w j : ℂ)) * ((starRingEnd ℂ) (F x) * Φ j x))
          * (star (Φ j x') * F x') := by
      intro x x'
      ring
    have hconj : (starRingEnd ℂ) (gramObs Φ F j)
        = ∑ x, (starRingEnd ℂ) (F x) * Φ j x := by
      rw [gramObs, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [starRingEnd_apply, star_mul, star_star, starRingEnd_apply]
    have hA : (∑ x, ((w j : ℂ)) * ((starRingEnd ℂ) (F x) * Φ j x))
        = ((w j : ℂ)) * (starRingEnd ℂ) (gramObs Φ F j) := by
      rw [hconj, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun x' _ => h1 x x',
      ← Finset.sum_mul_sum]
    show ((∑ x, ((w j : ℂ)) * ((starRingEnd ℂ) (F x) * Φ j x))
        * gramObs Φ F j)
      = ((w j : ℂ))
        * ((starRingEnd ℂ) (gramObs Φ F j) * gramObs Φ F j)
    rw [hA]
    ring
  calc (∑ x, ∑ x', (starRingEnd ℂ) (F x)
        * (∑ j, ((w j : ℂ)) * Φ j x * star (Φ j x')) * F x')
      = ∑ x, ∑ x', ∑ j, (starRingEnd ℂ) (F x)
          * (((w j : ℂ)) * Φ j x * star (Φ j x')) * F x' :=
        Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun x' _ => hterm x x'
    _ = ∑ j, ∑ x, ∑ x', (starRingEnd ℂ) (F x)
          * (((w j : ℂ)) * Φ j x * star (Φ j x')) * F x' :=
        hswap _
    _ = ∑ j, ((w j : ℂ))
          * ((starRingEnd ℂ) (gramObs Φ F j) * gramObs Φ F j) :=
        Finset.sum_congr rfl fun j _ => hfac j
    _ = ∑ j, ((w j * ‖gramObs Φ F j‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcc : (starRingEnd ℂ) (gramObs Φ F j) * gramObs Φ F j
            = ((‖gramObs Φ F j‖ ^ 2 : ℝ) : ℂ) :=
          (mul_comm _ _).trans
            ((RCLike.mul_conj _).trans (Complex.ofReal_pow _ _).symm)
        rw [hcc, ← Complex.ofReal_mul]
    _ = ((∑ j, w j * ‖gramObs Φ F j‖ ^ 2 : ℝ) : ℂ) :=
        (Complex.ofReal_sum _ _).symm

/-- The Gram pairing's real part is nonnegative when all
weights are. -/
theorem gram_pairing_re_nonneg {X ι : Type*} [Fintype X] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (Φ : ι → X → ℂ) (F : X → ℂ) :
    0 ≤ (∑ x, ∑ x', (starRingEnd ℂ) (F x)
        * (∑ j, ((w j : ℂ)) * Φ j x * star (Φ j x')) * F x').re := by
  rw [gram_pairing_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hw j) (pow_nonneg (norm_nonneg _) _)

/-- The degenerate feature shape of test F3: every feature is
constant in the configuration. -/
def gramFeaturesConstant {ι : Type*}
    (feat : ι → (LayerLink N → G) → ℂ) : Prop :=
  ∀ j u u', feat j u = feat j u'

variable (β : ℝ) {τ ι : Type*} [Fintype τ] [Fintype ι]
variable [Fintype G] [DecidableEq (LayerLink N)]

/-- **A Gram/SOS certificate for 𝒜 at (N, G, ρ, β)** — the §2
pin as a structure, finite regime.  The type family `τ` and
the joint index `ι` are finite-type parameters of the
structure (the finite regime's domination: every sum is a
finite sum).  Fields: the column expansion (`coeff`,
`coeff_nonneg`, `char`, `expansion`); the separation data
(`τof`, `feat`) with the assembled kernel identity
(`kernel_eq`); and the regime's pairing evaluation
(`pairScale`, `pairScale_nonneg`, `pairing_eq`). -/
structure LayerKernelSOSCert where
  /-- The column expansion coefficients `c_τ`. -/
  coeff : τ → ℝ
  /-- All column coefficients are nonnegative. -/
  coeff_nonneg : ∀ t, 0 ≤ coeff t
  /-- The column characters `χ_τ` (class functions on `G`). -/
  char : τ → G → ℂ
  /-- The column expansion: the one-column Boltzmann factor is
  the character sum with coefficients `coeff`. -/
  expansion : ∀ g : G,
    ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = ∑ t, ((coeff t : ℝ) : ℂ) * char t g
  /-- The column-type readout of a joint index: `τof j P` is
  the type `j` assigns to column `P` (the multi-index of
  (PIN), with the separation identities' contraction index
  flattened into the same finite index `ι`). -/
  τof : ι → LayerColumn N → τ
  /-- The separated features `Φ_j`: functions of the layer data
  alone (no stratum variable, no second configuration). -/
  feat : ι → (LayerLink N → G) → ℂ
  /-- The nonnegative scalar of the regime's pairing evaluation
  (at a finite seat: the product-measure mass of one
  configuration pair). -/
  pairScale : ℝ
  /-- The pairing scalar is nonnegative. -/
  pairScale_nonneg : 0 ≤ pairScale
  /-- The regime's pairing evaluation: the `LayerKernelPos`
  pairing integral is the scalar times the double sum over
  configurations. -/
  pairing_eq : ∀ F : (LayerLink N → G) → ℂ,
    (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = ((pairScale : ℝ) : ℂ)
        * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel μG ρ β u u' * F u'
  /-- **(PIN-F)** The assembled kernel identity: the kernel is
  the Gram sum over the joint index, with assembled weights
  `gramColWeight coeff τof j ≥ 0`. -/
  kernel_eq : ∀ u u' : LayerLink N → G,
    layerKernel μG ρ β u u'
      = ∑ j, ((gramColWeight coeff τof j : ℝ) : ℂ)
          * feat j u * star (feat j u')

namespace LayerKernelSOSCert

variable (cert : LayerKernelSOSCert (N := N) (τ := τ) (ι := ι) μG ρ β)

/-- The certificate's pairing in Gram form: a nonnegative real
cast — `pairScale · ∑_j weight_j ‖Z_j‖²`. -/
theorem gram_form (F : (LayerLink N → G) → ℂ) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = ((cert.pairScale
          * ∑ j, gramColWeight cert.coeff cert.τof j
              * ‖gramObs cert.feat F j‖ ^ 2 : ℝ) : ℂ) := by
  calc (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG))
      = ((cert.pairScale : ℝ) : ℂ)
          * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel μG ρ β u u' * F u' :=
        cert.pairing_eq F
    _ = ((cert.pairScale : ℝ) : ℂ)
          * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
              * (∑ j, ((gramColWeight cert.coeff cert.τof j : ℝ) : ℂ)
                  * cert.feat j u * star (cert.feat j u')) * F u' := by
        congr 1
        refine Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun u' _ => ?_
        rw [cert.kernel_eq]
    _ = ((cert.pairScale
          * ∑ j, gramColWeight cert.coeff cert.τof j
              * ‖gramObs cert.feat F j‖ ^ 2 : ℝ) : ℂ) := by
        rw [gram_pairing_eq, ← Complex.ofReal_mul]

/-- **G-0 headline — the discharge, proved once.**  Every
Gram/SOS certificate at (N, G, ρ, β) yields `LayerKernelPos`
at (N, G, ρ, β): the pairing is a nonnegative scalar times a
sum of `weight_j · ‖Z_j‖²` with both factors nonnegative.
Gauge invariance is not consumed (the certificate proves the
pairing for every `F`, as both landed supports do). -/
theorem layerKernelPos
    (cert : LayerKernelSOSCert (N := N) (τ := τ) (ι := ι) μG ρ β) :
    LayerKernelPos (N := N) μG ρ β := by
  intro F _hF
  rw [LayerKernelSOSCert.gram_form (μG := μG) (ρ := ρ) (β := β) cert F,
    Complex.ofReal_re]
  refine mul_nonneg cert.pairScale_nonneg ?_
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (gramColWeight_nonneg cert.coeff cert.τof
      cert.coeff_nonneg j) (pow_nonneg (norm_nonneg _) _)

/-- **The F3 degeneracy test.**  If a certificate's features
are all constant in the configuration, its kernel is constant
— the FACT/β = 0 shape.  At β > 0 such a certificate is
exactly what **K-GRAM-DEGEN** fires on. -/
theorem layerKernel_const_of_features_constant
    (hconst : gramFeaturesConstant cert.feat) :
    ∃ K₀ : ℂ, ∀ u u' : LayerLink N → G,
      layerKernel μG ρ β u u' = K₀ := by
  refine ⟨∑ j, ((gramColWeight cert.coeff cert.τof j : ℝ) : ℂ)
      * cert.feat j 1 * star (cert.feat j 1), fun u u' => ?_⟩
  rw [cert.kernel_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hconst j u 1, hconst j u' 1]

end LayerKernelSOSCert

end GramCertSection

end ThetLogos

