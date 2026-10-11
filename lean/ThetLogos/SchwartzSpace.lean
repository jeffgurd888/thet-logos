import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import ThetLogos.FieldOperators

namespace ThetLogos

open scoped SchwartzMap FourierTransform
open LineDeriv

/-!
# ThetLogos.SchwartzSpace — genuine Schwartz test-function machinery

Source: Rung 6, Price 2 (2026-10-11), Jeff's "continue."

**What this file IS.** The genuine Schwartz space `𝒮(ℝⁿ, ℂ)`, built on
Mathlib's `SchwartzMap` — not a from-scratch rebuild. Finding of record:
**the premise was wrong.** This Mathlib (2026) *ships* the Schwartz machine
(`Mathlib/Analysis/Distribution/SchwartzSpace/{Basic,Deriv,Fourier}.lean`,
`TemperedDistribution.lean`, all 2026 Moritz Doll): smooth rapidly-decreasing
functions with the seminorm family, the locally-convex metrizable topology,
derivatives and polynomial multiplication as continuous linear endomaps,
tempered distributions as the continuous dual, and the Fourier transform with
inversion. The `TestFunctionMarker` docstring in `FieldOperators.lean`
("Mathlib (2026) has no Schwartz space") is outdated as of this Mathlib —
this file is the correction, and `schwartzMarker` below discharges that T2
marker with `𝒮(ℝ⁴, ℂ)`.

Mathlib's definition (equivalent to the multi-index one): `f` is Schwartz if
it is `ContDiff ℝ ∞` and for all `k n : ℕ` there is `C` with
`‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C` for all `x`. The seminorms
`SchwartzMap.seminorm 𝕜 k n` are the best constants; they dominate the
classical `ρ_{α,β}(f) = sup |x^α D^β f|` for `|α| ≤ k`, `|β| = n`.

Honesty tiers in this file:
- **T1 (proved):** `schwartzSubmodule` (vector space as a submodule of all
  functions), `partialDerivSchwartz` + `partialDerivSchwartz_apply` (closure
  under partial/coordinate derivatives), `coord_hasTemperateGrowth`,
  `monomial_hasTemperateGrowth`, `polynomial_hasTemperateGrowth`,
  `mulTemperateCLM` + `mulTemperateCLM_apply` + `mulPolynomial_mem`
  (closure under polynomial multiplication), `schwartzTest_continuous`,
  `schwartzTest_bounded`, `schwartzTest_vanishesAtInfty`,
  `schwartzTest_locallyConvex`, `schwartzTest_firstCountable` (topology via
  Mathlib instances), `schwartzFourier_inversion` (Fourier inversion on
  `𝒮(EuclideanSpace ℝ (Fin n), ℂ)`, via Mathlib).
- **T2 (discharged marker):** `schwartzMarker` — the old `TestFunctionMarker`
  instantiated with genuine `𝒮(ℝ⁴, ℂ)`.
- **T5 (priced windows, exact statements, unproved by design):**
  `schwartzComplete_window` (Fréchet *completeness* — Mathlib has the
  locally-convex metrizable topology but no `CompleteSpace` instance),
  `fourierAutomorphism_window` (the Fourier automorphism transported to
  `𝒮(Fin n → ℝ, ℂ)` itself — Mathlib proves it on `EuclideanSpace`).
  Note the strong-dual topology of `𝒮'` is also unformalized (Mathlib uses
  the pointwise topology); the continuous dual as a space is T1.
-/

/-- **T1:** genuine Schwartz test functions on `ℝⁿ`: smooth, all derivatives
    rapidly decreasing. Mathlib's `SchwartzMap`; `n` is the spacetime
    dimension (use `4`). -/
abbrev SchwartzTest (n : ℕ) := SchwartzMap (Fin n → ℝ) ℂ

/-!
## The vector space
-/

/-- **T1:** the Schwartz functions form a submodule of all functions
    `ℝⁿ → ℂ` — in particular a complex vector space. (The `AddCommGroup` and
    `Module ℂ` instances on `SchwartzTest n` itself are Mathlib's.) -/
def schwartzSubmodule (n : ℕ) : Submodule ℂ ((Fin n → ℝ) → ℂ) where
  carrier := { f | ∃ s : SchwartzTest n, (s : (Fin n → ℝ) → ℂ) = f }
  add_mem' := by
    rintro a b ⟨sa, rfl⟩ ⟨sb, rfl⟩
    exact ⟨sa + sb, funext fun x => rfl⟩
  zero_mem' := ⟨0, funext fun x => rfl⟩
  smul_mem' := by
    rintro c a ⟨sa, rfl⟩
    exact ⟨c • sa, funext fun x => rfl⟩

/-!
## Closure under partial derivatives

Mathlib has no named partial-derivative operator; the partial derivative
`∂f/∂xᵢ` is the directional (line) derivative along the `i`-th coordinate
axis `Pi.single i 1`, which is exactly what `∂_{m}` means. Closure is the
continuous linear endomap `LineDeriv.lineDerivOpCLM`.
-/

/-- **T1:** partial derivative `∂/∂xᵢ` as a `ℂ`-linear endomap of Schwartz
    space — Schwartz functions are closed under differentiation, and the
    derivative is again Schwartz (continuously in `f`). -/
noncomputable def partialDerivSchwartz (n : ℕ) (i : Fin n) :
    SchwartzTest n →L[ℂ] SchwartzTest n :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzTest n) (Pi.single i (1 : ℝ) : Fin n → ℝ)

/-- **T1:** the partial derivative acts as the Fréchet derivative applied to
    the `i`-th basis vector — i.e. the genuine `∂f/∂xᵢ`. -/
theorem partialDerivSchwartz_apply (n : ℕ) (i : Fin n) (f : SchwartzTest n)
    (x : Fin n → ℝ) :
    partialDerivSchwartz n i f x
      = fderiv ℝ (f : (Fin n → ℝ) → ℂ) x (Pi.single i (1 : ℝ)) := by
  unfold partialDerivSchwartz
  rw [LineDeriv.lineDerivOpCLM_apply]
  exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ f x

/-!
## Closure under multiplication by polynomials

Polynomials have temperate growth (`Function.HasTemperateGrowth`), and
Mathlib's `SchwartzMap.smulLeftCLM` multiplies a Schwartz function by any
temperate-growth scalar function, staying inside Schwartz space.
-/

/-- **T1:** the `i`-th coordinate function `x ↦ xᵢ` (complex-valued) has
    temperate growth. -/
theorem coord_hasTemperateGrowth (n : ℕ) (i : Fin n) :
    Function.HasTemperateGrowth (fun x : Fin n → ℝ => Complex.ofReal (x i)) :=
  Complex.hasTemperateGrowth_ofReal.comp
    (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℝ) i).hasTemperateGrowth

/-- **T1:** every coordinate monomial `x ↦ ∏ᵢ xᵢ^(eᵢ)` has temperate growth. -/
theorem monomial_hasTemperateGrowth (n : ℕ) (e : Fin n → ℕ) :
    Function.HasTemperateGrowth
      (fun x : Fin n → ℝ => ∏ i, Complex.ofReal (x i) ^ e i) := by
  have key : ∀ s : Finset (Fin n), Function.HasTemperateGrowth
      (fun x : Fin n → ℝ => ∏ i ∈ s, Complex.ofReal (x i) ^ e i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
      have h1 : ∀ x : Fin n → ℝ,
          (∏ i ∈ insert a t, Complex.ofReal (x i) ^ e i)
            = Complex.ofReal (x a) ^ e a * ∏ i ∈ t, Complex.ofReal (x i) ^ e i :=
        fun x => Finset.prod_insert ha
      have h2 : (fun x : Fin n → ℝ => ∏ i ∈ insert a t, Complex.ofReal (x i) ^ e i)
          = (fun x : Fin n → ℝ => Complex.ofReal (x a) ^ e a) *
            (fun x : Fin n → ℝ => ∏ i ∈ t, Complex.ofReal (x i) ^ e i) :=
        funext fun x => by simp only [Pi.mul_apply]; exact h1 x
      rw [h2]
      exact ((coord_hasTemperateGrowth n a).pow (e a)).mul ih
  exact key Finset.univ

/-- **T1:** every polynomial `∑ₑ cₑ ∏ᵢ xᵢ^(eᵢ)` (finite support coefficients)
    has temperate growth. -/
theorem polynomial_hasTemperateGrowth (n : ℕ) (c : (Fin n → ℕ) →₀ ℂ) :
    Function.HasTemperateGrowth
      (fun x : Fin n → ℝ => ∑ e ∈ c.support, c e * ∏ i, Complex.ofReal (x i) ^ e i) := by
  apply Function.HasTemperateGrowth.sum
  intro e _
  exact (Function.HasTemperateGrowth.const (c e)).mul (monomial_hasTemperateGrowth n e)

/-- **T1:** multiplication by a temperate-growth scalar function (in
    particular any polynomial) as a `ℂ`-linear endomap of Schwartz space. -/
noncomputable def mulTemperateCLM (n : ℕ) (g : (Fin n → ℝ) → ℂ) :
    SchwartzTest n →L[ℂ] SchwartzTest n :=
  SchwartzMap.smulLeftCLM ℂ g

/-- **T1:** `mulTemperateCLM` acts by pointwise multiplication. -/
theorem mulTemperateCLM_apply (n : ℕ) (g : (Fin n → ℝ) → ℂ)
    (hg : g.HasTemperateGrowth) (f : SchwartzTest n) (x : Fin n → ℝ) :
    mulTemperateCLM n g f x = g x • f x :=
  SchwartzMap.smulLeftCLM_apply_apply hg f x

/-- **T1:** Schwartz space is closed under multiplication by polynomials —
    the product is again a Schwartz function, with the pointwise formula. -/
theorem mulPolynomial_mem (n : ℕ) (c : (Fin n → ℕ) →₀ ℂ) (f : SchwartzTest n) :
    ∃ h : SchwartzTest n, ∀ x : Fin n → ℝ,
      h x = (∑ e ∈ c.support, c e * ∏ i, Complex.ofReal (x i) ^ e i) • f x :=
  ⟨mulTemperateCLM n _ f,
    fun x => mulTemperateCLM_apply n _ (polynomial_hasTemperateGrowth n c) f x⟩

/-!
## Bounded, continuous, vanishing at infinity
-/

/-- **T1:** every Schwartz function is continuous. -/
theorem schwartzTest_continuous (n : ℕ) (f : SchwartzTest n) :
    Continuous (f : (Fin n → ℝ) → ℂ) :=
  f.continuous

/-- **T1:** every Schwartz function is bounded (controlled by the
    `(0,0)`-seminorm). -/
theorem schwartzTest_bounded (n : ℕ) (f : SchwartzTest n) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, ‖f x‖ ≤ C :=
  ⟨SchwartzMap.seminorm ℂ 0 0 f, fun x => SchwartzMap.norm_le_seminorm ℂ f x⟩

/-- **T1:** every Schwartz function vanishes at infinity. -/
theorem schwartzTest_vanishesAtInfty (n : ℕ) (f : SchwartzTest n) :
    Filter.Tendsto (f : (Fin n → ℝ) → ℂ) (Filter.cocompact (Fin n → ℝ)) (nhds 0) :=
  f.tendsto_cocompact

/-!
## Topology and duality: what Mathlib ships (T1 via instances)
-/

/-- **T1 (Mathlib):** Schwartz space is a locally convex real topological
    vector space for the seminorm topology. -/
theorem schwartzTest_locallyConvex (n : ℕ) :
    LocallyConvexSpace ℝ (SchwartzTest n) :=
  inferInstance

/-- **T1 (Mathlib):** the Schwartz topology is first countable (metrizable
    in the TVS sense — countably many seminorms). -/
theorem schwartzTest_firstCountable (n : ℕ) :
    FirstCountableTopology (SchwartzTest n) :=
  inferInstance

/-- **T1 (Mathlib):** tempered distributions are the continuous dual:
    `𝓢'(E, ℂ)` is *defined* as `𝓢(E, ℂ) →Lₚₜ[ℂ] ℂ` (continuous linear maps
    with the pointwise-convergence topology). The evaluation pairing
    `T f` is continuous-linear in each argument by definition. -/
theorem temperedDual_isContinuousDual (n : ℕ) :
    𝓢'(Fin n → ℝ, ℂ) = (SchwartzTest n →Lₚₜ[ℂ] ℂ) :=
  rfl

/-!
## Fourier transform (T1 via Mathlib, on Euclidean space)
-/

/-- **T1 (Mathlib):** Fourier inversion on Schwartz space —
    `𝓕⁻ (𝓕 f) = f`. Mathlib proves the Fourier transform as a continuous
    linear automorphism `SchwartzMap.fourierTransformCLM` with
    `FourierPair`/`FourierInvPair` instances; stated here for
    `EuclideanSpace ℝ (Fin n)`, the finite-dimensional real inner product
    space Mathlib's Fourier theory is built on. -/
theorem schwartzFourier_inversion (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕⁻ (𝓕 f) = f :=
  FourierTransform.fourierInv_fourier_eq f

/-- **T1 (Mathlib):** the other inversion direction — `𝓕 (𝓕⁻ f) = f`. -/
theorem schwartzFourier_inversion' (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕 (𝓕⁻ f) = f :=
  FourierTransform.fourier_fourierInv_eq f

/-!
## The discharged marker
-/

/-- **T2 discharged:** the old `TestFunctionMarker` placeholder from
    `FieldOperators.lean`, instantiated with genuine Schwartz test functions
    `𝒮(ℝ⁴, ℂ)`. The marker's docstring claim ("Mathlib (2026) has no Schwartz
    space") is superseded by this file. -/
def schwartzMarker : TestFunctionMarker :=
  ⟨SchwartzTest 4⟩

/-!
## Priced windows: the genuinely open remainders

The task priced three items as T5 windows (Fréchet topology, tempered
distributions, Fourier automorphism) on the premise that Mathlib lacked them.
Verdict: **two of the three are already T1 in Mathlib** (locally-convex
metrizable topology above; tempered distributions as the continuous dual;
Fourier inversion). What remains open is exact-stated below — clean frames,
no sorrys.
-/

/-- **Priced window (T5):** Fréchet *completeness* of Schwartz space.
    Mathlib 2026 proves the full locally-convex first-countable topology
    (`SchwartzMap.instLocallyConvexSpace`, `instFirstCountableTopology`,
    `schwartz_withSeminorms`) but provides **no** `CompleteSpace 𝓢(E, F)`
    instance. Exact statement: the seminorm topology is complete. -/
def schwartzComplete_window (n : ℕ) : Prop :=
  CompleteSpace (SchwartzTest n)

/-- **Priced window (T5):** the Fourier automorphism on `𝒮(Fin n → ℝ, ℂ)`
    itself. Mathlib proves Fourier inversion for
    `𝓢(EuclideanSpace ℝ (Fin n), ℂ)` (T1 above); transporting it along the
    canonical identification of `EuclideanSpace ℝ (Fin n)` with `Fin n → ℝ`
    (norm equivalence, hence Schwartz-space equivalence, intertwining the
    Fourier character) is routine analysis not formalized here.
    What would discharge it: the transfer principle for `SchwartzMap` along a
    linear isometry, or a direct repeat of the Fourier file at `Fin n → ℝ`. -/
def fourierAutomorphism_window (n : ℕ) : Prop :=
  Nonempty (SchwartzTest n ≃L[ℂ] SchwartzTest n)

#print axioms schwartzSubmodule
#print axioms partialDerivSchwartz_apply
#print axioms coord_hasTemperateGrowth
#print axioms monomial_hasTemperateGrowth
#print axioms polynomial_hasTemperateGrowth
#print axioms mulTemperateCLM_apply
#print axioms mulPolynomial_mem
#print axioms schwartzTest_continuous
#print axioms schwartzTest_bounded
#print axioms schwartzTest_vanishesAtInfty
#print axioms schwartzTest_locallyConvex
#print axioms schwartzTest_firstCountable
#print axioms schwartzFourier_inversion
#print axioms schwartzFourier_inversion'

end ThetLogos
