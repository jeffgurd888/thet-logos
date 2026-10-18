import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ThetLogos.SchrodingerDynamics

/-!
# Schrödinger smalls: the two priced remainders of `SchrodingerDynamics` (T1)

This module discharges the two remainders priced in the Schrödinger
gauntlet (`whitepaper/gauntlet-schrodinger-2026-10-16.md`) and re-priced
in the parked-fleet gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md`
§5), against the evolution operator `evolOp` of `SchrodingerDynamics.lean`
(which is NOT modified).

* **5a — literal `NormedSpace.exp` identification (S).**
  `SchrodingerDynamics` *characterized* `evolOp hT t` as `exp (−i t T)` via
  the Schrödinger equation + uniqueness (`evolOp_unique`) but never
  identified it with Mathlib's literal exponential of a continuous linear
  map. §1 closes this: for every `ψ₀`, the curve
  `s ↦ NormedSpace.exp (s • genCLM hT) ψ₀` satisfies the same ODE with the
  same initial value (the derivative is Mathlib's
  `hasDerivAt_exp_smul_const'`, used at the real scalar field — the pinned
  Mathlib's `NormedSpace.exp` is a single field-independent function, the
  exponential series at any characteristic-zero scalar field), so
  `evolOp_unique` identifies the curves, and two continuous linear maps
  agreeing on every vector are equal:
  `evolCLM hT t = NormedSpace.exp (t • genCLM hT)`.

* **5b — Dyson first-order term (S–M = α + β).**
  In the fermionic environment of Pitch 3 Campaign 1
  (`hamInt d lam W g = freeHamiltonian d lam + (g : ℂ) • intOp d W`):
  - **Dyson-α (S).** The first-order interaction-picture term
    `W₁(t) = −i • ∫₀ᵗ V_I(s) ds`, where
    `V_I(s) = heisenbergEvol (free) s (g • intOp W)` packaged as a
    continuous curve of continuous linear maps (continuity comes from
    the §1 exponential form of the free evolution). Characterized:
    `W₁(0) = 0` and `dW₁/dt = −i • V_I(t)` (FTC), and the applied form
    `W₁(t) ψ₀ = ∫₀ᵗ −i • V_I(s) ψ₀ ds`.
  - **Dyson-β (M).** The full Duhamel identity, as theorems: the
    interaction-picture state `F(t)ψ₀ = U₀(−t) U(t) ψ₀` satisfies
    `F(t)ψ₀ = ψ₀ + ∫₀ᵗ −i • V_I(s) (F(s)ψ₀) ds`, and splitting
    `F(s) = ψ₀ + (F(s) − ψ₀)` inside the integral gives the first-order
    expansion with the integral remainder as a theorem,
    `F(t)ψ₀ = ψ₀ + W₁(t)ψ₀ + ∫₀ᵗ −i • V_I(s)(F(s)ψ₀ − ψ₀) ds`,
    plus its Schrödinger-picture form. "First-order" is thereby an
    approximation statement, not a notation.

## Honesty fences

* Finite dimensions / finite modes only, exactly as in
  `SchrodingerDynamics`. The Dyson term is a formal first-order
  coefficient of the interaction-picture evolution; **no scattering
  theory, no S-matrix, no continuum statement** is made or implied.
* Nothing here touches the bosonic sector or any unbounded generator.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## §1. 5a — the literal `NormedSpace.exp` identification -/

section ExpIdentification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)

/-- The Schrödinger generator of the symmetric operator `T`, packaged as a
continuous linear map: `(-i) • T`. This is the literal generator whose
`NormedSpace.exp` is identified with `evolOp` below. -/
noncomputable def genCLM (hT : T.IsSymmetric) : H →L[ℂ] H :=
  (-Complex.I) • LinearMap.toContinuousLinearMap T

theorem genCLM_apply (x : H) : genCLM hT x = (-Complex.I) • T x := rfl

/-- Derivative of a real curve of complex continuous linear maps applied
to a *fixed* vector: if `c` has derivative `c'` at `t`, then
`s ↦ c s ψ₀` has derivative `c' ψ₀`. (Evaluation at `ψ₀` is a continuous
linear map, real-linear after restricting scalars; the statement goes
through `HasFDerivAt.comp_hasDerivAt`.) -/
theorem hasDerivAt_apply_const {c : ℝ → H →L[ℂ] H} {c' : H →L[ℂ] H}
    {t : ℝ} (hc : HasDerivAt c c' t) (ψ₀ : H) :
    HasDerivAt (fun s => c s ψ₀) (c' ψ₀) t := by
  have hev : HasFDerivAt (fun F : H →L[ℂ] H => F ψ₀)
      ((ContinuousLinearMap.apply ℂ H ψ₀).restrictScalars ℝ) (c t) :=
    ((ContinuousLinearMap.apply ℂ H ψ₀).restrictScalars ℝ).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt t hev hc

/-- The exponential curve of the generator, applied to a fixed vector,
satisfies the Schrödinger equation for `T`: the derivative of
`s ↦ NormedSpace.exp (s • genCLM hT) ψ₀` at `t` is
`(-i) • T (NormedSpace.exp (t • genCLM hT) ψ₀)`. -/
theorem hasDerivAt_exp_curve_apply (ψ₀ : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • genCLM hT) ψ₀)
      ((-Complex.I) • T (NormedSpace.exp (t • genCLM hT) ψ₀)) t := by
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hCLM : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • genCLM hT))
      (genCLM hT * NormedSpace.exp (t • genCLM hT)) t :=
    hasDerivAt_exp_smul_const' (genCLM hT) t
  have h := hasDerivAt_apply_const hCLM ψ₀
  simpa only [ContinuousLinearMap.mul_apply, genCLM_apply] using h

/-- **5a (T1):** the evolution operator of `SchrodingerDynamics` is the
literal `NormedSpace.exp` of the generator, applied to the vector:
`evolOp hT t ψ₀ = NormedSpace.exp (t • genCLM hT) ψ₀`. Proved by
`evolOp_unique`: the exponential curve solves the same Schrödinger
equation with the same initial value `ψ₀`. -/
theorem evolOp_apply_eq_exp (t : ℝ) (ψ₀ : H) :
    evolOp hT t ψ₀ = NormedSpace.exp (t • genCLM hT) ψ₀ := by
  have h := evolOp_unique hT
    (fun s : ℝ => NormedSpace.exp (s • genCLM hT) ψ₀) ψ₀
    (fun s => hasDerivAt_exp_curve_apply hT ψ₀ s)
    (by simp [NormedSpace.exp_zero]) t
  exact h.symm

/-- The evolution operator packaged as a continuous linear map. -/
noncomputable def evolCLM (hT : T.IsSymmetric) (t : ℝ) : H →L[ℂ] H :=
  LinearMap.toContinuousLinearMap (evolOp hT t)

theorem evolCLM_apply (t : ℝ) (ψ : H) : evolCLM hT t ψ = evolOp hT t ψ := rfl

/-- **5a (T1), packaged form:** as continuous linear maps,
`evolCLM hT t = NormedSpace.exp (t • genCLM hT)` — two continuous linear
maps agreeing on every vector are equal. -/
theorem evolCLM_eq_exp (t : ℝ) :
    evolCLM hT t = NormedSpace.exp (t • genCLM hT) := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [evolCLM_apply]
  exact evolOp_apply_eq_exp hT t ψ

/-- The packaged evolution is continuous in time, in operator norm —
an immediate corollary of the exponential form (used for the Dyson
integrands below). -/
theorem continuous_evolCLM : Continuous (evolCLM hT) := by
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hdiff : Differentiable ℝ (fun t : ℝ => NormedSpace.exp (t • genCLM hT)) :=
    fun t => (hasDerivAt_exp_smul_const' (genCLM hT) t).differentiableAt
  have hfun : evolCLM hT = fun t : ℝ => NormedSpace.exp (t • genCLM hT) :=
    funext (evolCLM_eq_exp hT)
  rw [hfun]
  exact hdiff.continuous

end ExpIdentification

/-! ## §2. 5b-α — the Dyson first-order term (interaction picture)

From here on the environment is the fermionic one of Pitch 3 Campaign 1:
`FermionicFock d` with free Hamiltonian `freeHamiltonian d lam` and
interacting Hamiltonian `hamInt d lam W g = freeHamiltonian d lam +
(g : ℂ) • intOp d W`. -/

section Dyson

variable (d : ℕ) (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
  (g : ℝ)

/-- The free Hamiltonian is symmetric (the diagonal-operator argument
already used inside `hamInt_isSymmetric`). -/
theorem freeHamiltonian_isSymmetric : (freeHamiltonian d lam).IsSymmetric :=
  diagOp_isSymmetric d (freeHamiltonian_basis d lam)

/-- The interaction-picture perturbation, packaged as a curve of
continuous linear maps: `s ↦ U₀(−s) ∘ (g • intOp W) ∘ U₀(s)`, i.e. the
CLM form of `heisenbergEvol (free) s ((g : ℂ) • intOp d W)`. -/
noncomputable def intPictCLM (s : ℝ) : FermionicFock d →L[ℂ] FermionicFock d :=
  LinearMap.toContinuousLinearMap
    (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
      ((g : ℂ) • intOp d W))

theorem intPictCLM_apply (s : ℝ) (ψ : FermionicFock d) :
    intPictCLM d lam W g s ψ
      = heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
          ((g : ℂ) • intOp d W) ψ := rfl

/-- The product form of the interaction-picture curve, through the
packaged free evolution of §1. -/
theorem intPictCLM_eq (s : ℝ) :
    intPictCLM d lam W g s
      = (evolCLM (freeHamiltonian_isSymmetric d lam) (-s)).comp
        ((LinearMap.toContinuousLinearMap ((g : ℂ) • intOp d W)).comp
          (evolCLM (freeHamiltonian_isSymmetric d lam) s)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [intPictCLM_apply, heisenbergEvol_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    evolCLM_apply, evolCLM_apply, LinearMap.coe_toContinuousLinearMap']

/-- The interaction-picture curve is continuous in operator norm —
the free factors are continuous by the exponential form of §1, and
multiplication of continuous linear maps is continuous. -/
theorem continuous_intPictCLM : Continuous (intPictCLM d lam W g) := by
  have h1 : Continuous (evolCLM (freeHamiltonian_isSymmetric d lam)) :=
    continuous_evolCLM _
  have h2 : Continuous
      fun s : ℝ => evolCLM (freeHamiltonian_isSymmetric d lam) (-s) :=
    h1.comp continuous_neg
  have h3 : Continuous fun s : ℝ =>
      (evolCLM (freeHamiltonian_isSymmetric d lam) (-s)).comp
        ((LinearMap.toContinuousLinearMap ((g : ℂ) • intOp d W)).comp
          (evolCLM (freeHamiltonian_isSymmetric d lam) s)) :=
    h2.clm_comp (continuous_const.clm_comp h1)
  exact h3.congr (fun s => (intPictCLM_eq d lam W g s).symm)

/-- **Dyson-α (T1):** the first-order interaction-picture term
`W₁(t) = −i • ∫₀ᵗ V_I(s) ds`, as a continuous linear map. -/
noncomputable def dysonW1 (t : ℝ) : FermionicFock d →L[ℂ] FermionicFock d :=
  (-Complex.I) • ∫ s in (0)..t, intPictCLM d lam W g s

/-- The first-order term vanishes at `t = 0`. -/
theorem dysonW1_zero : dysonW1 d lam W g 0 = 0 := by
  rw [dysonW1, intervalIntegral.integral_same]
  ext ψ
  simp

/-- The derivative of the first-order term is the interaction-picture
perturbation itself: `dW₁/dt = −i • V_I(t)` (fundamental theorem of
calculus applied to the continuous CLM-valued curve). -/
theorem hasDerivAt_dysonW1 (t : ℝ) :
    HasDerivAt (dysonW1 d lam W g) ((-Complex.I) • intPictCLM d lam W g t)
      t := by
  have hInt : IntervalIntegrable (intPictCLM d lam W g)
      MeasureTheory.volume 0 t :=
    (continuous_intPictCLM d lam W g).intervalIntegrable 0 t
  have hMeas : StronglyMeasurableAtFilter (intPictCLM d lam W g)
      (nhds t) MeasureTheory.volume :=
    (continuous_intPictCLM d lam W g).stronglyMeasurableAtFilter
      MeasureTheory.volume (nhds t)
  have h := intervalIntegral.integral_hasDerivAt_right hInt hMeas
    (continuous_intPictCLM d lam W g).continuousAt
  have h2 := h.const_smul (-Complex.I)
  exact h2

/-- The applied form of the first-order term:
`W₁(t) ψ₀ = ∫₀ᵗ −i • (V_I(s) ψ₀) ds`. -/
theorem dysonW1_apply (ψ₀ : FermionicFock d) (t : ℝ) :
    dysonW1 d lam W g t ψ₀
      = ∫ s in (0)..t, (-Complex.I) • (intPictCLM d lam W g s ψ₀) := by
  have hderiv : ∀ x ∈ Set.uIcc 0 t,
      HasDerivAt (fun u => dysonW1 d lam W g u ψ₀)
        ((-Complex.I) • (intPictCLM d lam W g x ψ₀)) x := by
    intro x _
    have h := hasDerivAt_apply_const (hasDerivAt_dysonW1 d lam W g x) ψ₀
    simpa only [ContinuousLinearMap.smul_apply] using h
  have hconst : Continuous fun _ : ℝ => (-Complex.I : ℂ) := continuous_const
  have hcont : Continuous
      (fun s => (-Complex.I) • (intPictCLM d lam W g s ψ₀)) :=
    hconst.smul ((continuous_intPictCLM d lam W g).clm_apply continuous_const)
  have hInt : IntervalIntegrable
      (fun s => (-Complex.I) • (intPictCLM d lam W g s ψ₀))
      MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable 0 t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
  rw [dysonW1_zero, ContinuousLinearMap.zero_apply, sub_zero] at h
  exact h.symm

end Dyson

/-! ## §3. 5b-β — the Duhamel identity and the first-order expansion -/

section DysonBeta

variable (d : ℕ) (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
  (g : ℝ)

/-- The interaction-picture state: `F(t)ψ₀ = U₀(−t) U(t) ψ₀`, where
`U₀` is the free evolution and `U` the interacting one. -/
noncomputable def intState (ψ₀ : FermionicFock d) (t : ℝ) :
    FermionicFock d :=
  evolOp (freeHamiltonian_isSymmetric d lam) (-t)
    (evolOp (hamInt_isSymmetric d lam W g) t ψ₀)

theorem intState_zero (ψ₀ : FermionicFock d) :
    intState d lam W g ψ₀ 0 = ψ₀ := by
  simp [intState, evolOp_zero]

/-- Applying the free evolution at time `t` to the interaction-picture
state recovers the interacting evolution (the group law at the
`evolOp` level). -/
theorem free_apply_intState (ψ₀ : FermionicFock d) (t : ℝ) :
    evolOp (freeHamiltonian_isSymmetric d lam) t
        (intState d lam W g ψ₀ t)
      = evolOp (hamInt_isSymmetric d lam W g) t ψ₀ :=
  evolOp_apply_neg_apply _ t _

/-- The interaction-picture state is continuous in time. -/
theorem continuous_intState (ψ₀ : FermionicFock d) :
    Continuous (intState d lam W g ψ₀) := by
  have hfun : intState d lam W g ψ₀
      = fun s => evolCLM (freeHamiltonian_isSymmetric d lam) (-s)
          (evolOp (hamInt_isSymmetric d lam W g) s ψ₀) := rfl
  rw [hfun]
  have hdiff : Differentiable ℝ
      fun s => evolOp (hamInt_isSymmetric d lam W g) s ψ₀ :=
    fun s => (hasDerivAt_evolOp_apply (hamInt_isSymmetric d lam W g) ψ₀
      s).differentiableAt
  exact ((continuous_evolCLM _).comp continuous_neg).clm_apply
    hdiff.continuous

/-- Continuity of Heisenberg-picture integrands against a continuous
vector curve (the integrand shape of the Duhamel identity). -/
theorem continuous_heisenberg_integrand {u : ℝ → FermionicFock d}
    (hu : Continuous u) :
    Continuous fun s => (-Complex.I)
      • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
          ((g : ℂ) • intOp d W)) (u s) := by
  have h2 : (fun s => (-Complex.I)
        • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
            ((g : ℂ) • intOp d W)) (u s))
      = fun s => (-Complex.I) • (intPictCLM d lam W g s (u s)) :=
    funext fun s => by rw [intPictCLM_apply]
  rw [h2]
  have hconst : Continuous fun _ : ℝ => (-Complex.I : ℂ) := continuous_const
  exact hconst.smul ((continuous_intPictCLM d lam W g).clm_apply hu)

/-- The interaction-picture state as the exponential product of §1:
`F(t)ψ₀ = (exp (t • (−A₀)) * exp (t • A)) ψ₀`, with `A₀` the free
generator and `A` the interacting generator as continuous linear maps. -/
theorem intState_eq_mul_exp (ψ₀ : FermionicFock d) (t : ℝ) :
    intState d lam W g ψ₀ t
      = (NormedSpace.exp (t • (-genCLM (freeHamiltonian_isSymmetric d lam)))
          * NormedSpace.exp (t • genCLM (hamInt_isSymmetric d lam W g)))
          ψ₀ := by
  rw [ContinuousLinearMap.mul_apply]
  have e1 : NormedSpace.exp (t • genCLM (hamInt_isSymmetric d lam W g)) ψ₀
      = evolOp (hamInt_isSymmetric d lam W g) t ψ₀ :=
    (evolOp_apply_eq_exp _ t ψ₀).symm
  have e2 : NormedSpace.exp (t • (-genCLM (freeHamiltonian_isSymmetric d lam)))
      = evolCLM (freeHamiltonian_isSymmetric d lam) (-t) := by
    rw [show t • (-genCLM (freeHamiltonian_isSymmetric d lam))
        = (-t) • genCLM (freeHamiltonian_isSymmetric d lam) by
      rw [smul_neg, neg_smul]]
    exact (evolCLM_eq_exp _ _).symm
  rw [e1, e2, evolCLM_apply]
  rfl

/-- The differential equation of the interaction-picture state:
`F'(t)ψ₀ = −i • V_I(t) (F(t)ψ₀)`. The proof differentiates the
exponential product of `intState_eq_mul_exp` in the CLM algebra
(`HasDerivAt.mul`), applies the result to the fixed vector `ψ₀`
(`hasDerivAt_apply_const`), and simplifies: the free-generator terms
cancel against the free part of the interacting Hamiltonian (via
`evolOp_apply_commute`), leaving exactly the interaction-picture
perturbation. -/
theorem hasDerivAt_intState (ψ₀ : FermionicFock d) (t : ℝ) :
    HasDerivAt (intState d lam W g ψ₀)
      ((-Complex.I) • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) t
        ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ t)) t := by
  haveI : CompleteSpace (FermionicFock d) := FiniteDimensional.complete ℂ _
  have hM : HasDerivAt
      (fun s => NormedSpace.exp (s • (-genCLM (freeHamiltonian_isSymmetric d lam)))
        * NormedSpace.exp (s • genCLM (hamInt_isSymmetric d lam W g)))
      (((-genCLM (freeHamiltonian_isSymmetric d lam))
          * NormedSpace.exp (t • (-genCLM (freeHamiltonian_isSymmetric d lam))))
        * NormedSpace.exp (t • genCLM (hamInt_isSymmetric d lam W g))
        + NormedSpace.exp (t • (-genCLM (freeHamiltonian_isSymmetric d lam)))
          * (genCLM (hamInt_isSymmetric d lam W g)
            * NormedSpace.exp (t • genCLM (hamInt_isSymmetric d lam W g)))) t :=
    (hasDerivAt_exp_smul_const'
      (-genCLM (freeHamiltonian_isSymmetric d lam)) t).mul
      (hasDerivAt_exp_smul_const' (genCLM (hamInt_isSymmetric d lam W g)) t)
  have hF := hasDerivAt_apply_const hM ψ₀
  have hfun : (fun s => intState d lam W g ψ₀ s)
      = fun s => (NormedSpace.exp (s • (-genCLM (freeHamiltonian_isSymmetric d lam)))
          * NormedSpace.exp (s • genCLM (hamInt_isSymmetric d lam W g))) ψ₀ :=
    funext (intState_eq_mul_exp d lam W g ψ₀)
  show HasDerivAt (fun s => intState d lam W g ψ₀ s)
    ((-Complex.I) • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) t
      ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ t)) t
  rw [hfun]
  apply hF.congr_deriv
  -- The algebra step: expand the derivative value.
  have e1 : NormedSpace.exp (t • genCLM (hamInt_isSymmetric d lam W g))
      = evolCLM (hamInt_isSymmetric d lam W g) t := (evolCLM_eq_exp _ _).symm
  have e2 : NormedSpace.exp (t • (-genCLM (freeHamiltonian_isSymmetric d lam)))
      = evolCLM (freeHamiltonian_isSymmetric d lam) (-t) := by
    rw [show t • (-genCLM (freeHamiltonian_isSymmetric d lam))
        = (-t) • genCLM (freeHamiltonian_isSymmetric d lam) by
      rw [smul_neg, neg_smul]]
    exact (evolCLM_eq_exp _ _).symm
  rw [e1, e2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    evolCLM_apply, ContinuousLinearMap.neg_apply, genCLM_apply,
    heisenbergEvol_apply, intState, hamInt, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul, evolOp_apply_commute,
    evolOp_apply_neg_apply, smul_add]
  module

/-- **Dyson-β (T1), Duhamel form:** the interaction-picture state
satisfies the exact integral equation
`F(t)ψ₀ = ψ₀ + ∫₀ᵗ −i • V_I(s) (F(s)ψ₀) ds`
(fundamental theorem of calculus applied to `hasDerivAt_intState`). -/
theorem duhamel_interaction (ψ₀ : FermionicFock d) (t : ℝ) :
    intState d lam W g ψ₀ t
      = ψ₀ + ∫ s in (0)..t, (-Complex.I)
          • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
              ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ s) := by
  have hInt : IntervalIntegrable
      (fun s => (-Complex.I)
        • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
            ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ s))
      MeasureTheory.volume 0 t :=
    (continuous_heisenberg_integrand d lam W g
      (continuous_intState d lam W g ψ₀)).intervalIntegrable 0 t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := intState d lam W g ψ₀)
    (f' := fun s => (-Complex.I)
      • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
          ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ s))
    (fun x _ => hasDerivAt_intState d lam W g ψ₀ x) hInt
  rw [intState_zero] at h
  rw [h]
  exact (add_sub_cancel _ _).symm

/-- Continuity of the Dyson-α integrand (interaction-picture curve
applied to a fixed vector, with the scalar factor). -/
theorem continuous_dyson_integrand (ψ₀ : FermionicFock d) :
    Continuous fun s => (-Complex.I) • (intPictCLM d lam W g s ψ₀) := by
  have hconst : Continuous fun _ : ℝ => (-Complex.I : ℂ) := continuous_const
  exact hconst.smul ((continuous_intPictCLM d lam W g).clm_apply
    continuous_const)

/-- **Dyson-β (T1), first-order form:** splitting `F(s) = ψ₀ + (F(s) − ψ₀)`
inside the Duhamel integral exhibits the Dyson-α term `W₁(t)ψ₀` plus an
explicit integral remainder:
`F(t)ψ₀ = ψ₀ + W₁(t)ψ₀ + ∫₀ᵗ −i • V_I(s)(F(s)ψ₀ − ψ₀) ds`.
The remainder is a theorem-level term, not a notation — this is what
makes "first-order" an approximation statement. -/
theorem duhamel_first_order (ψ₀ : FermionicFock d) (t : ℝ) :
    intState d lam W g ψ₀ t
      = ψ₀ + dysonW1 d lam W g t ψ₀
        + ∫ s in (0)..t, (-Complex.I)
            • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
                ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ s - ψ₀) := by
  have hInt1 : IntervalIntegrable
      (fun s => (-Complex.I) • (intPictCLM d lam W g s ψ₀))
      MeasureTheory.volume 0 t :=
    (continuous_dyson_integrand d lam W g ψ₀).intervalIntegrable 0 t
  have hInt2 : IntervalIntegrable
      (fun s => (-Complex.I)
        • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
            ((g : ℂ) • intOp d W)) (intState d lam W g ψ₀ s - ψ₀))
      MeasureTheory.volume 0 t :=
    (continuous_heisenberg_integrand d lam W g
      ((continuous_intState d lam W g ψ₀).sub
        continuous_const)).intervalIntegrable 0 t
  rw [duhamel_interaction, dysonW1_apply, add_assoc,
    ← intervalIntegral.integral_add hInt1 hInt2]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [intPictCLM_apply, smul_apply]
  rw [← smul_add, ← map_add, add_sub_cancel]

/-- **Dyson-β (T1), Schrödinger-picture form:** applying the free
evolution `U₀(t)` to the first-order interaction-picture expansion:
`U(t)ψ₀ = U₀(t)ψ₀ + U₀(t)(W₁(t)ψ₀) + U₀(t)(remainder)`. -/
theorem dyson_first_order_schrodinger (ψ₀ : FermionicFock d) (t : ℝ) :
    evolOp (hamInt_isSymmetric d lam W g) t ψ₀
      = evolOp (freeHamiltonian_isSymmetric d lam) t ψ₀
        + evolOp (freeHamiltonian_isSymmetric d lam) t
            (dysonW1 d lam W g t ψ₀)
        + evolOp (freeHamiltonian_isSymmetric d lam) t
            (∫ s in (0)..t, (-Complex.I)
              • (heisenbergEvol (freeHamiltonian_isSymmetric d lam) s
                  ((g : ℂ) • intOp d W))
                (intState d lam W g ψ₀ s - ψ₀)) := by
  have h := congrArg (evolOp (freeHamiltonian_isSymmetric d lam) t)
    (duhamel_first_order d lam W g ψ₀ t)
  rw [map_add, map_add, free_apply_intState] at h
  exact h

end DysonBeta

#print axioms evolOp_apply_eq_exp
#print axioms evolCLM_eq_exp
#print axioms dysonW1_apply
#print axioms hasDerivAt_dysonW1
#print axioms duhamel_interaction
#print axioms duhamel_first_order
#print axioms dyson_first_order_schrodinger

end ThetLogos
