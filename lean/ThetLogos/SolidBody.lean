import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# ThetLogos.SolidBody — the solid-body foundation (brick 1)

The rigid-body foundation for the Dzhanibekov / intermediate-axis work:
a free rigid body with distinct principal moments, its Euler vector
field, the two body-frame conservation laws, and the linearized
intermediate-axis instability with the growing mode exhibited in
closed form. Commissioned 2026-10-25 (Jeff: "build the solid body");
the priced prerequisite for formalizing the variable-intermediate-axis
theorem (whose moments vary in time — this brick's moments are FIXED).

## Tiers, on its face

* **Definitions** (the body, its moments, energy, angular momentum,
  the Euler field) — pure data, no tier.
* **T1** (machine-checked, from hypotheses): the two algebraic
  vanishing identities; conservation of rotational energy `T` and of
  body-frame `|L|²` along any trajectory satisfying Euler's equations;
  positivity of the growth rate; the exhibited sinh/cosh mode solving
  the linearized intermediate-axis system and its unboundedness
  (linear instability, literally); the stable-axis sin/cos contrast
  (stretch).
* **T4** (physics input, NOT proved here): Euler's equations
  themselves. Every conservation/instability theorem takes
  "ω obeys the Euler field" as a hypothesis; that a physical rigid
  body obeys it is the classical-mechanics input.
* **NO CLAIM** that any physical body obeys Euler's equations
  exactly, and no claim about the real Earth (a deformable,
  ocean-bearing body — the ocean composite is brick 2,
  `SolidBodyOcean`).

Frame note (honesty): the conserved pair proved here is the
BODY-frame pair (T, |L|²). Space-frame conservation of the vector L
itself needs the frame rotation (Poinsot), and is NOT claimed here.

Cyclic convention (fixed once, here): indices are `Fin 3` with
principal moments (I₁, I₂, I₃) at (0, 1, 2), and the Euler field is
  ω̇ᵢ = ((Iⱼ − Iₖ)/Iᵢ) · ωⱼ · ωₖ   for (i, j, k) cyclic,
i.e. ω̇₀ = ((I₂−I₃)/I₁)·ω₁·ω₂, ω̇₁ = ((I₃−I₁)/I₂)·ω₂·ω₀,
     ω̇₂ = ((I₁−I₂)/I₃)·ω₀·ω₁.
-/

namespace ThetLogos

/-- A solid (rigid) body, recorded by its three principal moments of
inertia, each strictly positive. -/
structure SolidBody where
  I1 : ℝ
  I2 : ℝ
  I3 : ℝ
  I1_pos : 0 < I1
  I2_pos : 0 < I2
  I3_pos : 0 < I3

/-- The principal moments as a function on axes: `0 ↦ I₁`, `1 ↦ I₂`,
`2 ↦ I₃`. -/
def momInertia (b : SolidBody) : Fin 3 → ℝ := ![b.I1, b.I2, b.I3]

/-- Angular momentum in the body frame, componentwise `Lᵢ = Iᵢ·ωᵢ`. -/
def angMom (b : SolidBody) (ω : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => momInertia b i * ω i

/-- Rotational kinetic energy `T = ½·Σᵢ Iᵢ·ωᵢ²`. -/
noncomputable def rotEnergy (b : SolidBody) (ω : Fin 3 → ℝ) : ℝ :=
  (1 / 2) * ∑ i, momInertia b i * (ω i) ^ 2

/-- Squared body-frame angular momentum `|L|² = Σᵢ (Iᵢ·ωᵢ)²`. -/
def angMomSq (b : SolidBody) (ω : Fin 3 → ℝ) : ℝ :=
  ∑ i, (momInertia b i * ω i) ^ 2

/-- The Euler vector field for a free rigid body, with the cyclic
convention fixed in the module header:
`ω̇ᵢ = ((Iⱼ − Iₖ)/Iᵢ)·ωⱼ·ωₖ` for `(i, j, k)` cyclic. -/
noncomputable def eulerRHS (b : SolidBody) (ω : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![ ((b.I2 - b.I3) / b.I1) * ω 1 * ω 2,
     ((b.I3 - b.I1) / b.I2) * ω 2 * ω 0,
     ((b.I1 - b.I2) / b.I3) * ω 0 * ω 1 ]

@[simp] lemma momInertia_zero (b : SolidBody) : momInertia b 0 = b.I1 := rfl
@[simp] lemma momInertia_one (b : SolidBody) : momInertia b 1 = b.I2 := rfl
@[simp] lemma momInertia_two (b : SolidBody) : momInertia b 2 = b.I3 := rfl

@[simp] lemma eulerRHS_zero (b : SolidBody) (ω : Fin 3 → ℝ) :
    eulerRHS b ω 0 = ((b.I2 - b.I3) / b.I1) * ω 1 * ω 2 := rfl
@[simp] lemma eulerRHS_one (b : SolidBody) (ω : Fin 3 → ℝ) :
    eulerRHS b ω 1 = ((b.I3 - b.I1) / b.I2) * ω 2 * ω 0 := rfl
@[simp] lemma eulerRHS_two (b : SolidBody) (ω : Fin 3 → ℝ) :
    eulerRHS b ω 2 = ((b.I1 - b.I2) / b.I3) * ω 0 * ω 1 := rfl

/-! ## Algebraic core: the two vanishing identities -/

/-- The Euler field does no work: `Σᵢ Iᵢ·ωᵢ·ω̇ᵢ = 0` identically.
This is the infinitesimal reason energy is conserved. -/
theorem eulerRHS_energy_vanishes (b : SolidBody) (ω : Fin 3 → ℝ) :
    ∑ i, momInertia b i * ω i * eulerRHS b ω i = 0 := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two,
    eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-- The Euler field does not change `|L|²`:
`Σᵢ (Iᵢ·ωᵢ)·Iᵢ·ω̇ᵢ = 0` identically. -/
theorem eulerRHS_angMomSq_vanishes (b : SolidBody) (ω : Fin 3 → ℝ) :
    ∑ i, (momInertia b i * ω i) * momInertia b i * eulerRHS b ω i = 0 := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two,
    eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-! ## Conservation along Euler trajectories

Throughout, `ω : ℝ → Fin 3 → ℝ` is a trajectory, `hω` says it obeys
the Euler field (the T4 physics input, taken as hypothesis), and
`hωdiff` is the regularity the chain rule needs, stated honestly as
a hypothesis: every coordinate function is differentiable everywhere. -/

theorem hasDerivAt_rotEnergy (b : SolidBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i)) (t : ℝ) :
    HasDerivAt (fun s => rotEnergy b (ω s)) 0 t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i) (eulerRHS b (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hcomp : ∀ i : Fin 3, HasDerivAt (fun s => momInertia b i * (ω s i) ^ 2)
      (momInertia b i * (2 * ω t i * eulerRHS b (ω t) i)) t := by
    intro i
    have hmul := (hcoord i).mul (hcoord i)
    have hcm := hmul.const_mul (momInertia b i)
    have hfun : (fun s => momInertia b i * (ω s i) ^ 2)
        = (fun s => momInertia b i * (ω s i * ω s i)) := by
      funext s
      rw [pow_two]
    rw [hfun]
    convert hcm using 1
    ring
  have hsum : HasDerivAt (fun s => ∑ i, momInertia b i * (ω s i) ^ 2)
      (∑ i, momInertia b i * (2 * ω t i * eulerRHS b (ω t) i)) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have htot := hsum.const_mul (1 / 2)
  have hfun2 : (fun s => rotEnergy b (ω s))
      = (fun s => (1 / 2) * ∑ i, momInertia b i * (ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert htot using 1
  have hval : ∑ i, momInertia b i * (2 * ω t i * eulerRHS b (ω t) i)
      = 2 * ∑ i, momInertia b i * ω t i * eulerRHS b (ω t) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hval, eulerRHS_energy_vanishes, mul_zero, mul_zero]

theorem hasDerivAt_angMomSq (b : SolidBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i)) (t : ℝ) :
    HasDerivAt (fun s => angMomSq b (ω s)) 0 t := by
  have hcoord : ∀ i : Fin 3, HasDerivAt (fun s => ω s i) (eulerRHS b (ω t) i) t := by
    intro i
    have h := (hωdiff i t).hasDerivAt
    rwa [hω t i] at h
  have hcomp : ∀ i : Fin 3, HasDerivAt (fun s => (momInertia b i * ω s i) ^ 2)
      (2 * (momInertia b i * ω t i) * (momInertia b i * eulerRHS b (ω t) i)) t := by
    intro i
    have hbase := (hcoord i).const_mul (momInertia b i)
    have hmul := hbase.mul hbase
    have hfun : (fun s => (momInertia b i * ω s i) ^ 2)
        = (fun s => (momInertia b i * ω s i) * (momInertia b i * ω s i)) := by
      funext s
      rw [pow_two]
    rw [hfun]
    convert hmul using 1
    ring
  have hsum : HasDerivAt (fun s => ∑ i, (momInertia b i * ω s i) ^ 2)
      (∑ i, 2 * (momInertia b i * ω t i) * (momInertia b i * eulerRHS b (ω t) i)) t :=
    HasDerivAt.fun_sum (fun i _ => hcomp i)
  have hfun2 : (fun s => angMomSq b (ω s))
      = (fun s => ∑ i, (momInertia b i * ω s i) ^ 2) := by
    funext s
    rfl
  rw [hfun2]
  convert hsum using 1
  have hval : ∑ i, 2 * (momInertia b i * ω t i) * (momInertia b i * eulerRHS b (ω t) i)
      = 2 * ∑ i, (momInertia b i * ω t i) * momInertia b i * eulerRHS b (ω t) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hval, eulerRHS_angMomSq_vanishes, mul_zero]

/-- Rotational energy is constant along any Euler trajectory. -/
theorem rotEnergy_const (b : SolidBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i)) (t₁ t₂ : ℝ) :
    rotEnergy b (ω t₁) = rotEnergy b (ω t₂) :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_rotEnergy b ω hω hωdiff t).differentiableAt)
    (fun t => (hasDerivAt_rotEnergy b ω hω hωdiff t).deriv) t₁ t₂

/-- Body-frame `|L|²` is constant along any Euler trajectory.
(The space-frame vector `L` is also conserved in reality, but that
needs the frame rotation and is not proved here.) -/
theorem angMomSq_const (b : SolidBody) (ω : ℝ → Fin 3 → ℝ)
    (hω : ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i)
    (hωdiff : ∀ i, Differentiable ℝ (fun s => ω s i)) (t₁ t₂ : ℝ) :
    angMomSq b (ω t₁) = angMomSq b (ω t₂) :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_angMomSq b ω hω hωdiff t).differentiableAt)
    (fun t => (hasDerivAt_angMomSq b ω hω hωdiff t).deriv) t₁ t₂

/-! ## Intermediate-axis instability, linearized core

Fix the strict ordering `I₁ < I₂ < I₃` and a spin `Ω > 0` about the
intermediate axis (axis 1, moment `I₂`). Writing `x = δω₀`,
`z = δω₂` for the perturbations, the linearization of Euler's
equations about `(0, Ω, 0)` is
  `x' = a·z`,  `z' = b·x`,
with `a = ((I₂−I₃)/I₁)·Ω` and `b = ((I₁−I₂)/I₃)·Ω`. Both are
negative, so `a·b > 0`: the system has a real growing mode with rate
`γ = Ω·√(((I₃−I₂)(I₂−I₁))/(I₁I₃))`, namely `γ² = a·b`. -/

/-- Linearized coefficient: `x' = linCoeffA · z` for a spin about
the intermediate axis. -/
noncomputable def linCoeffA (b : SolidBody) (Ω : ℝ) : ℝ := ((b.I2 - b.I3) / b.I1) * Ω

/-- Linearized coefficient: `z' = linCoeffB · x` for a spin about
the intermediate axis. -/
noncomputable def linCoeffB (b : SolidBody) (Ω : ℝ) : ℝ := ((b.I1 - b.I2) / b.I3) * Ω

/-- The growth rate `γ = Ω·√(((I₃−I₂)(I₂−I₁))/(I₁·I₃))` of the
intermediate-axis instability. -/
noncomputable def growthRate (b : SolidBody) (Ω : ℝ) : ℝ :=
  Ω * Real.sqrt (((b.I3 - b.I2) * (b.I2 - b.I1)) / (b.I1 * b.I3))

/-- The amplitude coefficient of the growing mode's `z` component:
`z(t) = modeCoeff · cosh (γt)` pairs with `x(t) = sinh (γt)`. -/
noncomputable def modeCoeff (b : SolidBody) (Ω : ℝ) : ℝ :=
  growthRate b Ω / linCoeffA b Ω

/-- Growing mode, `x` component: `x(t) = sinh (γt)`. -/
noncomputable def modeX (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  Real.sinh (growthRate b Ω * t)

/-- Growing mode, `z` component: `z(t) = modeCoeff · cosh (γt)`. -/
noncomputable def modeZ (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  modeCoeff b Ω * Real.cosh (growthRate b Ω * t)

theorem linCoeffA_ne_zero (b : SolidBody) (Ω : ℝ) (h23 : b.I2 < b.I3)
    (hΩ : 0 < Ω) : linCoeffA b Ω ≠ 0 := by
  unfold linCoeffA
  apply mul_ne_zero _ hΩ.ne'
  apply div_ne_zero _ b.I1_pos.ne'
  exact sub_ne_zero.mpr h23.ne

theorem growthRate_pos (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) : 0 < growthRate b Ω := by
  unfold growthRate
  exact mul_pos hΩ (Real.sqrt_pos.mpr
    (div_pos (mul_pos (sub_pos.mpr h23) (sub_pos.mpr h12))
      (mul_pos b.I1_pos b.I3_pos)))

/-- The defining identity of the growth rate: `γ² = a·b`. -/
theorem growthRate_sq (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) :
    growthRate b Ω ^ 2 = linCoeffA b Ω * linCoeffB b Ω := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have hfrac : (0 : ℝ) ≤ ((b.I3 - b.I2) * (b.I2 - b.I1)) / (b.I1 * b.I3) :=
    le_of_lt (div_pos (mul_pos (sub_pos.mpr h23) (sub_pos.mpr h12))
      (mul_pos b.I1_pos b.I3_pos))
  unfold growthRate linCoeffA linCoeffB
  rw [mul_pow, Real.sq_sqrt hfrac]
  field_simp
  ring

/-- The exhibited mode satisfies the first linearized equation:
`x'(t) = a · z(t)` for all `t`. -/
theorem modeX_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeX b Ω) t = linCoeffA b Ω * modeZ b Ω t := by
  have hA : linCoeffA b Ω ≠ 0 := linCoeffA_ne_zero b Ω h23 hΩ
  have hderiv : HasDerivAt (modeX b Ω)
      (Real.cosh (growthRate b Ω * t) * growthRate b Ω) t := by
    have h1 : HasDerivAt (fun s => growthRate b Ω * s) (growthRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (growthRate b Ω)
    have h2 := (Real.hasDerivAt_sinh (growthRate b Ω * t)).comp t h1
    have hfun : modeX b Ω = (fun s => Real.sinh (growthRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h2
  rw [hderiv.deriv]
  have hfunZ : modeZ b Ω t
      = (growthRate b Ω / linCoeffA b Ω) * Real.cosh (growthRate b Ω * t) := rfl
  rw [hfunZ]
  field_simp

/-- The exhibited mode satisfies the second linearized equation:
`z'(t) = b · x(t)` for all `t`. The coefficient works because
`modeCoeff · γ = γ²/a = b`, using `γ² = a·b`. -/
theorem modeZ_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeZ b Ω) t = linCoeffB b Ω * modeX b Ω t := by
  have hA : linCoeffA b Ω ≠ 0 := linCoeffA_ne_zero b Ω h23 hΩ
  have hcoeff : modeCoeff b Ω * growthRate b Ω = linCoeffB b Ω := by
    have hsq := growthRate_sq b Ω h12 h23
    unfold modeCoeff
    rw [div_mul_eq_mul_div, ← pow_two, hsq]
    exact mul_div_cancel_left₀ _ hA
  have hderiv : HasDerivAt (modeZ b Ω)
      (modeCoeff b Ω * (Real.sinh (growthRate b Ω * t) * growthRate b Ω)) t := by
    have h1 : HasDerivAt (fun s => growthRate b Ω * s) (growthRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (growthRate b Ω)
    have h2 := (Real.hasDerivAt_cosh (growthRate b Ω * t)).comp t h1
    have h3 := h2.const_mul (modeCoeff b Ω)
    have hfun : modeZ b Ω
        = (fun s => modeCoeff b Ω * Real.cosh (growthRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h3
  rw [hderiv.deriv]
  have hfunX : modeX b Ω t = Real.sinh (growthRate b Ω * t) := rfl
  rw [hfunX]
  calc modeCoeff b Ω * (Real.sinh (growthRate b Ω * t) * growthRate b Ω)
      = (modeCoeff b Ω * growthRate b Ω) * Real.sinh (growthRate b Ω * t) := by
        ring
    _ = linCoeffB b Ω * Real.sinh (growthRate b Ω * t) := by rw [hcoeff]

/-- The spin `sinh` tends to infinity: the engine behind the
unboundedness corollary. -/
theorem tendsto_sinh_atTop : Filter.Tendsto Real.sinh Filter.atTop Filter.atTop := by
  have hle : ∀ᶠ u in Filter.atTop, (Real.exp u - 1) / 2 ≤ Real.sinh u := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    have h1 : Real.exp (-u) ≤ 1 := by
      calc Real.exp (-u) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
    rw [Real.sinh_eq]
    linarith
  have hexp : Filter.Tendsto (fun u => (Real.exp u - 1) / 2)
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun u => Real.exp u - 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono' Filter.atTop
        (Filter.Eventually.of_forall (fun u => by
          show u ≤ Real.exp u - 1
          have h := Real.add_one_le_exp u
          linarith))
        Filter.tendsto_id
    exact h1.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  exact Filter.tendsto_atTop_mono' Filter.atTop hle hexp

/-- **Intermediate-axis linear instability, literally:** the
exhibited perturbation mode is unbounded as `t → ∞`. Together with
`modeX_deriv` and `modeZ_deriv` (the mode solves the linearized
system) and `growthRate_pos` (`γ > 0`), this is the linearized core
of the tennis-racket / Dzhanibekov instability: spin about the
intermediate axis is linearly unstable. -/
theorem intermediate_linear_unstable (b : SolidBody) (Ω : ℝ)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) :
    Filter.Tendsto (modeX b Ω) Filter.atTop Filter.atTop := by
  have hγ : 0 < growthRate b Ω := growthRate_pos b Ω h12 h23 hΩ
  have hfun : modeX b Ω = (fun t => Real.sinh (growthRate b Ω * t)) := by
    funext t
    rfl
  rw [hfun]
  have hmul : Filter.Tendsto (fun t => growthRate b Ω * t)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hγ Filter.tendsto_id
  exact tendsto_sinh_atTop.comp hmul

/-! ## Stretch: the stable-axis contrast

Spin `Ω > 0` about the MAXIMUM axis (axis 2, moment `I₃`), same
ordering `I₁ < I₂ < I₃`. With `x = δω₀`, `y = δω₁`, the
linearization is `x' = a·y` (the same `a = linCoeffA` as before)
and `y' = c·x` with `c = ((I₃−I₁)/I₂)·Ω > 0`. Now `a·c < 0`, so
instead of a growth rate there is an oscillation frequency
`ν = Ω·√(((I₃−I₂)(I₃−I₁))/(I₁I₂))`, `ν² = −a·c`, and the exhibited
mode `x(t) = sin (νt)`, `y(t) = (ν/a)·cos (νt)` is a bounded
oscillation — the stable seat, in the same language. -/

/-- Linearized coefficient `y' = stabCoeffB · x` for a spin about
the maximum axis. -/
noncomputable def stabCoeffB (b : SolidBody) (Ω : ℝ) : ℝ := ((b.I3 - b.I1) / b.I2) * Ω

/-- The oscillation frequency `ν = Ω·√(((I₃−I₂)(I₃−I₁))/(I₁·I₂))`
for spin about the maximum axis. -/
noncomputable def stableRate (b : SolidBody) (Ω : ℝ) : ℝ :=
  Ω * Real.sqrt (((b.I3 - b.I2) * (b.I3 - b.I1)) / (b.I1 * b.I2))

/-- Amplitude coefficient of the stable mode's `y` component. -/
noncomputable def stabCoeff (b : SolidBody) (Ω : ℝ) : ℝ :=
  stableRate b Ω / linCoeffA b Ω

/-- Stable mode, `x` component: `x(t) = sin (νt)`. -/
noncomputable def modeXs (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  Real.sin (stableRate b Ω * t)

/-- Stable mode, `y` component: `y(t) = stabCoeff · cos (νt)`. -/
noncomputable def modeYs (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  stabCoeff b Ω * Real.cos (stableRate b Ω * t)

theorem stableRate_pos (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) : 0 < stableRate b Ω := by
  unfold stableRate
  exact mul_pos hΩ (Real.sqrt_pos.mpr
    (div_pos (mul_pos (sub_pos.mpr h23) (sub_pos.mpr (lt_trans h12 h23)))
      (mul_pos b.I1_pos b.I2_pos)))

/-- The defining identity of the oscillation frequency:
`ν² = −(a·c)` — note the sign, opposite to the intermediate case. -/
theorem stableRate_sq (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) :
    stableRate b Ω ^ 2 = -(linCoeffA b Ω * stabCoeffB b Ω) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have hfrac : (0 : ℝ) ≤ ((b.I3 - b.I2) * (b.I3 - b.I1)) / (b.I1 * b.I2) :=
    le_of_lt (div_pos (mul_pos (sub_pos.mpr h23) (sub_pos.mpr (lt_trans h12 h23)))
      (mul_pos b.I1_pos b.I2_pos))
  unfold stableRate linCoeffA stabCoeffB
  rw [mul_pow, Real.sq_sqrt hfrac]
  field_simp
  ring

/-- The stable mode satisfies `x'(t) = a · y(t)`. -/
theorem modeXs_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeXs b Ω) t = linCoeffA b Ω * modeYs b Ω t := by
  have hA : linCoeffA b Ω ≠ 0 := linCoeffA_ne_zero b Ω h23 hΩ
  have hderiv : HasDerivAt (modeXs b Ω)
      (Real.cos (stableRate b Ω * t) * stableRate b Ω) t := by
    have h1 : HasDerivAt (fun s => stableRate b Ω * s) (stableRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (stableRate b Ω)
    have h2 := (Real.hasDerivAt_sin (stableRate b Ω * t)).comp t h1
    have hfun : modeXs b Ω = (fun s => Real.sin (stableRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h2
  rw [hderiv.deriv]
  have hfunY : modeYs b Ω t
      = (stableRate b Ω / linCoeffA b Ω) * Real.cos (stableRate b Ω * t) := rfl
  rw [hfunY]
  field_simp

/-- The stable mode satisfies `y'(t) = c · x(t)`. The coefficient
works because `stabCoeff · ν = ν²/a = −c`, using `ν² = −a·c`. -/
theorem modeYs_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeYs b Ω) t = stabCoeffB b Ω * modeXs b Ω t := by
  have hA : linCoeffA b Ω ≠ 0 := linCoeffA_ne_zero b Ω h23 hΩ
  have hcoeff : stabCoeff b Ω * stableRate b Ω = -(stabCoeffB b Ω) := by
    have hsq := stableRate_sq b Ω h12 h23
    have hfrac : stabCoeff b Ω * stableRate b Ω
        = (stableRate b Ω ^ 2) / linCoeffA b Ω := by
      unfold stabCoeff
      field_simp
    rw [hfrac, hsq, neg_div, mul_div_cancel_left₀ _ hA]
  have hderiv : HasDerivAt (modeYs b Ω)
      (stabCoeff b Ω * (-Real.sin (stableRate b Ω * t) * stableRate b Ω)) t := by
    have h1 : HasDerivAt (fun s => stableRate b Ω * s) (stableRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (stableRate b Ω)
    have h2 := (Real.hasDerivAt_cos (stableRate b Ω * t)).comp t h1
    have h3 := h2.const_mul (stabCoeff b Ω)
    have hfun : modeYs b Ω
        = (fun s => stabCoeff b Ω * Real.cos (stableRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h3
  rw [hderiv.deriv]
  have hfunX : modeXs b Ω t = Real.sin (stableRate b Ω * t) := rfl
  rw [hfunX]
  calc stabCoeff b Ω * (-Real.sin (stableRate b Ω * t) * stableRate b Ω)
      = -(stabCoeff b Ω * stableRate b Ω) * Real.sin (stableRate b Ω * t) := by
        ring
    _ = stabCoeffB b Ω * Real.sin (stableRate b Ω * t) := by rw [hcoeff]; ring

/-- The stable mode is a bounded oscillation: `|x(t)| ≤ 1` for
all `t` — the maximum-axis seat does not run away. -/
theorem modeXs_bounded (b : SolidBody) (Ω : ℝ) (t : ℝ) :
    |modeXs b Ω t| ≤ 1 := by
  have hfun : modeXs b Ω t = Real.sin (stableRate b Ω * t) := rfl
  rw [hfun]
  exact Real.abs_sin_le_one _

end ThetLogos
