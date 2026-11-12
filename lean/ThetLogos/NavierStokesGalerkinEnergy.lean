import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Navier–Stokes tunnel T1

TUNNEL T1 / finite Galerkin model only / NO CLAIM / parts of Clay statement closed 0.

This module formalizes only an abstract finite-dimensional Galerkin energy
identity.  The vector field is taken in the form
`F(v) = -B(v, v) - ν • A v + f`, stored below as
`-(B v v) - ν • (A v) + f`.

It is not a PDE existence, smoothness, or blow-up theorem.
-/

open scoped RealInnerProductSpace InnerProductSpace

namespace ThetLogos

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Data for the finite-dimensional Galerkin model.

The convection term is energy-neutral and the viscous operator is
nonnegative in the quadratic-form sense. -/
structure NSGalerkinData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] where
  /-- Bilinear convection operator. -/
  B : V →ₗ[ℝ] V →ₗ[ℝ] V
  /-- Linear viscous operator. -/
  A : V →ₗ[ℝ] V
  /-- Viscosity. -/
  ν : ℝ
  /-- Forcing vector. -/
  f : V
  /-- The viscosity is strictly positive. -/
  nu_pos : 0 < ν
  /-- Convection does no work: `⟪B v v, v⟫_ℝ = 0`. -/
  convection_energy_neutral : ∀ v : V, ⟪B v v, v⟫_ℝ = 0
  /-- The viscous quadratic form is nonnegative. -/
  viscous_nonnegative : ∀ v : V, 0 ≤ ⟪A v, v⟫_ℝ

/-- The finite Galerkin vector field, in the form
`-(B v v) - ν • (A v) + f`. -/
def NSGalerkinField (D : NSGalerkinData V) (v : V) : V :=
  -(D.B v v) - D.ν • (D.A v) + D.f

/-- Pointwise energy-pairing identity for the finite Galerkin field.

The field is placed in the first argument of the real inner product; over
`ℝ` this is the same pairing as the symmetric opposite order. -/
theorem nsGalerkin_energy_pairing (D : NSGalerkinData V) (v : V) :
    ⟪NSGalerkinField D v, v⟫_ℝ =
      (-D.ν) * ⟪D.A v, v⟫_ℝ + ⟪D.f, v⟫_ℝ := by
  simp [NSGalerkinField, inner_add_left, inner_sub_left, inner_neg_left,
    inner_smul_left, D.convection_energy_neutral v]

/-- A curve is a solution of the finite Galerkin equation on `I` when its
derivative at every point of `I` is the Galerkin field at that point. -/
def NSGalerkinSolutionOn (D : NSGalerkinData V) (I : Set ℝ) (v : ℝ → V) :
    Prop :=
  ∀ t ∈ I, HasDerivAt v (NSGalerkinField D (v t)) t

/-- Derivative form of the finite Galerkin energy identity. -/
theorem nsGalerkin_energy_deriv (D : NSGalerkinData V) {I : Set ℝ}
    {v : ℝ → V} (hsol : NSGalerkinSolutionOn D I v) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2)
      ((-D.ν) * ⟪D.A (v t), v t⟫_ℝ + ⟪D.f, v t⟫_ℝ) t := by
  have hv : HasDerivAt v (NSGalerkinField D (v t)) t := hsol t ht
  have hinner : HasDerivAt (fun s => ⟪v s, v s⟫_ℝ)
      (⟪v t, NSGalerkinField D (v t)⟫_ℝ +
        ⟪NSGalerkinField D (v t), v t⟫_ℝ) t :=
    HasDerivAt.inner ℝ hv hv
  have hcomm : ⟪v t, NSGalerkinField D (v t)⟫_ℝ =
      ⟪NSGalerkinField D (v t), v t⟫_ℝ :=
    real_inner_comm _ _
  have hpair := nsGalerkin_energy_pairing D (v t)
  have hderiv : ⟪v t, NSGalerkinField D (v t)⟫_ℝ +
        ⟪NSGalerkinField D (v t), v t⟫_ℝ =
      2 * ((-D.ν) * ⟪D.A (v t), v t⟫_ℝ + ⟪D.f, v t⟫_ℝ) := by
    rw [hcomm, hpair]; ring
  rw [hderiv] at hinner
  have hhalf := hinner.const_mul (1 / 2 : ℝ)
  have hscale : (1 / 2 : ℝ) *
        (2 * ((-D.ν) * ⟪D.A (v t), v t⟫_ℝ + ⟪D.f, v t⟫_ℝ)) =
      (-D.ν) * ⟪D.A (v t), v t⟫_ℝ + ⟪D.f, v t⟫_ℝ := by
    ring
  rw [hscale] at hhalf
  simpa [real_inner_self_eq_norm_sq] using hhalf

end ThetLogos
