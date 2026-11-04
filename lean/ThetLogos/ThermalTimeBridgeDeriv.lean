import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exponential
import ThetLogos.ThermalTimeBridge
import ThetLogos.ModularTime

open Matrix

namespace ThetLogos

/-!
# ThetLogos.ThermalTimeBridgeDeriv — DERIV-1: the bridge's twelfth clause

The finite thermal-time bridge (`ThetLogos.ThermalTimeBridge`,
`GibbsClock.thermal_time_bridge`) landed eleven of its twelve clauses;
the residue DERIV-1 was the infinitesimal-generator clause

  d/ds at 0 of `G.flow s A`  =  `modularFlux G.generator A`,

unformable in the corpus's own instance context: in the pinned Mathlib
(v4.35.0-rc3) matrices carry no canonical `NormedRing` instance, and
`NormedSpace.exp` on matrices is the norm-free topological exponential.

This module lands the clause by Route A of the bridge dossier (scoped
Frobenius norms). Every norm-sensitive statement below is formed under
`open scoped Matrix.Norms.Frobenius in`, so the Frobenius instances are
local to these declarations and nothing leaks into the ambient instance
context; no landed module is edited. The exponential agreement step of
the dossier's route collapses in this pin: `NormedSpace.exp` is a single
`irreducible_def` constant whose definition (the `expSeries ℚ` sum) does
not depend on any norm instance, so the exponential differentiated here
is definitionally the same constant as the one `modularFlow` is built
from — only the instance arguments carried by the `HasDerivAt` type are
the Frobenius ones, which is exactly the dialect the dossier registers
for this route.

Finite thermal-time structure only. NO CLAIM; dials 0/4.
-/

/-- The positive exponential argument of `modularFlow`, rewritten as a
    real scalar multiple of the generator line `Complex.I • K`
    (Tier T1 — proved). -/
theorem modularFlow_exp_arg_pos {N : ℕ} (s : ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    (Complex.I * (s : ℂ)) • K = s • (Complex.I • K) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

/-- The negative exponential argument of `modularFlow`, rewritten as a
    real scalar multiple of the negated generator line
    (Tier T1 — proved). -/
theorem modularFlow_exp_arg_neg {N : ℕ} (s : ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    (-(Complex.I * (s : ℂ))) • K = s • (-(Complex.I • K)) := by
  rw [smul_neg, ← modularFlow_exp_arg_pos, neg_smul]

/- **The derivative clause for the modular flow** (Tier T1 — proved,
    Frobenius dialect): the real-time modular flow through a matrix
    `A` is differentiable at time `0`, with derivative the modular flux
    `modularFlux K A = Complex.I • (K * A - A * K)`. This is DERIV-1 at
    the `modularFlow` seat. -/
open scoped Matrix.Norms.Frobenius in
theorem modularFlow_hasDerivAt_zero {N : ℕ}
    (K A : Matrix (Fin N) (Fin N) ℂ) :
    HasDerivAt (fun s : ℝ => modularFlow K s A) (modularFlux K A) 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • K) (0 : ℝ)
  have hF := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(Complex.I • K)) (0 : ℝ)
  have h := (hE.mul_const A).mul hF
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h
  have hval : (Complex.I • K) * A + A * (-(Complex.I • K))
      = modularFlux K A := by
    simp only [modularFlux, smul_mul_assoc, mul_smul_comm, mul_neg,
      sub_eq_add_neg, smul_add, smul_neg]
  rw [hval] at h
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => by
    show modularFlow K s A
      = NormedSpace.exp (s • (Complex.I • K)) * A
        * NormedSpace.exp (s • (-(Complex.I • K)))
    unfold modularFlow
    rw [modularFlow_exp_arg_pos, modularFlow_exp_arg_neg]

/- **DERIV-1, the bridge's twelfth clause** (Tier T1 — proved,
    Frobenius dialect): a Gibbs clock's own flow is differentiable at
    time `0` through every observable `A`, with derivative the modular
    flux of the clock's declared generator. -/
open scoped Matrix.Norms.Frobenius in
theorem GibbsClock.flow_hasDerivAt_zero {N : ℕ} (G : GibbsClock N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    HasDerivAt (fun s : ℝ => G.flow s A) (modularFlux G.generator A) 0 :=
  modularFlow_hasDerivAt_zero G.generator A

/- **The completed thermal-time bridge** (Tier T1 — proved): the
    eleven landed clauses of `GibbsClock.thermal_time_bridge` together
    with the twelfth, derivative, clause — all twelve clauses of the
    finite thermal-time bridge now stand. The derivative clause is
    stated in the Frobenius dialect (see the module header). -/
open scoped Matrix.Norms.Frobenius in
theorem GibbsClock.thermal_time_bridge_complete {N : ℕ}
    (G : GibbsClock N) :
    ((∀ s t : ℝ, ∀ A : Matrix (Fin N) (Fin N) ℂ,
      G.flow (s + t) A = G.flow s (G.flow t A)) ∧
    (∀ A : Matrix (Fin N) (Fin N) ℂ, G.flow 0 A = A) ∧
    (∀ (s : ℝ) (A B : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (A * B) = G.flow s A * G.flow s B) ∧
    (∀ (s : ℝ) (A B : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (A + B) = G.flow s A + G.flow s B) ∧
    (∀ (s : ℝ) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (c • A) = c • G.flow s A) ∧
    (∀ s : ℝ, G.flow s (1 : Matrix (Fin N) (Fin N) ℂ) = 1) ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      (G.flow s A)ᴴ = G.flow s Aᴴ) ∧
    (∀ s : ℝ, G.flow s G.state = G.state) ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.expectation (G.flow s A) = G.expectation A) ∧
    KMSCondition G.state G.K G.beta ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.flow s A = modularFlow G.K (G.beta * s) A) ∧
    (∀ (c : ℂ) (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      modularFlow (G.generator + c • 1) s A = G.flow s A)) ∧
    (∀ A : Matrix (Fin N) (Fin N) ℂ,
      HasDerivAt (fun s : ℝ => G.flow s A) (modularFlux G.generator A)
        0) :=
  ⟨G.thermal_time_bridge, fun A => G.flow_hasDerivAt_zero A⟩

#print axioms modularFlow_exp_arg_pos
#print axioms modularFlow_exp_arg_neg
#print axioms modularFlow_hasDerivAt_zero
#print axioms GibbsClock.flow_hasDerivAt_zero
#print axioms GibbsClock.thermal_time_bridge_complete

end ThetLogos
