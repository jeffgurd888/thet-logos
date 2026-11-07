import Mathlib.Tactic
import Mathlib.Analysis.Matrix.PosDef
import ThetLogos.FiniteArrowPin
import ThetLogos.BridgeMagneticHeat

open scoped InnerProductSpace

/-!
# ThetLogos.FiniteArrowMagnetic — FA-7 (OPTIONAL): decay survives gauging

The optional brick of the finite arrow line (scoping
`finite-arrow-scoping-2026-11-06.md` §3.8(d3); pin FA-0,
`FiniteArrowPin.lean`). Working label only — naming is Jeff's.

**What is proved.** The gauged (magnetic) heat flow's quadratic
form `⟪x, e^{−t·magMat} x⟫` is antitone in `t` on `t ≥ 0`: the
spectral damping that carries the arrow's energy form exists
verbatim for `magHeat`, because the magnetic generator is still
Hermitian and positive-semidefinite. The proof is a
citation-assembly (labeled as such): the landed
`heatKernelGen_quadraticForm_eq` writes the form as
`∑ i, exp (−t λᵢ) ‖yᵢ‖²` in the eigenbasis, the landed
`magMat_eigenvalues_nonneg` gives `λᵢ ≥ 0`, and each term is
antitone in `t`.

**Fence (on the face).** A magnetic field is the classic
time-reversal breaker in physics, and this seat does NOT
capture that: `magHeat` is a self-adjoint semigroup whose
Loschmidt pair (FA-5's shape) has the ungauged form — the gauge
phases damp nothing and reverse nothing in any statement this
corpus can currently make. NO time-reversal-breaking claim is
made or implied. NO CLAIM; dials 0/4; Dial 2 = 0.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **FA-7.** Energy decay survives gauging: the magnetic heat
kernel's quadratic form is antitone in `t` on `t ≥ 0`. -/
theorem magHeat_quadraticForm_antitoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    (x : V → ℂ) :
    AntitoneOn (fun t => (dotProduct (star x)
      (Matrix.mulVec (magHeat w θ t) x)).re) (Set.Ici 0) := by
  have hform : ∀ t : ℝ, (dotProduct (star x)
        (Matrix.mulVec (magHeat w θ t) x)).re
      = ∑ i, Real.exp (-t * (magMat_isHermitian w hw θ hθ).eigenvalues i)
        * ‖(Matrix.mulVec (star ((magMat_isHermitian w hw θ hθ).eigenvectorUnitary
            : Matrix V V ℂ)) x) i‖ ^ 2 := by
    intro t
    rw [show magHeat w θ t = heatKernelGen (magMat w θ) t from rfl,
      heatKernelGen_quadraticForm_eq (magMat w θ)
        (magMat_isHermitian w hw θ hθ) t x]
    simp only [Complex.ofReal_re]
  intro a _ b _ hab
  show (dotProduct (star x) (Matrix.mulVec (magHeat w θ b) x)).re
    ≤ (dotProduct (star x) (Matrix.mulVec (magHeat w θ a) x)).re
  rw [hform b, hform a]
  apply Finset.sum_le_sum
  intro i _
  have hl : 0 ≤ (magMat_isHermitian w hw θ hθ).eigenvalues i :=
    magMat_eigenvalues_nonneg w hw hw0 θ hθ i
  have hexp : Real.exp (-b * (magMat_isHermitian w hw θ hθ).eigenvalues i)
      ≤ Real.exp (-a * (magMat_isHermitian w hw θ hθ).eigenvalues i) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hab hl
    linarith
  exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)

/-- The FA-7 pin, discharged. -/
theorem fa7_pin : @FA7Pin V _ _ :=
  fun w hw hw0 θ hθ x => magHeat_quadraticForm_antitoneOn w hw hw0 θ hθ x

end ThetLogos
