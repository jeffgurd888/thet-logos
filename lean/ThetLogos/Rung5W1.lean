import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets

namespace ThetLogos

/-!
# ThetLogos.Rung5W1 — W1 (fields exist) for the one-mode Majorana field (Rung 5)

**Honest label.** This proves the W1 sharp target `W1_fieldsExist_sharp` for
the one-mode Majorana field `ψ(c) = c • (a† + a)` lifted to the top submodule
`D = ⊤`, with test-function space `ℂ` and test-function conjugation `star`:
- `vac1 ∈ ⊤` and `vac1 ≠ 0` (T1, `Submodule.mem_top`, `vac1_ne_zero`).
- Linearity in the test function from `fieldMajorana_add` /
  `fieldMajorana_smul`, transported through `liftTop`.
- Hermiticity `⟪ψ(f)ψ', χ⟫ = ⟪ψ', ψ(f̄)χ⟫` reduces to the T1
  `fieldMajorana_hermitian`, since `liftTop` and the `⊤`-coercion are
  definitional identities on the underlying vectors.
- `star` is involutive on `ℂ` (`star_star`).

**Priced, NOT claimed.** The test-function space here is `ℂ`, not Schwartz
space `𝒮(ℝ⁴)` — there is no spacetime, no smearing, no distribution theory.
This discharges the algebraic shadow of W1 for the zero-mode model; the
analytic content (tempered distributions, the common dense invariant domain
of a real theory) is the T5 window framed in `WightmanTargets.lean`.
-/

/-- `liftTop` preserves addition (T1 helper). -/
theorem liftTop_add {H : Type*} [AddCommGroup H] [Module ℂ H] (A B : H →ₗ[ℂ] H) :
    liftTop (A + B) = liftTop A + liftTop B := by
  ext x
  rfl

/-- **W1 fields-exist (T1)** for the one-mode Majorana field: `ψ(c)`,
    complex-linear in the test function and Hermitian w.r.t. test-function
    conjugation `star`, with `vac1 ∈ ⊤` nonzero. -/
theorem w1_majorana :
    W1_fieldsExist_sharp Fock1 vac1 (⟨ℂ⟩ : TestFunctionMarker)
      (⊤ : Submodule ℂ Fock1) star (fun c => liftTop (fieldMajorana c)) := by
  refine ⟨Submodule.mem_top, ?_, ?_, ?_, ?_, vac1_ne_zero⟩
  · -- additivity in the test function
    intro f g
    show liftTop (fieldMajorana (f + g))
      = liftTop (fieldMajorana f) + liftTop (fieldMajorana g)
    rw [← liftTop_add, fieldMajorana_add]
  · -- homogeneity in the test function
    intro c f
    show liftTop (fieldMajorana (c • f)) = c • liftTop (fieldMajorana f)
    rw [smul_eq_mul, fieldMajorana_smul, liftTop_smul]
  · -- Hermiticity w.r.t. test-function conjugation
    intro f ψ χ
    exact fieldMajorana_hermitian f (ψ : Fock1) (χ : Fock1)
  · -- test-function conjugation is involutive
    intro f
    exact star_star f

#print axioms w1_majorana

end ThetLogos
