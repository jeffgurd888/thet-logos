import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets

namespace ThetLogos

/-!
# ThetLogos.Rung5W4 — W4 (locality) for the one-mode Majorana field (Rung 5)

**Honest label.** This proves the W4 sharp target `W4_locality_sharp` with
`s = +1` for the one-mode Majorana field `ψ(c) = c • (a† + a)` lifted to the
top submodule `D = ⊤`:
- `s² = 1` holds since `(1 : ℂ)² = 1`.
- The field *commutes*: `ψ(f) ∘ ψ(g) = fg • 1` (T1, `fieldMajorana_comp`),
  so the locality equation holds with the bosonic sign `s = +1`.
- `spacelikeSep` is taken to be trivially `True`: the one-mode model has no
  spacetime, so there is nothing for separation to mean.

**Priced, NOT claimed.** Genuine spacelike fermionic anticommutativity
(`{φ(f), φ(g)} = 0` for spacelike-separated supports) needs Schwartz support
theory — defining supports of test functions and the spacelike condition via
the Minkowski form — which Mathlib (2026) lacks. That is the T5 window; this
file discharges only the algebraic shadow for the zero-mode model.
-/

/-- The lifted Majorana product on `D = ⊤` reduces to a scalar (T1 helper). -/
theorem liftTop_fieldMajorana_comp (f g : ℂ) :
    (liftTop (fieldMajorana f)).comp (liftTop (fieldMajorana g))
      = (f * g) • (1 : (⊤ : Submodule ℂ Fock1) →ₗ[ℂ] (⊤ : Submodule ℂ Fock1)) := by
  rw [← liftTop_comp, fieldMajorana_comp, liftTop_smul, liftTop_one]

/-- **W4 locality (T1)** for the one-mode Majorana field with `s = +1`:
    the field commutes, `ψ(f)ψ(g) = 1 • ψ(g)ψ(f)`, and `1² = 1`.
    `spacelikeSep` is trivially `True` — the one-mode model has no spacetime. -/
theorem w4_majorana :
    W4_locality_sharp Fock1 (⟨ℂ⟩ : TestFunctionMarker) (⊤ : Submodule ℂ Fock1)
      (fun c => liftTop (fieldMajorana c)) (fun _ _ => True) 1 := by
  constructor
  · norm_num
  · intro f g _
    show (liftTop (fieldMajorana f)).comp (liftTop (fieldMajorana g))
        = (1 : ℂ) • ((liftTop (fieldMajorana g)).comp (liftTop (fieldMajorana f)))
    rw [liftTop_fieldMajorana_comp, liftTop_fieldMajorana_comp, one_smul, mul_comm g f]

#print axioms w4_majorana

end ThetLogos
