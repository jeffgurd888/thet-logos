import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.Rung5W6 — axiom W6 (nontriviality) for the Majorana field

**Both results here are T1 (machine-proved).**

**PART A — the bosonic-form target HOLDS for the free Majorana fermion.**
The Wightman functions of the one-mode Majorana field are
`wMajorana n fs = ⟪vac1, (∏ f ∈ fs, ψ(f)) vac1⟫`. Since
`ψ(f) ∘ ψ(g) = (fg) • 1` (`fieldMajorana_comp`), the 2-point function is
`W₂(f,g) = f·g` and the 4-point is `W₄(f₁,f₂,f₃,f₄) = f₁f₂f₃f₄`. The bosonic
Wick subtraction then gives `f₁f₂f₃f₄ − 3·f₁f₂f₃f₄ = −2·f₁f₂f₃f₄ ≠ 0`, so the
target `W6_nontrivial_sharp` is discharged — **but this is a false positive
for "interacting": the field is free.** The bosonic criterion is
fermion-blind.

**PART B — the fermionic-sign corrected criterion VANISHES (T1).**
With Koszul signs `(+, −, +)` the connected 4-point function is identically
zero by Wick's theorem, correctly detecting freeness. This proves the
Rung-4 caveat ("the fermionic version inserts Koszul signs") is
load-bearing, not cosmetic.
-/

/-- The Wightman functions of the one-mode Majorana field. -/
noncomputable def wMajorana : ℕ → List ℂ → ℂ :=
  fun _ fs => vacExp1 ((fs.map fieldMajorana).prod)

/-- `(1 : Module.End ℂ Fock1)` fixes the vacuum (T1 helper). -/
theorem end_one_apply_vac1 : ((1 : Module.End ℂ Fock1) vac1) = vac1 := rfl

/-- `(1 : Module.End ℂ Fock1).comp 1 = 1` (T1 helper). -/
theorem end_one_comp_one :
    ((1 : Module.End ℂ Fock1).comp (1 : Module.End ℂ Fock1)) = 1 := by
  ext x
  rfl

/-- Scalar operators read off the vacuum (T1 helper). -/
theorem vacExp1_smul_one (z : ℂ) : vacExp1 (z • (1 : Module.End ℂ Fock1)) = z := by
  unfold vacExp1
  rw [LinearMap.smul_apply, end_one_apply_vac1, inner_smul_right]
  have h : ⟪vac1, vac1⟫_ℂ = 1 := by
    have h1 := vacExp1_one
    unfold vacExp1 at h1
    rwa [end_one_apply_vac1] at h1
  rw [h, mul_one]

/-- The 2-point function: `W₂(f,g) = f·g` (T1). -/
theorem wMajorana_two (f g : ℂ) : wMajorana 2 [f, g] = f * g := by
  have hprod : ((fieldMajorana f :: fieldMajorana g ::
      ([] : List (Module.End ℂ Fock1))).prod
      = fieldMajorana f * fieldMajorana g) := by
    simp [List.prod_cons]
  unfold wMajorana
  simp only [List.map_cons, List.map_nil]
  rw [hprod, Module.End.mul_eq_comp, fieldMajorana_comp, vacExp1_smul_one]

/-- The 4-point function: `W₄(f₁,f₂,f₃,f₄) = f₁f₂f₃f₄` (T1). -/
theorem wMajorana_four (f₁ f₂ f₃ f₄ : ℂ) :
    wMajorana 4 [f₁, f₂, f₃, f₄] = f₁ * f₂ * f₃ * f₄ := by
  have hprod : ((fieldMajorana f₁ :: fieldMajorana f₂ :: fieldMajorana f₃ ::
        fieldMajorana f₄ :: ([] : List (Module.End ℂ Fock1))).prod
        = ((f₁ * f₂) * (f₃ * f₄)) • (1 : Module.End ℂ Fock1)) := by
    have hstep : (fieldMajorana f₁ :: fieldMajorana f₂ :: fieldMajorana f₃ ::
          fieldMajorana f₄ :: ([] : List (Module.End ℂ Fock1))).prod
          = ((fieldMajorana f₁ * fieldMajorana f₂)
            * (fieldMajorana f₃ * fieldMajorana f₄)) := by
      simp [List.prod_cons, mul_assoc]
    rw [hstep]
    simp only [Module.End.mul_eq_comp, fieldMajorana_comp, smul_comp_smul,
      end_one_comp_one]
  unfold wMajorana
  simp only [List.map_cons, List.map_nil]
  rw [hprod, vacExp1_smul_one]
  ring

/-- **PART A (T1):** the bosonic-form W6 target holds for the free Majorana
    fermion — `connectedFourPoint = 1 − 3 = −2 ≠ 0` at `fs = ![1,1,1,1]`.
    Honest label: this is a FALSE POSITIVE for "interacting" — the field is
    free. The bosonic criterion is fermion-blind. -/
theorem w6_majorana : W6_nontrivial_sharp (⟨ℂ⟩ : TestFunctionMarker) wMajorana := by
  refine ⟨![1, 1, 1, 1], ?_⟩
  have h : connectedFourPoint (⟨ℂ⟩ : TestFunctionMarker) wMajorana ![1, 1, 1, 1]
      = wMajorana 4 [1, 1, 1, 1]
        - (wMajorana 2 [1, 1] * wMajorana 2 [1, 1]
          + wMajorana 2 [1, 1] * wMajorana 2 [1, 1]
          + wMajorana 2 [1, 1] * wMajorana 2 [1, 1]) := rfl
  rw [h]
  simp only [wMajorana_two, wMajorana_four]
  norm_num

/-- **PART B (T1):** fermionic Wick's theorem with Koszul signs — the
    correctly-signed connected 4-point function vanishes identically,
    correctly detecting that the Majorana field is free. -/
theorem w6_fermionic_wick (a b c d : ℂ) :
    wMajorana 4 [a, b, c, d]
      = wMajorana 2 [a, b] * wMajorana 2 [c, d]
        - wMajorana 2 [a, c] * wMajorana 2 [b, d]
        + wMajorana 2 [a, d] * wMajorana 2 [b, c] := by
  simp only [wMajorana_four, wMajorana_two]
  ring

#print axioms vacExp1_smul_one
#print axioms wMajorana_two
#print axioms wMajorana_four
#print axioms w6_majorana
#print axioms w6_fermionic_wick

end ThetLogos
