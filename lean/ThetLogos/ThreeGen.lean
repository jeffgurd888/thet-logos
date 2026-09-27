import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.Scaffold32
import ThetLogos.FiniteSpectralTriple
import ThetLogos.MartinettiRep

/-!
# ThetLogos.ThreeGen — three-generation triplication (T2/T3/T4)

Imposed triplication of the one-generation finite geometry from `ThetLogos.MartinettiRep`
to ℂ⁹⁶ = ℂ³² ⊗ ℂ³.

**Honesty boundary (read first).**
* Triplication is IMPOSED, not derived: nothing selects three generations from thet
  primitives. The representation π₃(a) = π(a) ⊗ I₃ and the Dirac ansatz below are
  conventional choices.
* Flavour structure (CKM/PMNS, mass hierarchies) is INPUT via the Yukawa matrices,
  not output. Order-one does not select them.
* Tier T2 (definitions, this file): `gamma3`, `UJ3`, `smGen3`, `smGenOp3`,
  `smDirac3diag` (flavour-diagonal triplication D₃ = D₁ ⊗ I₃).
* Tier T3 (proven, this file): blockwise action of Γ₃ (`gamma3_mul_apply`,
  `mul_gamma3_apply`).
* Tier T3 (mathematics, not yet formalized): for flavour-diagonal Yukawas,
  D₃ = D₁ ⊗ I₃ inherits grading-oddness, self-adjointness, J-compatibility,
  order-zero, and order-one from the one-generation theorems by Kronecker
  reduction. The formalization is deferred due to tactic-engineering time,
  not a mathematical gap.
* Tier T4 (numerical only, NOT proven here): all axioms including order-one
  for arbitrary 3×3 Yukawa matrices. Verified 2026-09-27 in
  `attack4_corrected/attack4_3gen.py`: 3 random trials, exact zeros for
  grading-oddness, self-adjointness, J-compatibility (symmetric MR), and
  order-one (144+144 pairs); total order-one nullity 402 = 3×46 + 3×88.

Index convention: `I96 := I32 × Fin 3`; the pair `(i, g)` is the 32-index `i`
in generation `g`. This matches the Python 96-index `n = i.val * 3 + g.val`.
-/

open Matrix

namespace ThetLogos

/-- 96-dim index: 32-dim flavour-colour index × 3 generations. -/
abbrev I96 := I32 × Fin 3

/-- Triplicated grading: Γ₃ = Γ ⊗ I₃ (block-diagonal in generation). -/
def gamma3 : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => gammaF i j * if g = gp then (1 : ℂ) else 0

/-- Triplicated real structure: UJ₃ = UJ ⊗ I₃. -/
def UJ3 : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => UJ i j * if g = gp then (1 : ℂ) else 0

/-- Triplicated SM generators: π₃(a) = π(a) ⊗ I₃. -/
noncomputable def smGen3 (g : Fin 12) : Matrix I96 I96 ℂ :=
  fun (i, a) (j, b) => smGen g i j * if a = b then (1 : ℂ) else 0

/-- Triplicated opposite generators: π₃°(b) = π°(b) ⊗ I₃. -/
noncomputable def smGenOp3 (g : Fin 12) : Matrix I96 I96 ℂ :=
  fun (i, a) (j, b) => smGenOp g i j * if a = b then (1 : ℂ) else 0

/-- Flavour-diagonal three-generation Dirac: D₃ = D₁ ⊗ I₃.
    Takes the one-generation Dirac operator D₁ and triplicates it diagonally
    in generation space. The T3-proven case; arbitrary 3×3 Yukawa matrices
    are T4 (numerical) only. -/
def smDirac3diag (D1 : Matrix I32 I32 ℂ) : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => D1 i j * if g = gp then (1 : ℂ) else 0

/-! ## Blockwise action of the triplicated grading (T3) -/

/-- Γ₃ applied to indices. -/
theorem gamma3_apply (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    gamma3 (i, g) (j, gp) = gammaF i j * if g = gp then (1 : ℂ) else 0 := rfl

/-- Γ₃ is the 1-gen grading on the diagonal. -/
theorem gamma3_diag (i : I32) (g : Fin 3) : gamma3 (i, g) (i, g) = gammaF i i := by
  rw [gamma3_apply, if_pos rfl, mul_one]

/-- Γ₃ acts by left multiplication as the 1-gen grading on each block (T3). -/
theorem gamma3_mul_apply (M : Matrix I96 I96 ℂ) (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    (gamma3 * M) (i, g) (j, gp) = gammaF i i * M (i, g) (j, gp) := by
  have hsum : ∑ k : I96, gamma3 (i, g) k * M k (j, gp)
      = gamma3 (i, g) (i, g) * M (i, g) (j, gp) := by
    apply Finset.sum_eq_single (i, g)
    · intro b _ hb
      obtain ⟨k, c⟩ := b
      simp only [gamma3_apply]
      by_cases hcc : g = c
      · have hik : i ≠ k := by
          intro heq; apply hb; simp [heq, hcc]
        simp [ite_eq_left hcc, gammaF_apply_ne hik]
      · simp [ite_eq_right hcc]
    · intro hcon
      exact absurd (Finset.mem_univ (i, g)) hcon
  rw [Matrix.mul_apply, hsum, gamma3_diag]

/-- Γ₃ acts by right multiplication as the 1-gen grading on each block (T3). -/
theorem mul_gamma3_apply (M : Matrix I96 I96 ℂ) (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    (M * gamma3) (i, g) (j, gp) = M (i, g) (j, gp) * gammaF j j := by
  have hsum : ∑ k : I96, M (i, g) k * gamma3 k (j, gp)
      = M (i, g) (j, gp) * gamma3 (j, gp) (j, gp) := by
    apply Finset.sum_eq_single (j, gp)
    · intro b _ hb
      obtain ⟨k, c⟩ := b
      simp only [gamma3_apply]
      by_cases hcc : c = gp
      · have hkj : k ≠ j := by
          intro heq; apply hb; simp [heq, hcc]
        simp [ite_eq_left hcc, gammaF_apply_ne hkj]
      · simp [ite_eq_right hcc]
    · intro hcon
      exact absurd (Finset.mem_univ (j, gp)) hcon
  rw [Matrix.mul_apply, hsum, gamma3_diag]

end ThetLogos
