import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open Matrix

namespace ThetLogos

/-!
# ThetLogos.ActiveFlux — trace identities for the active flux (Tier T1)

For block matrices `G`, `D` over `Fin m ⊕ Fin n`, the active flux
`φ_act = i • (G * D - D * G)` (lowercase φ, per doctrine) satisfies

  Tr(φ_act²) = -(Tr(C₁₁·C₁₁) + Tr(C₂₂·C₂₂) + 2·Tr(C₁₂·C₂₁)),

where `Cᵢⱼ` are the blocks of the commutator `[G, D]`. Pure linear algebra:
no physics input, no approximations. Zero `sorry`s.
-/

/-- Trace of a block matrix is the sum of the diagonal-block traces. -/
theorem trace_fromBlocks {m n : ℕ} (R : Type*) [CommRing R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₂₂]

/-- The commutator of two block matrices, in block components. -/
theorem commutator_fromBlocks {m n : ℕ}
    (G₁₁ : Matrix (Fin m) (Fin m) ℂ) (G₁₂ : Matrix (Fin m) (Fin n) ℂ)
    (G₂₁ : Matrix (Fin n) (Fin m) ℂ) (G₂₂ : Matrix (Fin n) (Fin n) ℂ)
    (D₁₁ : Matrix (Fin m) (Fin m) ℂ) (D₁₂ : Matrix (Fin m) (Fin n) ℂ)
    (D₂₁ : Matrix (Fin n) (Fin m) ℂ) (D₂₂ : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ * fromBlocks D₁₁ D₁₂ D₂₁ D₂₂
      - fromBlocks D₁₁ D₁₂ D₂₁ D₂₂ * fromBlocks G₁₁ G₁₂ G₂₁ G₂₂
      = fromBlocks (G₁₁ * D₁₁ + G₁₂ * D₂₁ - D₁₁ * G₁₁ - D₁₂ * G₂₁)
          (G₁₁ * D₁₂ + G₁₂ * D₂₂ - D₁₁ * G₁₂ - D₁₂ * G₂₂)
          (G₂₁ * D₁₁ + G₂₂ * D₂₁ - D₂₁ * G₁₁ - D₂₂ * G₂₁)
          (G₂₁ * D₁₂ + G₂₂ * D₂₂ - D₂₁ * G₁₂ - D₂₂ * G₂₂) := by
  rw [fromBlocks_multiply, fromBlocks_multiply, sub_eq_add_neg,
    fromBlocks_neg, fromBlocks_add, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

/-- Trace of the square of a block matrix, in block components.
    Uses Tr(AB) = Tr(BA) to identify the two off-diagonal contributions. -/
theorem trace_blockSq {m n : ℕ}
    (C₁₁ : Matrix (Fin m) (Fin m) ℂ) (C₁₂ : Matrix (Fin m) (Fin n) ℂ)
    (C₂₁ : Matrix (Fin n) (Fin m) ℂ) (C₂₂ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((fromBlocks C₁₁ C₁₂ C₂₁ C₂₂) ^ 2)
      = Matrix.trace (C₁₁ * C₁₁) + Matrix.trace (C₂₂ * C₂₂)
        + 2 * Matrix.trace (C₁₂ * C₂₁) := by
  have hsq : (fromBlocks C₁₁ C₁₂ C₂₁ C₂₂) ^ 2
      = fromBlocks (C₁₁ * C₁₁ + C₁₂ * C₂₁) (C₁₁ * C₁₂ + C₁₂ * C₂₂)
          (C₂₁ * C₁₁ + C₂₂ * C₂₁) (C₂₁ * C₁₂ + C₂₂ * C₂₂) := by
    rw [sq, fromBlocks_multiply]
  rw [hsq, trace_fromBlocks]
  simp only [Matrix.trace_add]
  rw [Matrix.trace_mul_comm C₂₁ C₁₂]
  ring

/-- Scalar factor through a matrix square: Tr((r • X)²) = r² · Tr(X²). -/
theorem trace_smul_sq {n : Type*} [Fintype n] [DecidableEq n] (r : ℂ)
    (X : Matrix n n ℂ) :
    Matrix.trace ((r • X) ^ 2) = r ^ 2 * Matrix.trace (X ^ 2) := by
  have h : (r • X) * (r • X) = (r * r) • (X * X) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_smul]
  simp only [sq, h, Matrix.trace_smul, smul_eq_mul]

/-- The active-flux trace identity (Tier T1 — proved): for block matrices
    `G`, `D` over `Fin m ⊕ Fin n`, with `φ_act = i • (G * D - D * G)`,

    Tr(φ_act²) = -(Tr(C₁₁²) + Tr(C₂₂²) + 2·Tr(C₁₂·C₂₁)),

    where the `Cᵢⱼ` are the commutator blocks `[G, D]ᵢⱼ`. The overall sign
    comes from `i² = -1`; the `2·Tr(C₁₂·C₂₁)` cross term from cyclicity of
    the trace. -/
theorem trace_fluxSq_block {m n : ℕ}
    (G₁₁ : Matrix (Fin m) (Fin m) ℂ) (G₁₂ : Matrix (Fin m) (Fin n) ℂ)
    (G₂₁ : Matrix (Fin n) (Fin m) ℂ) (G₂₂ : Matrix (Fin n) (Fin n) ℂ)
    (D₁₁ : Matrix (Fin m) (Fin m) ℂ) (D₁₂ : Matrix (Fin m) (Fin n) ℂ)
    (D₂₁ : Matrix (Fin n) (Fin m) ℂ) (D₂₂ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((Complex.I • (fromBlocks G₁₁ G₁₂ G₂₁ G₂₂
        * fromBlocks D₁₁ D₁₂ D₂₁ D₂₂
        - fromBlocks D₁₁ D₁₂ D₂₁ D₂₂ * fromBlocks G₁₁ G₁₂ G₂₁ G₂₂)) ^ 2)
      = -(Matrix.trace ((G₁₁ * D₁₁ + G₁₂ * D₂₁ - D₁₁ * G₁₁ - D₁₂ * G₂₁)
            * (G₁₁ * D₁₁ + G₁₂ * D₂₁ - D₁₁ * G₁₁ - D₁₂ * G₂₁))
          + Matrix.trace ((G₂₁ * D₁₂ + G₂₂ * D₂₂ - D₂₁ * G₁₂ - D₂₂ * G₂₂)
            * (G₂₁ * D₁₂ + G₂₂ * D₂₂ - D₂₁ * G₁₂ - D₂₂ * G₂₂))
          + 2 * Matrix.trace ((G₁₁ * D₁₂ + G₁₂ * D₂₂ - D₁₁ * G₁₂ - D₁₂ * G₂₂)
            * (G₂₁ * D₁₁ + G₂₂ * D₂₁ - D₂₁ * G₁₁ - D₂₂ * G₂₁))) := by
  rw [commutator_fromBlocks, trace_smul_sq, trace_blockSq, Complex.I_sq]
  ring

#print axioms trace_fluxSq_block
#print axioms trace_blockSq
#print axioms commutator_fromBlocks
#print axioms trace_fromBlocks

end ThetLogos
