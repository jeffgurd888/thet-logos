import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import ThetLogos.ModularTime

open Matrix

namespace ThetLogos

/-!
# ThetLogos.ModularFlux — thermal flux vanishing & active driver existence (Tier T1)

Two machine-checked companions to the modular-flux core (`ModularTime.lean`):

1. **Thermal vanishing.** For the Gibbs-type modular Hamiltonian K = β·D²,
   the modular flux vanishes identically: `modularFlux (β • D^2) D = 0`.
   This is the machine-checked form of audit claim A1 (Φ_β = 0).

2. **Active driver existence.** For the finite Dirac operator in off-diagonal
   block form D = fromBlocks 0 M Mᴴ 0 with M ≠ 0, there exists a self-adjoint
   "active driver" G with G * D ≠ D * G. This closes the Gate G existence
   claim as a machine-checked theorem (zero sorrys). The witness is the
   block-diagonal G = fromBlocks 1 0 0 0.

   Note on indexing: `Fin 32 ≃ Fin 16 ⊕ Fin 16` via `finSumFinEquiv`, so the
   general statement below applies to the 32-state D_F up to reindexing.
-/

/-- Thermal vanishing (Tier T1 — proved): the Gibbs-type modular Hamiltonian
    K = β·D² commutes with D, so the modular flux `φ = i[K, D]` is
    identically zero. -/
theorem thermal_flux_vanishes {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    modularFlux ((β : ℂ) • D ^ 2) D = 0 := by
  unfold modularFlux
  have hcomm : ((β : ℂ) • D ^ 2) * D = D * ((β : ℂ) • D ^ 2) := by
    have h3 : D ^ 2 * D = D * D ^ 2 := by
      rw [sq]
      exact mul_assoc _ _ _
    calc ((β : ℂ) • D ^ 2) * D = (β : ℂ) • (D ^ 2 * D) :=
          Algebra.smul_mul_assoc _ _ _
      _ = (β : ℂ) • (D * D ^ 2) := by rw [h3]
      _ = D * ((β : ℂ) • D ^ 2) := (Algebra.mul_smul_comm _ _ _).symm
  rw [hcomm, sub_self, smul_zero]

/-- The active driver: block-diagonal, identity on the first block and zero
    on the second. -/
def activeDriver (m n : ℕ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 0

/-- The active driver is self-adjoint. -/
theorem activeDriver_selfAdjoint (m n : ℕ) :
    (activeDriver m n)ᴴ = activeDriver m n := by
  unfold activeDriver
  rw [fromBlocks_conjTranspose]
  simp

/-- Active driver existence (Tier T1 — proved): for the off-diagonal block
    Dirac operator D = fromBlocks 0 M Mᴴ 0 with M ≠ 0, the self-adjoint
    driver G = fromBlocks 1 0 0 0 does not commute with D. -/
theorem exists_activeDriver {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (hM : M ≠ 0) :
    ∃ G : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ,
      Gᴴ = G ∧
        G * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 ≠
          fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * G := by
  refine ⟨activeDriver m n, activeDriver_selfAdjoint m n, ?_⟩
  intro hcon
  have h1 : activeDriver m n * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0
      = fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M 0 0 := by
    unfold activeDriver
    rw [fromBlocks_multiply]
    simp
  have h2 : fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * activeDriver m n
      = fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) 0 Mᴴ 0 := by
    unfold activeDriver
    rw [fromBlocks_multiply]
    simp
  rw [h1, h2] at hcon
  -- M has a nonzero entry; evaluate both sides there.
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hM (Matrix.ext fun a b => hc a b)
  have hentry := congrFun (congrFun hcon (Sum.inl i)) (Sum.inr j)
  simp only [fromBlocks_apply₁₂] at hentry
  exact hij hentry

end ThetLogos
