import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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

3. **Gauge covariance.** For a unitary `U` commuting with the driver `G`
   (the commutant constraint), conjugating the flux equals the flux of the
   conjugated Dirac operator: `modularFlux_gaugeCovariant`. Corollary: the
   flux trace is gauge-invariant (`modularFlux_trace_gaugeInvariant`).

4. **Inter-sectoral driver.** The explicit off-diagonal driver
   `interSectoralDriver` (with nonzero (1,2)-block across the chiral
   bipartition) yields nonzero active flux: `interSectoral_flux_nonzero`.
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

-- ============================================================================
-- Gauge covariance of the modular flux (gauntlet target 1, Tier T1)
-- ============================================================================

/-- Gauge covariance of the modular flux φ = i[G, D] under a gauge unitary U
that commutes with the driver G (the commutant constraint).
Conjugating the flux equals the flux of the conjugated Dirac operator:
U φ(G, D) Uᴴ = φ(G, U D Uᴴ).

Note on scope: the gauge group U(A_F) is not formalized (the codebase
represents A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ) via the 12 explicit generators `smGen` in
`MartinettiRep.lean`); the commutant constraint is what supplies `hcomm`
for gauge unitaries. Formalizing the group itself is future work. -/
theorem modularFlux_gaugeCovariant {N : ℕ} (G D U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (hcomm : U * G = G * U) :
    U * modularFlux G D * Uᴴ = modularFlux G (U * D * Uᴴ) := by
  -- The conjugate transpose of a gauge unitary inherits the commutation:
  -- Uᴴ * G = G * Uᴴ, via inserting 1 = U * Uᴴ on the right.
  have hcomm' : Uᴴ * G = G * Uᴴ := by
    have e1 : Uᴴ * G = Uᴴ * G * (U * Uᴴ) := by rw [hU, mul_one]
    rw [e1]
    calc Uᴴ * G * (U * Uᴴ)
        = Uᴴ * (G * U) * Uᴴ := by simp only [← mul_assoc]
      _ = Uᴴ * (U * G) * Uᴴ := by rw [← hcomm]
      _ = (Uᴴ * U) * G * Uᴴ := by simp only [mul_assoc]
      _ = G * Uᴴ := by rw [hU', one_mul]
  -- First summand: U * (G * D) * Uᴴ = G * (U * D * Uᴴ), using U * G = G * U.
  have e1 : U * (G * D) * Uᴴ = G * (U * D * Uᴴ) := by
    simp only [← mul_assoc]
    rw [hcomm]
  -- Second summand: U * (D * G) * Uᴴ = (U * D * Uᴴ) * G, using Uᴴ * G = G * Uᴴ.
  have e2 : U * (D * G) * Uᴴ = (U * D * Uᴴ) * G := by
    calc U * (D * G) * Uᴴ
        = U * (D * (G * Uᴴ)) := by simp only [mul_assoc]
      _ = U * (D * (Uᴴ * G)) := by rw [← hcomm']
      _ = (U * D * Uᴴ) * G := by simp only [← mul_assoc]
  -- Assemble: conjugation distributes over the commutator difference.
  have e : U * (G * D - D * G) * Uᴴ
      = G * (U * D * Uᴴ) - (U * D * Uᴴ) * G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  unfold modularFlux
  rw [Matrix.mul_smul, Matrix.smul_mul, e]

/-- Gauge-invariance of the flux trace: conjugating D by a gauge unitary that
commutes with G leaves the trace of the modular flux unchanged.
Corollary of `modularFlux_gaugeCovariant` plus cyclicity of the trace. -/
theorem modularFlux_trace_gaugeInvariant {N : ℕ} (G D U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (hcomm : U * G = G * U) :
    Matrix.trace (modularFlux G (U * D * Uᴴ)) = Matrix.trace (modularFlux G D) := by
  rw [← modularFlux_gaugeCovariant G D U hU hU' hcomm]
  rw [Matrix.trace_mul_comm (U * modularFlux G D) Uᴴ]
  rw [← mul_assoc, hU', one_mul]

-- ============================================================================
-- Inter-sectoral driver (gauntlet target 2, Tier T1)
-- ============================================================================

/-- Inter-sectoral driver: pure off-diagonal block shift across the chiral
bipartition. Its (1,2)-block is the identity.

Note on the signature: the two-parameter form `fromBlocks 0 1 0 0` over
`Matrix (Fin m) (Fin n)` does not elaborate, since rectangular matrices have
no `1`. Only the square case is used. -/
def interSectoralDriver (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  fromBlocks 0 1 0 0

/-- The (1,2)-block of the inter-sectoral driver is nonzero: it carries
identity mass across the bipartition. -/
theorem interSectoralDriver_offdiag {m : ℕ} [NeZero m] :
    ∃ i : Fin m, ∃ j : Fin m,
      interSectoralDriver m (Sum.inl i) (Sum.inr j) ≠ 0 := by
  obtain ⟨i⟩ : Nonempty (Fin m) := inferInstance
  refine ⟨i, i, ?_⟩
  unfold interSectoralDriver
  rw [fromBlocks_apply₁₂]
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) i i = 1 := Matrix.one_apply_eq i
  rw [h1]
  exact one_ne_zero

/-- Nonzero active flux from the inter-sectoral driver (Tier T1 — proved):
for D = fromBlocks 0 M Mᴴ 0 with M ≠ 0, the active flux
φ_act = Complex.I • (G * D - D * G) is nonzero.
(φ_act here is the explicit form; it equals `modularFlux` up to the
finSumFinEquiv reindexing.) -/
theorem interSectoral_flux_nonzero {m : ℕ} [NeZero m]
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M ≠ 0) :
    Complex.I • (interSectoralDriver m * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0
      - fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * interSectoralDriver m) ≠ 0 := by
  have hGD : interSectoralDriver m * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0
      = fromBlocks Mᴴ 0 0 (0 : Matrix (Fin m) (Fin m) ℂ) := by
    unfold interSectoralDriver
    rw [fromBlocks_multiply]
    simp
  have hDG : fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * interSectoralDriver m
      = fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) 0 0 Mᴴ := by
    unfold interSectoralDriver
    rw [fromBlocks_multiply]
    simp
  have hsub : interSectoralDriver m * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0
      - fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * interSectoralDriver m
      = fromBlocks Mᴴ 0 0 (-Mᴴ) := by
    rw [hGD, hDG, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp
  -- The commutator itself is nonzero: evaluate at a nonzero entry of M.
  have hcomm_ne : interSectoralDriver m * fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0
      - fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) M Mᴴ 0 * interSectoralDriver m ≠ 0 := by
    intro h0
    rw [hsub] at h0
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hM (Matrix.ext fun a b => hc a b)
    have hentry := congrFun (congrFun h0 (Sum.inl j)) (Sum.inl i)
    simp only [fromBlocks_apply₁₁, Matrix.conjTranspose_apply, Matrix.zero_apply] at hentry
    exact (star_ne_zero.mpr hij) hentry
  exact smul_ne_zero Complex.I_ne_zero hcomm_ne

end ThetLogos
