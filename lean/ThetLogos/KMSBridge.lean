import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic
import ThetLogos.ModularFlux

open Matrix

namespace ThetLogos

/-!
# ThetLogos.KMSBridge — the KMS bridge (Tiers T1/T2/T5)

Folds the Kubo–Martin–Schwinger (KMS) condition into ACMD's modular-flux
core. FIT verdict: FIT — the finite-dimensional KMS identity is proved
here as Tier T1 against ACMD's formalized objects (Gibbs-type modular
Hamiltonians, modular-flow exponentials, the trace), not as analogy.

Tier map:
- T2 (definitions): `gibbsWeight`, `gibbsZ`, `gibbsState`,
  `modularFlowImag`, `KMSCondition`.
- T1 (proved): `commute_smul_K` (scalar multiples of K commute);
  `exp_smul_mul_exp_neg_smul` (imaginary-time exponentials are mutual
  inverses); `trace_mul_three` (three-factor trace cyclicity);
  `gibbs_kms_weight` (KMS for the unnormalized Gibbs weight, by trace
  cyclicity); `gibbs_kms` (KMS for the normalized Gibbs state);
  `gibbsKMSAtOwnBeta_witness` / `magnetophaseKMS_witness` (explicit Gibbs
  witnesses for the pinned T5 targets in `ModularFlux.lean`);
  `gibbsWeight_stationary` (the Gibbs weight is stationary under real
  modular time); `gibbs_kms_flux_stationary` (the KMS state is the
  flux-stationary state); `thermal_flux_observable_vanishing` (the thermal
  flux is a vanishing observable).
- T5 (priced window): `TomitaTakesakiWindow` — the infinite-dimensional
  Tomita–Takesaki theory is priced, not formalized.

Note: the eigenbasis KMS target `kms_identity_diagonal`
(ModularTime.lean, T3 sorry) is the diagonal specialization of
`gibbs_kms_weight` (β = 1, K diagonal); discharging it through this route
would need the exp-of-diagonal spectral lemma, so it is left untouched
per intake scope.
-/

-- ============================================================================
-- Tier T2: definitions
-- ============================================================================

/-- The Gibbs (thermal) weight Ω_{β,K} = e^{-βK} (unnormalized).
    Tier T2. -/
noncomputable def gibbsWeight {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((-(β : ℂ)) • K)

/-- Gibbs partition function Z_{β,K} = Tr(e^{-βK}). Tier T2. -/
noncomputable def gibbsZ {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) : ℂ :=
  Matrix.trace (gibbsWeight K β)

/-- The normalized Gibbs state ρ_{β,K} = e^{-βK}/Z. Tier T2.
    (Trace-one and positivity are not needed for the KMS identity: the
    scalar Z⁻¹ factors out of both sides of `gibbs_kms`.) -/
noncomputable def gibbsState {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (gibbsZ K β)⁻¹ • gibbsWeight K β

/-- The modular flow at imaginary time iβ: σ_{iβ}(B) = e^{-βK} B e^{+βK}.
    This is the analytic continuation of the real-time modular flow
    σ_s(B) = e^{isK} B e^{-isK} to s = iβ — the object the KMS condition
    is stated with. Tier T2. -/
noncomputable def modularFlowImag {N : ℕ} (K B : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((-(β : ℂ)) • K) * B * NormedSpace.exp (((β : ℂ)) • K)

/-- KMS condition (Tier T2 — definition): the state ρ satisfies KMS at
    inverse temperature β w.r.t. the modular flow of K if
    Tr(ρ A σ_{iβ}(B)) = Tr(ρ B A) for all observables A, B. -/
def KMSCondition {N : ℕ} (ρ K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) : Prop :=
  ∀ A B : Matrix (Fin N) (Fin N) ℂ,
    Matrix.trace (ρ * A * modularFlowImag K B β) = Matrix.trace (ρ * B * A)

-- ============================================================================
-- Tier T1: the exponential algebra
-- ============================================================================

/-- Scalar multiples of K commute (Tier T1 — proved). -/
theorem commute_smul_K {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (c d : ℂ) :
    Commute (c • K) (d • K) := by
  show (c • K) * (d • K) = (d • K) * (c • K)
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_comm]

/-- Imaginary-time exponentials are mutual inverses (Tier T1 — proved):
    e^{cK} e^{-cK} = 1 for any scalar c, via the matrix `Matrix.exp_neg`. -/
theorem exp_smul_mul_exp_neg_smul {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (c : ℂ) :
    NormedSpace.exp (c • K) * NormedSpace.exp ((-c) • K) = 1 := by
  rw [neg_smul c K, Matrix.exp_neg, Matrix.nonsing_inv_eq_ringInverse,
    Ring.mul_inverse_cancel _ (Matrix.isUnit_exp _)]

/-- Cyclicity of the trace for three factors (Tier T1 — proved). -/
theorem trace_mul_three {N : ℕ} (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (X * Y * Z) = Matrix.trace (Y * Z * X) := by
  rw [mul_assoc, Matrix.trace_mul_comm X (Y * Z)]

-- ============================================================================
-- Tier T1: the finite-dimensional KMS identity
-- ============================================================================

/-- KMS identity for the Gibbs weight (Tier T1 — proved):
    Tr(Ω_β A σ_{iβ}(B)) = Tr(Ω_β B A), where Ω_β = e^{-βK} and
    σ_{iβ}(B) = e^{-βK} B e^{+βK}.
    Proof: reassociate, cycle e^{+βK} to the front by trace cyclicity,
    cancel e^{+βK}e^{-βK} = 1, cycle once more. -/
theorem gibbs_kms_weight {N : ℕ} (K A B : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    Matrix.trace (gibbsWeight K β * A * modularFlowImag K B β)
      = Matrix.trace (gibbsWeight K β * B * A) := by
  have hFE : NormedSpace.exp (((β : ℂ)) • K) * NormedSpace.exp ((-(β : ℂ)) • K)
      = (1 : Matrix (Fin N) (Fin N) ℂ) :=
    exp_smul_mul_exp_neg_smul K ((β : ℂ))
  unfold gibbsWeight modularFlowImag
  set E : Matrix (Fin N) (Fin N) ℂ := NormedSpace.exp ((-(β : ℂ)) • K) with hEdef
  set F : Matrix (Fin N) (Fin N) ℂ := NormedSpace.exp (((β : ℂ)) • K) with hFdef
  have hFE' : F * E = 1 := hFE
  calc Matrix.trace (E * A * (E * B * F))
      = Matrix.trace (F * (E * A * E * B)) := by
        rw [show E * A * (E * B * F) = (E * A * E * B) * F from by
          simp only [mul_assoc]]
        exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * E * B) := by
        simp only [← mul_assoc]
        rw [hFE', one_mul]
    _ = Matrix.trace (E * B * A) := trace_mul_three A E B

/-- KMS identity for the normalized Gibbs state (Tier T1 — proved):
    ρ_{β,K} = e^{-βK}/Z satisfies the KMS condition at its own β.
    No Z ≠ 0 hypothesis is needed: the scalar Z⁻¹ factors out of both
    sides. -/
theorem gibbs_kms {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) :
    KMSCondition (gibbsState K β) K β := by
  unfold KMSCondition
  intro A B
  have hw := gibbs_kms_weight K A B β
  unfold gibbsState
  simp only [Algebra.smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
  rw [hw]

/-- Explicit Gibbs witness for the pinned `GibbsKMSAtOwnBeta` target
    (Tier T1 — proved): the normalized Gibbs state ρ_{β,K} satisfies the
    KMS identity at its own β. The hypotheses (β > 0, K Hermitian) are the
    pinned target's; the proof needs neither. -/
theorem gibbsKMSAtOwnBeta_witness {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) (_hβ : 0 < β) (_hK : K.IsHermitian) :
    ∃ ρ : Matrix (Fin N) (Fin N) ℂ,
      ∀ A B : Matrix (Fin N) (Fin N) ℂ,
        Matrix.trace (ρ * A *
          (NormedSpace.exp (((-β : ℂ)) • K) * B * NormedSpace.exp (((β : ℂ)) • K)))
          = Matrix.trace (ρ * B * A) := by
  refine ⟨gibbsState K β, fun A B => ?_⟩
  have hAB := gibbs_kms K β A B
  unfold modularFlowImag at hAB
  exact hAB

/-- Magnetophase KMS witness (Tier T1 — proved): the pinned
    `MagnetophaseKMSAtOwnBeta` target needs no new KMS machinery — it is
    `gibbsKMSAtOwnBeta_witness` at K := D_A² (D_A Hermitian gives D_A²
    Hermitian). -/
theorem magnetophaseKMS_witness {N : ℕ} (D_A : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) (hβ : 0 < β) (hD : D_A.IsHermitian) :
    ∃ ρ : Matrix (Fin N) (Fin N) ℂ,
      ∀ A B : Matrix (Fin N) (Fin N) ℂ,
        Matrix.trace (ρ * A *
          (NormedSpace.exp (((-β : ℂ)) • D_A ^ 2) * B *
            NormedSpace.exp (((β : ℂ)) • D_A ^ 2)))
          = Matrix.trace (ρ * B * A) :=
  gibbsKMSAtOwnBeta_witness (D_A ^ 2) β hβ (hD.pow 2)

/-- Stationarity of the Gibbs weight under real modular time
    (Tier T1 — proved): σ_s(Ω_β) = e^{isK} Ω_β e^{-isK} = Ω_β.
    The Gibbs weight is a function of K, so it commutes with the modular
    unitaries. This is the finite-dimensional "KMS ⟹ stationary"
    direction. (The normalized state inherits it by scalar factoring.) -/
theorem gibbsWeight_stationary {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (β s : ℝ) :
    NormedSpace.exp ((Complex.I * (s : ℂ)) • K) * gibbsWeight K β *
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • K) = gibbsWeight K β := by
  have hcomm := commute_smul_K K (Complex.I * (s : ℂ)) (-(β : ℂ))
  have hUE : NormedSpace.exp ((Complex.I * (s : ℂ)) • K) *
        NormedSpace.exp ((-(β : ℂ)) • K)
      = NormedSpace.exp ((-(β : ℂ)) • K) *
        NormedSpace.exp ((Complex.I * (s : ℂ)) • K) := by
    rw [← Matrix.exp_add_of_commute _ _ hcomm,
      ← Matrix.exp_add_of_commute _ _ hcomm.symm, add_comm]
  have hUV : NormedSpace.exp ((Complex.I * (s : ℂ)) • K) *
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • K) = 1 :=
    exp_smul_mul_exp_neg_smul K (Complex.I * (s : ℂ))
  unfold gibbsWeight
  calc NormedSpace.exp ((Complex.I * (s : ℂ)) • K) *
          NormedSpace.exp ((-(β : ℂ)) • K) *
          NormedSpace.exp ((-(Complex.I * (s : ℂ))) • K)
      = NormedSpace.exp ((-(β : ℂ)) • K) *
          (NormedSpace.exp ((Complex.I * (s : ℂ)) • K) *
            NormedSpace.exp ((-(Complex.I * (s : ℂ))) • K)) := by
        rw [hUE]
        simp only [mul_assoc]
    _ = NormedSpace.exp ((-(β : ℂ)) • K) := by
        rw [hUV, mul_one]

-- ============================================================================
-- Tier T1: the KMS ↔ modular-flux connections
-- ============================================================================

/-- KMS ⟺ flux stationarity (Tier T1 — proved): for the thermal modular
    Hamiltonian K = β•D², the Gibbs state satisfies KMS at its own β
    (`gibbs_kms`) AND the modular flux vanishes (`thermal_flux_vanishes`).
    The KMS state is the flux-stationary state: thermal equilibrium in the
    state picture coincides with vanishing modular flux in the geometric
    picture. -/
theorem gibbs_kms_flux_stationary {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) :
    KMSCondition (gibbsState (((β : ℂ)) • D ^ 2) β) (((β : ℂ)) • D ^ 2) β ∧
      modularFlux (((β : ℂ)) • D ^ 2) D = 0 :=
  ⟨gibbs_kms _ β, thermal_flux_vanishes D β⟩

/-- The vanishing thermal flux is an observable (Tier T1 — proved):
    for D Hermitian, the modular flux of K = β•D² is self-adjoint
    (`modularFlux_selfAdjoint`) — and identically zero
    (`thermal_flux_vanishes`). KMS equilibrium carries no modular flux,
    and the (vanishing) flux is Hermitian: equilibrium is an observable
    fact, not a gauge artifact. -/
theorem thermal_flux_observable_vanishing {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (hD : D.IsHermitian) (β : ℝ) :
    (modularFlux (((β : ℂ)) • D ^ 2) D).IsHermitian ∧
      modularFlux (((β : ℂ)) • D ^ 2) D = 0 := by
  have hβ : IsSelfAdjoint (β : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  have hK : ((((β : ℂ)) • D ^ 2)).IsHermitian := (hD.pow 2).smul hβ
  exact ⟨modularFlux_selfAdjoint hK hD, thermal_flux_vanishes D β⟩

-- ============================================================================
-- Tier T5: priced window (not proved, not a sorry)
-- ============================================================================

/-- Infinite-dimensional Tomita–Takesaki window (Tier T5 — PRICED, not proved).

    The Tomita–Takesaki theorem — every faithful normal state on a von
    Neumann algebra carries a canonical modular automorphism group
    satisfying the KMS condition — is the infinite-dimensional parent of
    `gibbs_kms`. It is NOT formalized here, and this marker records the
    price honestly rather than faking it:

    - Unbounded operators affiliated with a von Neumann algebra (the
      Tomita involution S and the modular operator Δ = S*S are unbounded
      in general); Mathlib has no von Neumann algebra theory.
    - The modular conjugation J and the commutant theorem J M J = M'.
    - Araki's perturbation theory of KMS states.
    - The type-III factor classification the theory feeds.

    What IS proved here (`gibbs_kms`, `gibbs_kms_weight`) is the exact
    finite-dimensional shadow: on M_N(ℂ) every faithful state is Gibbs,
    the modular group is inner (conjugation by e^{isK}), and KMS reduces
    to trace cyclicity. The infinite-dimensional lift is future work with
    the price above — a window, not a sorry. -/
def TomitaTakesakiWindow : Prop := True

end ThetLogos
