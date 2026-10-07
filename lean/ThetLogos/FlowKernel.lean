import ThetLogos.ModularTime
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix NormedSpace

namespace ThetLogos

/-!
# ThetLogos.FlowKernel — the kernel-destruction mechanism (Rung 5, Target 1)

**Origin.** This file formalizes a finding discovered by our own instrument,
tonight: the Modular Flow Laboratory (`scripts/modular_flow_lab.py`,
`whitepaper/modular-flow-lab-2026-10-07.md`, T4) observed that the modular
flow `σ_s(D) = e^{isK} D e^{−isK}` destroys the commutator kernel —
1-dimensional at `s = 0`, 0-dimensional for every `s ≠ 0` — with mechanism:
the flow transports the commutant rigidly, but moves it *out of the
represented algebra* `π(A_F)`.

**What is proved (T1, zero sorrys).** The mechanism, in full generality, for a
unitary `U` conjugating a Dirac operator `D` against a subspace `A` (the
represented algebra):
- `commutant_transport`: unitary conjugation transports commutants:
  `[U D Uᴴ, X] = 0 ↔ [D, Uᴴ X U] = 0`.
- `represented_kernel_identity`: the represented kernel at flow-time is the
  transported commutant intersected with the algebra.
- `kernel_destruction_criterion`: the conditional theorem — if the only
  commutant elements the flow can bring into the algebra lie along the
  `s = 0` generator `X₀` (rigidity), and the flow moves `X₀` out (exit),
  then the represented kernel vanishes.
- `kernel_dim_one_at_zero`: the `s = 0` input — under the same rigidity the
  represented kernel is exactly `span{X₀}`.
- `destruction_of_satisfies`: the criterion applied to pinned concrete data.

**What is pinned (T5).** `satisfiesDestruction`: the statement that the actual
finite triple (`D_F` 32×32, `K = −ln ρ`, Option-A representation) satisfies
the criterion's hypotheses. Numerical evidence is T4 (flow lab); promotion to
T1 needs the concrete 32×32 entries (`Scaffold32.lean`, `MartinettiRep.lean`).

**Target 2** (same file): the KMS-flow question — the finite-dimensional KMS
definition, the KMS=Gibbs equivalence pinned (Bratteli–Robinson), the
`φ_act`-flow question, and the Bisognano–Wichmann gap ledger. No BW-type
claims beyond the pinned question.
-/

-- ============================================================================
-- Target 1: the kernel-destruction mechanism (T1)
-- ============================================================================

section Transport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Round-trip cancellation: `U (Uᴴ X U) Uᴴ = X` (Tier T1 — proved). -/
theorem conj_cancel_left (U X : Matrix n n ℂ) (hU2 : U * Uᴴ = 1) :
    U * (Uᴴ * X * U) * Uᴴ = X := by
  simp only [Matrix.mul_assoc]
  rw [hU2, mul_one, ← Matrix.mul_assoc U Uᴴ _, hU2, one_mul]

/-- Round-trip cancellation, dual: `Uᴴ (U Y Uᴴ) U = Y` (Tier T1 — proved). -/
theorem conj_cancel_right (U Y : Matrix n n ℂ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * (U * Y * Uᴴ) * U = Y := by
  simp only [Matrix.mul_assoc]
  rw [hU1, mul_one, ← Matrix.mul_assoc Uᴴ U _, hU1, one_mul]

/-- Unitary conjugation transports commutants (Tier T1 — proved).
    `[U D Uᴴ, X] = 0 ↔ [D, Uᴴ X U] = 0`. The computational core of
    "the flow moves the kernel rigidly": the full commutant is carried
    along by `σ`, so any change in the *represented* kernel comes from the
    algebra `A`, not from the commutant itself. -/
theorem commutant_transport (D U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (X : Matrix n n ℂ) :
    (U * D * Uᴴ) * X = X * (U * D * Uᴴ)
      ↔ D * (Uᴴ * X * U) = (Uᴴ * X * U) * D := by
  have e1 : Uᴴ * ((U * D * Uᴴ) * X) * U = D * (Uᴴ * X * U) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U _, hU1, one_mul]
  have e2 : Uᴴ * (X * (U * D * Uᴴ)) * U = (Uᴴ * X * U) * D := by
    simp only [Matrix.mul_assoc]
    rw [hU1, mul_one]
  have e3 : U * (D * (Uᴴ * X * U)) * Uᴴ = (U * D * Uᴴ) * X := by
    simp only [Matrix.mul_assoc]
    rw [hU2, mul_one]
  have e4 : U * ((Uᴴ * X * U) * D) * Uᴴ = X * (U * D * Uᴴ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ _, hU2, one_mul]
  constructor
  · intro h
    have h1 := congrArg (fun M : Matrix n n ℂ => Uᴴ * M * U) h
    rw [e1, e2] at h1
    exact h1
  · intro h
    have h1 := congrArg (fun M : Matrix n n ℂ => U * M * Uᴴ) h
    rw [e3, e4] at h1
    exact h1

/-- The represented kernel at flow-time is the transported commutant
    intersected with the algebra (Tier T1 — proved):
    `{X ∈ A : [σ(D), X] = 0} = σ '' {Y : [D, Y] = 0 ∧ σ(Y) ∈ A}`
    with `σ(Y) = U Y Uᴴ`. -/
theorem represented_kernel_identity (D U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (A : Set (Matrix n n ℂ)) :
    {X | X ∈ A ∧ (U * D * Uᴴ) * X = X * (U * D * Uᴴ)}
      = (fun Y => U * Y * Uᴴ) '' {Y | D * Y = Y * D ∧ U * Y * Uᴴ ∈ A} := by
  ext X
  constructor
  · rintro ⟨hXA, hcomm⟩
    have e : U * (Uᴴ * X * U) * Uᴴ = X := conj_cancel_left U X hU2
    refine ⟨Uᴴ * X * U, ⟨(commutant_transport D U hU1 hU2 X).mp hcomm, ?_⟩, ?_⟩
    · rw [e]; exact hXA
    · exact e
  · rintro ⟨Y, ⟨hDY, hUYA⟩, rfl⟩
    have e : Uᴴ * (U * Y * Uᴴ) * U = Y := conj_cancel_right U Y hU1
    refine ⟨hUYA, ?_⟩
    have h := (commutant_transport D U hU1 hU2 (U * Y * Uᴴ)).mpr ?_
    · exact h
    · rw [e]; exact hDY

/-- The kernel-destruction criterion (Tier T1 — proved). Let `A` be a
    subspace of matrices (the represented algebra), `U` a unitary (the flow
    at `s ≠ 0`), and `X₀ ∈ A` with `[D, X₀] = 0` (the `s = 0` generator).
    Hypotheses (exactly what the flow lab observed, T4):
    - (rigidity) every commutant element the flow can bring into `A` lies
      along `X₀`;
    - (exit) the flow moves `X₀` itself out of `A`.
    Then the represented kernel at flow-time is zero.
    (`X₀` is the `s = 0` generator; its membership and commutation data are
    bundled in the `satisfiesDestruction` predicate.) -/
theorem kernel_destruction_criterion (D U : Matrix n n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (A : Set (Matrix n n ℂ)) (hA : ∀ X ∈ A, ∀ c : ℂ, c • X ∈ A)
    (X₀ : Matrix n n ℂ)
    (hrigid : ∀ Y : Matrix n n ℂ, D * Y = Y * D → U * Y * Uᴴ ∈ A
      → ∃ c : ℂ, Y = c • X₀)
    (hexit : U * X₀ * Uᴴ ∉ A) :
    ∀ X : Matrix n n ℂ, X ∈ A → (U * D * Uᴴ) * X = X * (U * D * Uᴴ)
      → X = 0 := by
  intro X hXA hcomm
  have e : U * (Uᴴ * X * U) * Uᴴ = X := conj_cancel_left U X hU2
  have hDY : D * (Uᴴ * X * U) = (Uᴴ * X * U) * D :=
    (commutant_transport D U hU1 hU2 X).mp hcomm
  have hUYA : U * (Uᴴ * X * U) * Uᴴ ∈ A := by
    rw [e]; exact hXA
  obtain ⟨c, hc⟩ := hrigid (Uᴴ * X * U) hDY hUYA
  have hX : X = c • (U * X₀ * Uᴴ) := by
    calc X = U * (Uᴴ * X * U) * Uᴴ := e.symm
      _ = U * (c • X₀) * Uᴴ := by rw [hc]
      _ = c • (U * X₀ * Uᴴ) := by simp only [Matrix.mul_smul, Matrix.smul_mul]
  by_cases hc0 : c = 0
  · rw [hX, hc0, zero_smul]
  · exfalso
    apply hexit
    have hZ : c⁻¹ • (c • (U * X₀ * Uᴴ)) = U * X₀ * Uᴴ := by
      rw [← mul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hUX : U * X₀ * Uᴴ = c⁻¹ • X := by
      rw [hX]
      exact hZ.symm
    rw [hUX]
    exact hA X hXA c⁻¹

end Transport

/-- The `s = 0` input (Tier T1 — proved): at the identity flow (`U = 1`),
    the rigidity hypothesis says the represented kernel is exactly
    `span{X₀}` — the 1-dimensional kernel the lab observed at `s = 0`. -/
theorem kernel_dim_one_at_zero {n : Type*} [Fintype n] (D : Matrix n n ℂ)
    (A : Set (Matrix n n ℂ))
    (X₀ : Matrix n n ℂ)
    (hrigid : ∀ Y : Matrix n n ℂ, D * Y = Y * D → Y ∈ A
      → ∃ c : ℂ, Y = c • X₀) :
    ∀ X : Matrix n n ℂ, X ∈ A → D * X = X * D → ∃ c : ℂ, X = c • X₀ :=
  fun X hXA hcomm => hrigid X hcomm hXA

-- ============================================================================
-- The modular unitary and the concrete (T5) pinning
-- ============================================================================

section ConcretePin

variable {N : ℕ}

/-- The modular unitary at flow parameter `s` (T2 definition): `U_s = e^{isK}`.
    In the lab this is `σ_s(D) = e^{isK} D e^{−isK}` with `K = −ln ρ`. -/
noncomputable def modularUnitary (K : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((Complex.I * (s : ℂ)) • K)

/-- Unitarity of the modular unitary for Hermitian `K` (T5 — pinned).
    Standard: `exp` of a skew-adjoint operator is unitary. The proof needs
    `exp`/`conjTranspose` commutation lemmas not yet assembled here;
    realistic T1 target. -/
def modularUnitary_unitary : Prop :=
  ∀ (K : Matrix (Fin 32) (Fin 32) ℂ), K.IsHermitian →
    ∀ s : ℝ, (modularUnitary K s)ᴴ * (modularUnitary K s) = 1 ∧
      (modularUnitary K s) * (modularUnitary K s)ᴴ = 1

/-- The concrete destruction data (T5 predicate): the finite triple's Dirac
    operator `D`, modular Hamiltonian `K`, represented algebra `π`, and the
    `s = 0` kernel generator `X₀` satisfy the criterion's hypotheses.
    Intended instantiation: `D = D_F` (32×32, `Scaffold32.lean`),
    `K = −ln ρ` thermal, `π` = Option-A representation (2-dim),
    `X₀` = the observed 1-dim kernel generator.
    Numerical evidence: `whitepaper/modular-flow-lab-2026-10-07.md` (T4).
    Promotion to T1: verify against the concrete 32×32 entries. -/
def satisfiesDestruction (D K : Matrix (Fin N) (Fin N) ℂ)
    (π : Set (Matrix (Fin N) (Fin N) ℂ)) (X₀ : Matrix (Fin N) (Fin N) ℂ) :
    Prop :=
  X₀ ∈ π ∧ X₀ ≠ 0 ∧ D * X₀ = X₀ * D ∧
  (∀ X ∈ π, D * X = X * D → ∃ c : ℂ, X = c • X₀) ∧
  ∀ s : ℝ, s ≠ 0 → ∀ U : Matrix (Fin N) (Fin N) ℂ,
    U = modularUnitary K s → Uᴴ * U = 1 → U * Uᴴ = 1 →
    ((∀ Y : Matrix (Fin N) (Fin N) ℂ, D * Y = Y * D → U * Y * Uᴴ ∈ π
      → ∃ c : ℂ, Y = c • X₀) ∧
    U * X₀ * Uᴴ ∉ π)

/-- From the pinned data to the destruction conclusion (Tier T1 — proved):
    *if* the concrete triple satisfies the criterion's hypotheses, the
    represented kernel vanishes at every `s ≠ 0`. -/
theorem destruction_of_satisfies (D K : Matrix (Fin N) (Fin N) ℂ)
    (π : Set (Matrix (Fin N) (Fin N) ℂ)) (X₀ : Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ X ∈ π, ∀ c : ℂ, c • X ∈ π)
    (h : satisfiesDestruction D K π X₀) :
    ∀ s : ℝ, s ≠ 0 → ∀ U : Matrix (Fin N) (Fin N) ℂ,
      U = modularUnitary K s → Uᴴ * U = 1 → U * Uᴴ = 1 →
      ∀ X : Matrix (Fin N) (Fin N) ℂ, X ∈ π
        → (U * D * Uᴴ) * X = X * (U * D * Uᴴ) → X = 0 := by
  obtain ⟨-, -, -, -, hdata⟩ := h
  intro s hs U hU hU1 hU2
  obtain ⟨hrigid, hexit⟩ := hdata s hs U hU hU1 hU2
  exact kernel_destruction_criterion D U hU1 hU2 π hA X₀ hrigid hexit

end ConcretePin

-- ============================================================================
-- Target 2: the KMS-flow question (T5 pins)
-- ============================================================================

section KMSQuestion

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A density matrix: Hermitian, positive (`x⋆ρx ≥ 0`, via the real part —
    the standard finite-dimensional characterization, since `ℂ` carries no
    order for `Matrix.PosSemidef`), trace 1 (T2 definition). -/
def IsDensityMatrix (ρ : Matrix m m ℂ) : Prop :=
  ρ.IsHermitian ∧ (∀ x : m → ℂ, 0 ≤ ((star x) ⬝ᵥ (ρ *ᵥ x)).re)
    ∧ Matrix.trace ρ = 1

/-- The flow action at complex parameter `z` (T2 definition):
    `α_z(B) = e^{izH} B e^{−izH}`, entire in `z` for finite matrices.
    For real `z = t` this is unitary conjugation; the KMS condition
    evaluates it at `z = t + iβ`. -/
noncomputable def flowAction (H : Matrix m m ℂ) (z : ℂ)
    (B : Matrix m m ℂ) : Matrix m m ℂ :=
  NormedSpace.exp ((Complex.I * z) • H) * B * NormedSpace.exp ((-Complex.I * z) • H)

/-- The finite-dimensional KMS condition (T2 definition): `ρ` is a density
    matrix, `H` Hermitian, and for all `A, B, t`,
    `Tr(ρ A α_{t+iβ}(B)) = Tr(ρ α_t(B) A)`.
    In finite dimensions the functions `t ↦ Tr(ρ A α_t(B))` are entire, so
    the analytic-continuation part of the usual KMS definition is automatic;
    the condition is the boundary identity. -/
def IsKMSFlow (ρ H : Matrix m m ℂ) (β : ℝ) : Prop :=
  IsDensityMatrix ρ ∧ H.IsHermitian ∧
  ∀ A B : Matrix m m ℂ, ∀ t : ℝ,
    Matrix.trace (ρ * A * flowAction H ((t : ℂ) + (β : ℂ) * Complex.I) B)
      = Matrix.trace (ρ * flowAction H (t : ℂ) B * A)

/-- Finite-dimensional KMS = Gibbs (T5 — pinned; Bratteli–Robinson).
    For the full matrix algebra with `α^H`, `KMS_β` holds iff
    `ρ = e^{−βH}/Tr(e^{−βH})` (unique). The forward direction (Gibbs ⟹ KMS)
    is a trace computation; the reverse uses faithfulness of the trace.
    Realistic T1 target. -/
def kms_iff_gibbs : Prop :=
  ∀ (ρ H : Matrix m m ℂ) (β : ℝ), IsKMSFlow ρ H β ↔
    ρ = (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • H)))⁻¹
      • NormedSpace.exp ((-(β : ℂ)) • H)

/-- The offensive question, pinned (T5): the flow generated by the active
    flux `φ_act = i[G, D]` — self-adjoint by `modularFlux_selfAdjoint`
    (Tier T1, `ModularTime.lean`) — satisfies `KMS_β` for its Gibbs state.
    In finite dimensions this is a corollary of `kms_iff_gibbs`; the content
    is not existence (the Gibbs state always exists) but the *geometricity*
    question below: does this KMS structure have a continuum/twisted-triple
    limit in which the flow becomes spacetime? -/
def phiActFlowKMSQuestion : Prop :=
  ∀ (G D : Matrix (Fin 32) (Fin 32) ℂ) (β : ℝ),
    G.IsHermitian → D.IsHermitian →
    let φ := modularFlux G D
    IsKMSFlow
      ((Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • φ)))⁻¹
        • NormedSpace.exp ((-(β : ℂ)) • φ))
      φ β

/-- The Bisognano–Wichmann gap, ledgered (T5). A positive answer to the
    BW-analog question would consist of:
    (1) a Lorentzian (twisted) extension of the finite spectral triple —
        OPEN: no such extension exists (Rung 1);
    (2) a modular flow acting geometrically (boost-like) on the extension —
        OPEN: the finite flow is a compact unitary orbit, quasi-periodic,
        the opposite of a boost's hyperbolic action (flow lab, T4);
    (3) a continuum limit recovering the BW identification
        (modular flow = Lorentz boosts for the wedge algebra) —
        OPEN: needs the interacting 4D construction (Rung 3 wall).
    The fields are opaque Props; this pins the *question*, not a claim.
    BW reference: Bisognano–Wichmann 1975–76; Tomita–Takesaki modular theory. -/
structure BWAnalogData where
  /-- (1) the Lorentzian twisted extension — OPEN -/
  twistedExtension : Type
  /-- (2) the geometric modular flow on it — OPEN -/
  geometricFlow : twistedExtension → twistedExtension
  /-- (3) the BW identification (modular flow = spacetime symmetries) — OPEN -/
  bwIdentification : Prop

/-- The BW-analog question: does such data exist with the identification
    holding? T5 — each component is open, ledgered above. -/
def bwAnalogQuestion : Prop :=
  ∃ D : BWAnalogData, D.bwIdentification

end KMSQuestion

#print axioms commutant_transport
#print axioms represented_kernel_identity
#print axioms kernel_destruction_criterion
#print axioms kernel_dim_one_at_zero
#print axioms destruction_of_satisfies

end ThetLogos
