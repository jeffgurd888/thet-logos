import Mathlib.Tactic
import ThetLogos.GibbsSpan
import ThetLogos.TwistedTriple

open Matrix

namespace ThetLogos

/-!
# ThetLogos.ThermalTimeBridge — the finite thermal-time bridge

## Audit and pinned statement

The corpus already owns the components of the finite Connes–Rovelli /
Tomita–Takesaki picture, but in several dialects:

* `KMSBridge` owns the normalized matrix Gibbs state
  `gibbsState K β = (gibbsZ K β)⁻¹ • gibbsWeight K β`, the finite KMS
  relation `gibbs_kms`, and stationarity of the unnormalized Gibbs weight.
* `ThermalClock` owns the packaged `GibbsClock`: its state is that Gibbs
  state, its non-scalar modular generator is `β • K`, its real-time flow is
  `modularFlow (β • K)`, the one-parameter law `GibbsClock.flow_add`, the
  own-β KMS transport `GibbsClock.kms`, and the thermal/laboratory
  conversion `GibbsClock.conversion`.
* `GibbsSpan` owns the identification of that matrix modular flow with the
  built Heisenberg evolution and Schrödinger-picture stationarity of the
  Gibbs state under the laboratory Hamiltonian's own density flow.
* `ModularTime` owns `modularFlux K A = Complex.I • (K * A - A * K)` and
  proves it is self-adjoint for Hermitian `K, A`, but explicitly leaves the
  derivative identity for a modular orbit unproved there.
* `ThermalKMS` owns only an abstract `ModularData` group law on the fixed
  32-dimensional seat; it is not used as a substitute for the Gibbs flow.
* `SpectralClock` and the measured-clock modules own finite clock readings
  and fit decisions, not a Gibbs-state modular flow.  They are not content
  of this bridge.

The bridge pinned here is therefore the general finite matrix statement
for a packaged `GibbsClock G`.  Its flow is proved to be a
one-parameter group of *-automorphisms, to fix `G.state`, to preserve the
thermal trace expectation, to satisfy KMS at the clock's own `β`, and to
convert to laboratory time at the constant rate `β`.  The
infinitesimal-generator (derivative) clause is NOT landed here: it is
the named residue DERIV-1, with its obstruction recorded in the residue
note inside the module — the outcome is PARTIAL at exactly that clause.
This is an assembly of owned finite-level objects plus the elementary
automorphism/stationarity/expectation consequences recorded below; it is
not a continuum Tomita–Takesaki theorem.

## Fences

Finite matrices only.  The theorem says nothing about physical time in
general, quasars, the solar clock, cosmology, or any Millennium problem.
Those topics are not content here.  NO CLAIM; dials 0/4.
-/

/-- The thermal expectation of an observable in a Gibbs clock's own
    state: `Tr (ρ A)`.  This is a definition, not a new state. -/
noncomputable def GibbsClock.expectation {N : ℕ} (G : GibbsClock N)
    (A : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  Matrix.trace (G.state * A)

/-- The Gibbs clock's declared generator is Hermitian: it is a real
    scalar multiple of the clock's Hermitian laboratory Hamiltonian. -/
theorem GibbsClock.generator_isHermitian {N : ℕ} (G : GibbsClock N) :
    G.generator.IsHermitian := by
  have hβ : IsSelfAdjoint (G.beta : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  exact G.K_hermitian.smul hβ

/-- The Gibbs clock at thermal time zero is the identity map. -/
theorem GibbsClock.flow_zero {N : ℕ} (G : GibbsClock N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow 0 A = A :=
  modularFlow_zero G.generator A

/-- The Gibbs clock's flow in the corpus's built Heisenberg form. -/
theorem GibbsClock.flow_eq_heisenbergFlow {N : ℕ} (G : GibbsClock N)
    (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s A = GibbsSpan.heisenbergFlow G.generator s A :=
  GibbsSpan.modularFlow_eq_heisenbergFlow G.generator_isHermitian s A

/-- The Gibbs clock's flow as unitary conjugation, in the corpus's
    `twistConj` dialect. -/
theorem GibbsClock.flow_eq_twistConj {N : ℕ} (G : GibbsClock N)
    (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s A
      = twistConj (GibbsSpan.evolutionUnitary G.generator s)ᴴ A := by
  rw [G.flow_eq_heisenbergFlow]
  unfold GibbsSpan.heisenbergFlow twistConj
  rw [Matrix.conjTranspose_conjTranspose]

/-- Multiplicativity of the Gibbs clock flow: each thermal-time map is
    an algebra homomorphism. -/
theorem GibbsClock.flow_mul {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A B : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s (A * B) = G.flow s A * G.flow s B := by
  obtain ⟨hU1, hU2⟩ :=
    GibbsSpan.evolutionUnitary_isUnitary G.generator_isHermitian s
  have hA : (GibbsSpan.evolutionUnitary G.generator s)ᴴᴴ
        * (GibbsSpan.evolutionUnitary G.generator s)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU2
  have hB : (GibbsSpan.evolutionUnitary G.generator s)ᴴ
        * (GibbsSpan.evolutionUnitary G.generator s)ᴴᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU1
  rw [G.flow_eq_twistConj, G.flow_eq_twistConj, G.flow_eq_twistConj]
  exact twistConj_mul _ hA hB A B

/-- Additivity of the Gibbs clock flow. -/
theorem GibbsClock.flow_add_apply {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A B : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s (A + B) = G.flow s A + G.flow s B := by
  rw [G.flow_eq_twistConj, G.flow_eq_twistConj, G.flow_eq_twistConj]
  unfold twistConj
  rw [Matrix.mul_add, Matrix.add_mul]

/-- Scalar homogeneity of the Gibbs clock flow. -/
theorem GibbsClock.flow_smul {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s (c • A) = c • G.flow s A := by
  rw [G.flow_eq_twistConj, G.flow_eq_twistConj]
  unfold twistConj
  rw [Matrix.mul_smul, smul_mul_assoc]

/-- The Gibbs clock flow preserves the identity observable. -/
theorem GibbsClock.flow_one {N : ℕ} (G : GibbsClock N) (s : ℝ) :
    G.flow s (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  obtain ⟨hU1, -⟩ :=
    GibbsSpan.evolutionUnitary_isUnitary G.generator_isHermitian s
  rw [G.flow_eq_twistConj]
  unfold twistConj
  rw [Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  exact hU1

/-- The Gibbs clock flow is a *-map. -/
theorem GibbsClock.flow_conjTranspose {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (G.flow s A)ᴴ = G.flow s Aᴴ := by
  rw [G.flow_eq_twistConj, G.flow_eq_twistConj]
  exact twistConj_star _ A

/-- Backward thermal time inverts forward thermal time. -/
theorem GibbsClock.flow_neg_flow {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow (-s) (G.flow s A) = A := by
  have h := G.flow_add (-s) s A
  rw [neg_add_cancel, G.flow_zero] at h
  exact h.symm

/-- Forward thermal time also inverts backward thermal time. -/
theorem GibbsClock.flow_flow_neg {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s (G.flow (-s) A) = A := by
  have h := G.flow_add s (-s) A
  rw [add_neg_cancel, G.flow_zero] at h
  exact h.symm

/-- The unnormalized Gibbs weight is stationary under the Gibbs clock's
    own flow.  This transports the owned laboratory-flow stationarity
    through the owned conversion theorem. -/
theorem GibbsClock.flow_weight_stationary {N : ℕ} (G : GibbsClock N)
    (s : ℝ) :
    G.flow s (gibbsWeight G.K G.beta) = gibbsWeight G.K G.beta := by
  calc G.flow s (gibbsWeight G.K G.beta)
      = modularFlow G.K (G.beta * s) (gibbsWeight G.K G.beta) :=
        GibbsClock.conversion G s _
    _ = gibbsWeight G.K G.beta := G.weight_stationary _

/-- **The Gibbs state is fixed by its own clock.** -/
theorem GibbsClock.flow_state_stationary {N : ℕ} (G : GibbsClock N)
    (s : ℝ) :
    G.flow s G.state = G.state := by
  unfold GibbsClock.state gibbsState
  rw [G.flow_smul, G.flow_weight_stationary]

/-- The Gibbs clock flow preserves the trace of every observable. -/
theorem GibbsClock.flow_trace {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (G.flow s A) = Matrix.trace A := by
  obtain ⟨hU1, hU2⟩ :=
    GibbsSpan.evolutionUnitary_isUnitary G.generator_isHermitian s
  rw [G.flow_eq_twistConj]
  unfold twistConj
  calc Matrix.trace
        ((GibbsSpan.evolutionUnitary G.generator s)ᴴ * A
          * (GibbsSpan.evolutionUnitary G.generator s)ᴴᴴ)
      = Matrix.trace
          ((GibbsSpan.evolutionUnitary G.generator s)ᴴᴴ
            * ((GibbsSpan.evolutionUnitary G.generator s)ᴴ * A)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace A := by
        rw [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hU2,
          Matrix.one_mul]

/-- **Thermal expectation is invariant under the state's own clock.** -/
theorem GibbsClock.expectation_flow {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    G.expectation (G.flow s A) = G.expectation A := by
  unfold GibbsClock.expectation
  calc Matrix.trace (G.state * G.flow s A)
      = Matrix.trace (G.flow (-s) (G.state * G.flow s A)) :=
        (G.flow_trace (-s) _).symm
    _ = Matrix.trace (G.flow (-s) G.state * G.flow (-s) (G.flow s A)) := by
        rw [G.flow_mul]
    _ = Matrix.trace (G.state * A) := by
        rw [G.flow_state_stationary, G.flow_neg_flow]

/-- A scalar shift of the Gibbs generator — the ambiguity in writing a
    logarithm of the state — does not change the clock. -/
theorem GibbsClock.flow_generator_add_smul_one {N : ℕ} (G : GibbsClock N)
    (c : ℂ) (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow (G.generator + c • 1) s A = G.flow s A :=
  modularFlow_add_smul_one G.generator c s A

/-! ## Named residue — the derivative clause (NOT proved here)

The pinned bridge also asked for the infinitesimal-generator clause:
the derivative of `s ↦ G.flow s A` at `s = 0` is `modularFlux
G.generator A`.  That clause is ABSENT from this landing, for a
corpus-level reason found by attempting it (2026-11-04): in the pinned
Mathlib (v4.35.0-rc3), `NormedSpace.exp` on matrices is the norm-free
topological exponential — its signature needs only `Ring`,
`TopologicalSpace`, `IsTopologicalRing` — and matrices carry no
canonical `NormedRing` (nor even `SeminormedAddCommGroup`) instance
(`#synth` fails; the normed-ring instances in
`Mathlib/Analysis/Matrix/Normed.lean` are all scoped opt-ins).  A
`HasDerivAt` statement for the matrix flow therefore cannot even be
formed in the corpus's own instance context: it requires choosing a
matrix norm (e.g. the Frobenius scoped instances) AND proving the
normed exponential so obtained agrees with the corpus's topological
`modularFlow`.  That is a separate brick — DERIV-1, priced S–M,
est. strict 4–10 — not a silent weakening of this one.  (The scalar
route exists in the corpus for CLM/operator exponentials —
`hasDerivAt_exp_smul_const'`, used in `SchrodingerSmalls` — but its
`NormedRing 𝔸` hypothesis is exactly what matrices lack here.) -/

/-- **THE UNIVERSAL BRIDGE, finite form (headline assembly).**
    For a packaged Gibbs clock `G` — the finite Gibbs state
    `ρ = e^{−βK}/Z` with its non-scalar modular generator `β • K` —
    the state's own modular flow is a clock in the full finite sense:
    it is a one-parameter group of *-automorphisms of the observable
    algebra, it fixes the state and preserves the thermal expectation,
    the state satisfies KMS at the clock's own `β`, thermal time
    converts to laboratory time at the constant rate `β`, the clock is
    unchanged by the scalar (log-partition) ambiguity in `−ln ρ`.
    (The infinitesimal-generator / derivative clause is the named
    residue DERIV-1 — see the residue note above this headline; it is
    NOT a clause of this conjunction.)
    Every clause is one of the theorems above or an owned
    theorem of `ThermalClock`/`KMSBridge`; this headline is an
    assembly at exact equality, in the sense of U-1 ONE KERNEL. -/
theorem GibbsClock.thermal_time_bridge {N : ℕ} (G : GibbsClock N) :
    (∀ s t : ℝ, ∀ A : Matrix (Fin N) (Fin N) ℂ,
      G.flow (s + t) A = G.flow s (G.flow t A)) ∧
    (∀ A : Matrix (Fin N) (Fin N) ℂ, G.flow 0 A = A) ∧
    (∀ (s : ℝ) (A B : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (A * B) = G.flow s A * G.flow s B) ∧
    (∀ (s : ℝ) (A B : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (A + B) = G.flow s A + G.flow s B) ∧
    (∀ (s : ℝ) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.flow s (c • A) = c • G.flow s A) ∧
    (∀ s : ℝ, G.flow s (1 : Matrix (Fin N) (Fin N) ℂ) = 1) ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      (G.flow s A)ᴴ = G.flow s Aᴴ) ∧
    (∀ s : ℝ, G.flow s G.state = G.state) ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.expectation (G.flow s A) = G.expectation A) ∧
    KMSCondition G.state G.K G.beta ∧
    (∀ (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      G.flow s A = modularFlow G.K (G.beta * s) A) ∧
    (∀ (c : ℂ) (s : ℝ) (A : Matrix (Fin N) (Fin N) ℂ),
      modularFlow (G.generator + c • 1) s A = G.flow s A) :=
  ⟨fun s t A => G.flow_add s t A,
   fun A => G.flow_zero A,
   fun s A B => G.flow_mul s A B,
   fun s A B => G.flow_add_apply s A B,
   fun s c A => G.flow_smul s c A,
   fun s => G.flow_one s,
   fun s A => G.flow_conjTranspose s A,
   fun s => G.flow_state_stationary s,
   fun s A => G.expectation_flow s A,
   G.kms,
   fun s A => G.conversion s A,
   fun c s A => G.flow_generator_add_smul_one c s A⟩

end ThetLogos
