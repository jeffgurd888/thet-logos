import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import ThetLogos.ModularTime
import ThetLogos.ThermalKMS
import ThetLogos.KMSBridge

/-!
# ThetLogos.ThermalClock — the thermal clock of a finite state (Tiers T1/T2)

Charter: `whitepaper/thermal-clock-charter-DRAFT-2026-10-17.md` (NO CLAIM).
Origin (Jeff, 2026-10-17): "people call a year 1 trip around the sun. can we
now define the thermal clock."

Two clocks, honestly separated:

- **Travel clock** — external, counts trips (a year is one orbit, a day one
  spin). Metrology; no Lean content is claimed for it here.
- **Thermal clock** — internal, one per state: for a faithful finite state ρ,
  the modular Hamiltonian K = −ln ρ generates the modular flow, and **the
  flow parameter is thermal time**. Nothing travels; the state itself is the
  clock and heat is its mechanism.

This module collects, under one name, the definition and the clock
properties the corpus already carries scattered across `ModularTime.lean`
(the eigenbasis/diagonal picture), `ThermalKMS.lean` (the abstract
`ModularData` group law), and `KMSBridge.lean` (the Gibbs/KMS matrix
picture), and proves the conversion between thermal and laboratory time
for Gibbs states: **physical time = β × thermal time** — temperature is the
exchange rate between the two clocks, the same structural role c plays
between years and light-years in the travel system.

## Fences (what this module does NOT claim)

- Finite level / finite modes only. No continuum, no infinite-dimensional
  statement.
- The thermal clock is a property of a *state*, not of spacetime.
- No claim that physical time in general IS thermal time: the
  Connes–Rovelli thermal-time hypothesis is T4/T5 literature, cited as
  such, not proved or assumed here. What is proved is the finite-level
  conversion for Gibbs states, below.
- Not a solution to the problem of time.
- NO CLAIM on any Millennium statement; this is foundations packaging,
  like the Bridge exhibit.
- The pre-existing T3 `sorry` in `ModularTime.kms_identity_diagonal` is
  quarantined: nothing in this module routes through it. The Gibbs
  conversion is proved from `modularEigenvalue_diff` and direct phase
  algebra, not from the KMS identity in the eigenbasis.

Tier map:
- T2 (definitions): `ThermalClock`, `GibbsClock`, `modularFlow`,
  `hamiltonianFlow`, `gibbsDiagWeights`.
- T1 (proved): everything else — the group law in both pictures, the
  Gibbs conversion in eigenvalue, diagonal-flow, and matrix form, the
  stopped-clock theorems, and the transports of corpus anchors
  (`ModularData.flow_add`, `gibbs_kms`, `gibbsWeight_stationary`,
  `thermal_flux_vanishes`) restated in clock language.
-/

open Matrix NormedSpace

namespace ThetLogos

-- ============================================================================
-- §1. The clock: definition in the eigenbasis picture (Deliverable 1)
-- ============================================================================

/-- A **thermal clock**: a faithful finite state, packaged by its
    eigenbasis weights. The state's modular Hamiltonian K = −ln ρ and its
    modular flow are *derived* from the weights (see `ThermalClock.K`,
    `ThermalClock.flow`), never stipulated — per the charter's stop
    condition. Faithfulness (every weight strictly positive) is the side
    condition that makes `log` honest: at a zero weight the clock's
    generator is not defined by this formula. Tier T2. -/
structure ThermalClock (N : ℕ) where
  /-- Eigenbasis weights of the state ρ = diag(weights). -/
  weights : Fin N → ℝ
  /-- Faithfulness: every weight is strictly positive. -/
  faithful : ∀ j, 0 < weights j
  /-- Normalization: the weights sum to 1 (ρ is a state). -/
  normalized : ∑ j, weights j = 1

/-- The clock's state ρ = diag(weights). Derived, Tier T2. -/
noncomputable def ThermalClock.state {N : ℕ} (C : ThermalClock N) :
    Matrix (Fin N) (Fin N) ℂ :=
  diagState C.weights

/-- The clock's modular Hamiltonian K = −ln ρ, diagonal in the eigenbasis
    with entries −log w_j. Derived from ρ — this *is* −ln ρ computed in
    the eigenbasis (`diagModularK`), not a stipulated generator.
    Tier T2. -/
noncomputable def ThermalClock.K {N : ℕ} (C : ThermalClock N) :
    Matrix (Fin N) (Fin N) ℂ :=
  diagModularK C.weights

/-- The clock's flow: σ_s = the modular flow of the clock's state at
    thermal time s. **Thermal time is the flow parameter s.** Tier T2. -/
noncomputable def ThermalClock.flow {N : ℕ} (C : ThermalClock N) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  diagFlow C.weights s a

/-- The state's diagonal entries are the weights (Tier T1 — proved). -/
theorem ThermalClock.state_apply_diag {N : ℕ} (C : ThermalClock N) (j : Fin N) :
    C.state j j = (C.weights j : ℂ) := by
  simp [ThermalClock.state, diagState, Matrix.diagonal_apply_eq]

/-- The clock's K really is −ln ρ: its diagonal entries are −log of the
    state's diagonal entries (Tier T1 — proved). -/
theorem ThermalClock.K_apply_diag {N : ℕ} (C : ThermalClock N) (j : Fin N) :
    C.K j j = ((-Real.log (C.weights j) : ℝ) : ℂ) := by
  simp [ThermalClock.K, diagModularK, Matrix.diagonal_apply_eq]

/-- The clock's generator is Hermitian — an observable (Tier T1 — proved):
    K = −ln ρ has real eigenvalues −log w_j. -/
theorem ThermalClock.K_isHermitian {N : ℕ} (C : ThermalClock N) :
    C.K.IsHermitian := by
  rw [Matrix.IsHermitian, ThermalClock.K, diagModularK]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

-- ============================================================================
-- §2. Clock additivity: thermal time composes (Deliverable 2)
-- ============================================================================

/-- The phase factors compose: w^{i(s+t)} = w^{is} · w^{it}
    (Tier T1 — proved). -/
theorem cpowI_add (w : ℝ) (s t : ℝ) :
    cpowI w (s + t) = cpowI w s * cpowI w t := by
  unfold cpowI
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Entry formula for the eigenbasis flow (Tier T1 — proved). -/
theorem diagFlow_apply {N : ℕ} (w : Fin N → ℝ) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    diagFlow w s a i j = cpowI (w i) s * a i j * cpowI (w j) (-s) := by
  unfold diagFlow
  rw [mul_diagonal, diagonal_mul]

/-- The eigenbasis flow at thermal time 0 is the identity
    (Tier T1 — proved). -/
theorem diagFlow_zero {N : ℕ} (w : Fin N → ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) : diagFlow w 0 a = a := by
  ext i j
  rw [diagFlow_apply]
  have h0 : cpowI (w i) 0 = 1 := by
    unfold cpowI
    simp
  have h0' : cpowI (w j) (-0) = 1 := by
    unfold cpowI
    simp
  rw [h0, h0', one_mul, mul_one]

/-- **Clock additivity, eigenbasis form** (Tier T1 — proved): flowing for
    thermal time s + t is flowing for t, then for s. Thermal time
    composes additively — the one-parameter group law of the clock. -/
theorem diagFlow_add {N : ℕ} (w : Fin N → ℝ) (s t : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow w (s + t) a = diagFlow w s (diagFlow w t a) := by
  ext i j
  rw [diagFlow_apply, diagFlow_apply, diagFlow_apply,
    show -(s + t) = -s + -t by ring, cpowI_add, cpowI_add]
  ring

/-- **Clock additivity for a `ThermalClock`** (Tier T1 — proved):
    `C.flow (s + t) = C.flow s ∘ C.flow t`. -/
theorem ThermalClock.flow_add {N : ℕ} (C : ThermalClock N) (s t : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    C.flow (s + t) a = C.flow s (C.flow t a) :=
  diagFlow_add C.weights s t a

/-- The clock at thermal time 0 does not move (Tier T1 — proved). -/
theorem ThermalClock.flow_zero {N : ℕ} (C : ThermalClock N)
    (a : Matrix (Fin N) (Fin N) ℂ) : C.flow 0 a = a :=
  diagFlow_zero C.weights a

/-- Rescaling all weights by a positive constant — a change of
    normalization, e.g. dividing by the partition function — does not
    change the clock (Tier T1 — proved): the phases pick up exp(±is·log c)
    factors that cancel. This is why the clock of ρ and of Z·ρ agree. -/
theorem diagFlow_scale_weights {N : ℕ} (w : Fin N → ℝ) {c : ℝ} (hc : 0 < c)
    (hw : ∀ j, 0 < w j) (s : ℝ) (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (fun j => c * w j) s a = diagFlow w s a := by
  ext i j
  rw [diagFlow_apply, diagFlow_apply]
  have hlog : ∀ j, Real.log (c * w j) = Real.log c + Real.log (w j) :=
    fun j => Real.log_mul (ne_of_gt hc) (ne_of_gt (hw j))
  have e1 : cpowI (c * w i) s
      = cpowI c s * cpowI (w i) s := by
    unfold cpowI
    rw [hlog i, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : cpowI (c * w j) (-s)
      = cpowI c (-s) * cpowI (w j) (-s) := by
    unfold cpowI
    rw [hlog j, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hne : cpowI c s ≠ 0 := by
    unfold cpowI
    exact Complex.exp_ne_zero _
  rw [e1, e2, cpowI_neg,
    show cpowI c s * cpowI (w i) s * a i j * ((cpowI c s)⁻¹ * cpowI (w j) (-s))
      = (cpowI c s * (cpowI c s)⁻¹)
        * (cpowI (w i) s * a i j * cpowI (w j) (-s)) from by ring,
    mul_inv_cancel₀ hne, one_mul]

/-- The clock's phase factors have unit modulus (Tier T1 — proved):
    the hands of the clock move on the unit circle. The modulus identity
    is unconditional — `Real.log` is real-valued for every real w; it is
    faithfulness (0 < w, part of `ThermalClock`) that makes `Real.log w`
    the true logarithm of the weight, i.e. that makes `cpowI w s` the
    phase of ρ^{is} rather than of |w|^{is}. -/
theorem cpowI_norm (w : ℝ) (s : ℝ) :
    ‖cpowI w s‖ = 1 := by
  have h : cpowI w s = Complex.exp (((s * Real.log w : ℝ) : ℂ) * Complex.I) := by
    unfold cpowI
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The abstract `ModularData` group law, restated as clock additivity
    (Tier T1 — transport of `ModularData.flow_add`): an abstract modular
    clock's thermal time also composes additively. -/
theorem ModularData.flow_additive (M : ModularData) (s t : ℝ)
    (A : Matrix I32 I32 ℂ) :
    M.flow (s + t) A = M.flow s (M.flow t A) :=
  M.flow_add s t A

-- ============================================================================
-- §3. The matrix picture: modular flow generated by a Hamiltonian
-- ============================================================================

/-- The modular flow generated by a matrix Hamiltonian K, in the matrix
    (non-eigenbasis) picture: σ_s(B) = e^{isK} B e^{−isK}. This is the
    real-time flow whose imaginary-time value at s = iβ is
    `modularFlowImag` of `KMSBridge`. Tier T2. -/
noncomputable def modularFlow {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (s : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((Complex.I * (s : ℂ)) • K) * B
    * NormedSpace.exp ((-(Complex.I * (s : ℂ))) • K)

/-- The matrix flow at time 0 is the identity (Tier T1 — proved). -/
theorem modularFlow_zero {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) : modularFlow K 0 B = B := by
  unfold modularFlow
  simp

/-- **Clock additivity, matrix form** (Tier T1 — proved): the matrix
    modular flow is a one-parameter group,
    σ_{s+t} = σ_s ∘ σ_t. -/
theorem modularFlow_add {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (s t : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow K (s + t) B = modularFlow K s (modularFlow K t B) := by
  have hsplit : ∀ c d : ℂ,
      NormedSpace.exp ((c + d) • K)
        = NormedSpace.exp (c • K) * NormedSpace.exp (d • K) := by
    intro c d
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (commute_smul_K K c d)
  have hcast : (Complex.I * (((s + t : ℝ)) : ℂ))
      = Complex.I * (s : ℂ) + Complex.I * (t : ℂ) := by push_cast; ring
  have hcast' : (-(Complex.I * (s : ℂ) + Complex.I * (t : ℂ)))
      = (-(Complex.I * (t : ℂ))) + (-(Complex.I * (s : ℂ))) := by ring
  unfold modularFlow
  rw [hcast, hsplit, hcast', hsplit]
  simp only [mul_assoc]

-- ============================================================================
-- §4. The Gibbs clock and the conversion theorem (Deliverable 3)
-- ============================================================================

/-- A **Gibbs clock**: the clock of the Gibbs state ρ_{β,K} = e^{−βK}/Z
    at inverse temperature β for a laboratory Hamiltonian K. The package
    carries exactly what the formalism carries: the Hamiltonian, its
    Hermiticity, and the temperature field β (the exchange rate).
    The state's own modular Hamiltonian is −ln ρ_{β,K} = β·K + (ln Z)·I;
    the scalar part is invisible to the flow (in the eigenbasis picture
    this cancellation is `modularEigenvalue_diff`; in this picture the
    conversion theorem below is stated for the generator β·K exactly).
    Tier T2. -/
structure GibbsClock (N : ℕ) where
  /-- The laboratory Hamiltonian. -/
  K : Matrix (Fin N) (Fin N) ℂ
  /-- K is Hermitian — an observable. -/
  K_hermitian : K.IsHermitian
  /-- Inverse temperature β — the exchange rate between thermal and
      physical time. -/
  beta : ℝ
  /-- β > 0: a genuine (positive-temperature) Gibbs state. -/
  beta_pos : 0 < beta

/-- The Gibbs clock's state: ρ_{β,K} = e^{−βK}/Z (`gibbsState`).
    Derived, Tier T2. -/
noncomputable def GibbsClock.state {N : ℕ} (G : GibbsClock N) :
    Matrix (Fin N) (Fin N) ℂ :=
  gibbsState G.K G.beta

/-- The Gibbs clock's generator: β·K, the non-scalar part of −ln ρ.
    Derived, Tier T2. -/
noncomputable def GibbsClock.generator {N : ℕ} (G : GibbsClock N) :
    Matrix (Fin N) (Fin N) ℂ :=
  (G.beta : ℂ) • G.K

/-- The Gibbs clock's flow at thermal time s: the modular flow of its
    own state, generated by β·K. Derived, Tier T2. -/
noncomputable def GibbsClock.flow {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  modularFlow G.generator s B

/-- **Clock additivity for a Gibbs clock** (Tier T1 — proved):
    thermal time composes additively on the Gibbs clock too. -/
theorem GibbsClock.flow_add {N : ℕ} (G : GibbsClock N) (s t : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    G.flow (s + t) B = G.flow s (G.flow t B) :=
  modularFlow_add G.generator s t B

/-- **THE CONVERSION THEOREM, matrix form** (Tier T1 — proved).
    Flowing with the Gibbs state's own generator β·K for thermal time s
    is flowing with the laboratory Hamiltonian K for physical time β·s:

        physical time = β × thermal time.

    The rate β is constant — independent of s and of the observable —
    so the Gibbs clock ticks *uniformly* relative to the laboratory
    clock, at exchange rate β. (At β = 1 the two clocks coincide.) -/
theorem gibbs_conversion {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) (s : ℝ) (B : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow ((β : ℂ) • K) s B = modularFlow K (β * s) B := by
  have e1 : (Complex.I * (s : ℂ)) • ((β : ℂ) • K)
      = (Complex.I * (((β * s : ℝ)) : ℂ)) • K := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  have e2 : (-(Complex.I * (s : ℂ))) • ((β : ℂ) • K)
      = (-(Complex.I * (((β * s : ℝ)) : ℂ))) • K := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  unfold modularFlow
  rw [e1, e2]

/-- **The conversion theorem for a `GibbsClock`** (Tier T1 — proved):
    the Gibbs clock's own flow at thermal time s is the laboratory flow
    of K at physical time β·s. -/
theorem GibbsClock.conversion {N : ℕ} (G : GibbsClock N) (s : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    G.flow s B = modularFlow G.K (G.beta * s) B :=
  gibbs_conversion G.K G.beta s B

/-- The Gibbs clock satisfies the KMS condition at its own β
    (Tier T1 — transport of `gibbs_kms`): the Gibbs state is the
    equilibrium state of its own clock. -/
theorem GibbsClock.kms {N : ℕ} (G : GibbsClock N) :
    KMSCondition G.state G.K G.beta :=
  gibbs_kms G.K G.beta

/-- The Gibbs weight is stationary under the laboratory flow
    (Tier T1 — transport of `gibbsWeight_stationary`): the equilibrium
    weight does not move under the physical dynamics it generates. -/
theorem GibbsClock.weight_stationary {N : ℕ} (G : GibbsClock N) (s : ℝ) :
    modularFlow G.K s (gibbsWeight G.K G.beta) = gibbsWeight G.K G.beta :=
  gibbsWeight_stationary G.K G.beta s

-- ============================================================================
-- §5. The conversion in the eigenbasis picture (Deliverable 3, cont.)
-- ============================================================================

/-- Gibbs weights in the eigenbasis: for a Dirac operator with eigenvalues
    λ_j at inverse temperature β, the Gibbs state ρ = e^{−βD²}/Z has
    weights w_j = exp(−(βλ_j² + logZ)) — the exponential of minus the
    modular eigenvalue (`modularEigenvalue`). Tier T2. -/
noncomputable def gibbsDiagWeights {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) : Fin N → ℝ :=
  fun j => Real.exp (-(modularEigenvalue β (lam j) logZ))

/-- Gibbs weights are faithful (Tier T1 — proved): every weight is
    strictly positive, so a Gibbs state always carries an honest thermal
    clock — faithfulness is automatic, not an extra hypothesis. -/
theorem gibbsDiagWeights_pos {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) (j : Fin N) : 0 < gibbsDiagWeights β lam logZ j :=
  Real.exp_pos _

/-- The log of a Gibbs weight is minus the modular eigenvalue
    (Tier T1 — proved): log w_j = −(βλ_j² + logZ), i.e. the clock
    generator's eigenvalue is K_j = βλ_j² + logZ. -/
theorem gibbsDiagWeights_log {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) (j : Fin N) :
    Real.log (gibbsDiagWeights β lam logZ j)
      = -(modularEigenvalue β (lam j) logZ) := by
  simp [gibbsDiagWeights, Real.log_exp]

/-- **The conversion, eigenvalue form** (Tier T1 — proved): the Gibbs
    clock's generator level-spacings are exactly β times the laboratory
    Hamiltonian's (D²) level-spacings,
    K_i − K_j = β·(λ_i² − λ_j²).
    The partition-function constant logZ cancels — this is precisely the
    corpus anchor `modularEigenvalue_diff`, restated as the clock's
    exchange rate. -/
theorem gibbs_K_eigenvalue_diff {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) (i j : Fin N) :
    (-Real.log (gibbsDiagWeights β lam logZ i))
      - (-Real.log (gibbsDiagWeights β lam logZ j))
      = β * (lam i ^ 2 - lam j ^ 2) := by
  simp only [gibbsDiagWeights_log, neg_neg]
  exact modularEigenvalue_diff β (lam i) (lam j) logZ

/-- The laboratory (physical-time) flow of a diagonal Hamiltonian with
    energy levels E, in the eigenbasis: conjugation by e^{−itE}.
    Tier T2. -/
noncomputable def hamiltonianFlow {N : ℕ} (E : Fin N → ℝ) (t : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun j => Complex.exp (-(Complex.I * (t : ℂ) * (E j : ℂ))))
    * a
    * diagonal (fun j => Complex.exp (Complex.I * (t : ℂ) * (E j : ℂ)))

/-- Entry formula for the laboratory flow (Tier T1 — proved). -/
theorem hamiltonianFlow_apply {N : ℕ} (E : Fin N → ℝ) (t : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    hamiltonianFlow E t a i j
      = Complex.exp (-(Complex.I * (t : ℂ) * (E i : ℂ))) * a i j
        * Complex.exp (Complex.I * (t : ℂ) * (E j : ℂ)) := by
  unfold hamiltonianFlow
  rw [mul_diagonal, diagonal_mul]

/-- **THE CONVERSION THEOREM, eigenbasis form** (Tier T1 — proved):
    the Gibbs state's thermal flow at thermal time s *is* the laboratory
    flow of D² at physical time β·s,

        diagFlow (Gibbs weights) s = hamiltonianFlow (λ²) (β·s).

    Together with `gibbs_conversion` (the same statement in the matrix
    picture) this is the brick's headline: for Gibbs states,
    **physical time = β × thermal time**, with the uniform rate β. -/
theorem diagFlow_gibbs_eq_hamiltonianFlow {N : ℕ} (β : ℝ)
    (lam : Fin N → ℝ) (logZ : ℝ) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (gibbsDiagWeights β lam logZ) s a
      = hamiltonianFlow (fun j => lam j ^ 2) (β * s) a := by
  ext i j
  rw [diagFlow_apply, hamiltonianFlow_apply]
  have hprod : cpowI (gibbsDiagWeights β lam logZ i) s
        * cpowI (gibbsDiagWeights β lam logZ j) (-s)
      = Complex.exp (-(Complex.I * (((β * s : ℝ)) : ℂ)
          * (((lam i ^ 2 : ℝ)) : ℂ)))
        * Complex.exp (Complex.I * (((β * s : ℝ)) : ℂ)
          * (((lam j ^ 2 : ℝ)) : ℂ)) := by
    unfold cpowI
    rw [gibbsDiagWeights_log, gibbsDiagWeights_log,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold modularEigenvalue
    push_cast
    ring
  rw [show cpowI (gibbsDiagWeights β lam logZ i) s * a i j
        * cpowI (gibbsDiagWeights β lam logZ j) (-s)
      = (cpowI (gibbsDiagWeights β lam logZ i) s
        * cpowI (gibbsDiagWeights β lam logZ j) (-s)) * a i j from by ring,
    hprod]
  ring

/-- The Gibbs clock does not depend on the partition-function convention
    (Tier T1 — proved): shifting logZ rescales all weights by one
    positive constant, and rescaling weights does not change the flow
    (`diagFlow_scale_weights`). The clock reads the *ratios* of weights,
    never their normalization. -/
theorem diagFlow_gibbs_logZ_independent {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ logZ' : ℝ) (s : ℝ) (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (gibbsDiagWeights β lam logZ') s a
      = diagFlow (gibbsDiagWeights β lam logZ) s a := by
  have hscale : (fun j => Real.exp (logZ - logZ') * gibbsDiagWeights β lam logZ j)
      = gibbsDiagWeights β lam logZ' := by
    funext j
    simp only [gibbsDiagWeights]
    rw [← Real.exp_add]
    congr 1
    unfold modularEigenvalue
    ring
  rw [← hscale]
  exact diagFlow_scale_weights _ (Real.exp_pos _)
    (fun j => gibbsDiagWeights_pos β lam logZ j) s a

-- ============================================================================
-- §6. The stopped clock: thermal vanishing (Deliverable 4)
-- ============================================================================

/-- **A stopped clock, commuting case** (Tier T1 — transport of
    `diagFlow_trivial_of_commute`): an observable that commutes with the
    clock's state does not move under the clock, at any thermal time.
    Where the state and the observable commute, the clock's hands pass
    and nothing happens. -/
theorem ThermalClock.flow_fixes_of_commute {N : ℕ} (C : ThermalClock N)
    (s : ℝ) (a : Matrix (Fin N) (Fin N) ℂ)
    (hcomm : C.state * a = a * C.state) :
    C.flow s a = a :=
  diagFlow_trivial_of_commute C.weights s a hcomm

/-- **A stopped clock, constant-weight case** (Tier T1 — transport of
    `diagFlow_trivial_of_const`): a clock whose weights are all equal has
    trivial flow — thermal time passes and nothing moves, for every
    observable at every time. -/
theorem ThermalClock.stopped_of_const_weights {N : ℕ} (C : ThermalClock N)
    {c : ℝ} (hc : C.weights = fun _ => c) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    C.flow s a = a := by
  rw [ThermalClock.flow, hc]
  exact diagFlow_trivial_of_const c s a

/-- The maximally mixed clock: the clock of the tracial state
    ρ = I/N — the state of maximal ignorance, all weights 1/N.
    Tier T2. -/
noncomputable def maximallyMixedClock (N : ℕ) [NeZero N] : ThermalClock N where
  weights := fun _ => 1 / (N : ℝ)
  faithful := by
    intro _
    exact one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  normalized := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel
      (ne_of_gt (Nat.cast_pos.mpr (NeZero.pos N)))

/-- **THE STOPPED CLOCK** (Tier T1 — transport of
    `maximallyMixed_flow_trivial`): the thermal clock of the tracial /
    maximally mixed state is stopped. Thermal time flows; nothing moves.
    This is the H21 caution as a theorem: tracial states are thermally
    inert, and that is a proved case about the clock — a deliverable,
    not an embarrassment. A thermal clock needs a *non-central* state
    the way a travel clock needs a journey: at maximal ignorance there
    is no journey and no time. -/
theorem maximallyMixedClock_stopped (N : ℕ) [NeZero N] (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    (maximallyMixedClock N).flow s a = a :=
  maximallyMixed_flow_trivial s a

/-- **Equilibrium carries no flux** (Tier T1 — transport of
    `thermal_flux_vanishes`): for the thermal generator K = β·D², the
    modular flux on D vanishes identically. In clock language: at
    equilibrium the clock's hands exert no force — the state that the
    Gibbs clock describes is the flux-stationary state (cf.
    `GibbsClock.kms`: the same state's KMS equilibrium). -/
theorem gibbs_flux_vanishing {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (β : ℝ) :
    modularFlux ((β : ℂ) • D ^ 2) D = 0 :=
  thermal_flux_vanishes D β

-- ============================================================================
-- §7. The scalar-shift lemma, matrix level (housekeeping brick, 2026-10-18)
-- ============================================================================

/-- **Scalar shifts are invisible to the commutator** (Tier T1 — proved):
    for every generator K, observable A, and scalar c,
    `[K + c • I, A] = [K, A]`. The scalar part of a generator commutes
    with everything, so it drops out of every commutator — in
    particular out of the modular flux. This is the algebraic heart of
    the matrix-level scalar-shift lemma (the named leftover of
    `whitepaper/thermal-clock-2026-10-17.md` §4). -/
theorem commutator_add_smul_one {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ)
    (c : ℂ) :
    (K + c • 1) * A - A * (K + c • 1) = K * A - A * K := by
  have h1 : (c • (1 : Matrix (Fin N) (Fin N) ℂ)) * A = c • A := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  have h2 : A * (c • (1 : Matrix (Fin N) (Fin N) ℂ)) = c • A := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [add_mul, mul_add, h1, h2, add_sub_add_comm, sub_self, add_zero]

/-- **Scalar shifts are invisible to the modular flux** (Tier T1 —
    proved): `modularFlux (K + c • I) D = modularFlux K D`, since the
    flux is `I • [K, D]` and the commutator does not see the shift. -/
theorem modularFlux_add_smul_one {N : ℕ} (K D : Matrix (Fin N) (Fin N) ℂ)
    (c : ℂ) :
    modularFlux (K + c • 1) D = modularFlux K D := by
  unfold modularFlux
  rw [commutator_add_smul_one]

/-- **THE SCALAR-SHIFT LEMMA, matrix level** (Tier T1 — proved): adding
    a scalar multiple of the identity to the generator does not change
    the modular flow: `modularFlow (K + c • I) s = modularFlow K s` for
    every time s and every observable. Route (as priced in the
    dossier): the exponential of the shifted generator splits by
    `Matrix.exp_add_of_commute` into the exponential of the unshifted
    generator times a scalar exponential, and the two scalar factors
    cancel in the conjugation. This is the standalone matrix-level
    statement whose eigenbasis shadow is `gibbs_K_eigenvalue_diff` /
    `diagFlow_gibbs_logZ_independent`. -/
theorem modularFlow_add_smul_one {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (c : ℂ) (s : ℝ) (B : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow (K + c • 1) s B = modularFlow K s B := by
  have hPi : ∀ a : ℂ, NormedSpace.exp (fun _ : Fin N => a)
      = fun _ => NormedSpace.exp a := by
    intro a
    funext i
    have h1 : ∀ x : Fin N → ℂ, (NormedSpace.exp x) i
        = ∑' (n : ℕ), ((Nat.factorial n : ℂ))⁻¹ • (x ^ n) i := by
      intro x
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := Fin N → ℂ)]
      exact Pi.tsum_apply (NormedSpace.expSeries_summable' x)
    rw [h1]
    simp only [Pi.pow_apply]
    exact (congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := ℂ)) a).symm
  have hscalar : ∀ a : ℂ,
      NormedSpace.exp (a • (1 : Matrix (Fin N) (Fin N) ℂ))
        = (NormedSpace.exp a) • 1 := by
    intro a
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, hPi,
      ← Matrix.smul_one_eq_diagonal]
  have hexp : ∀ z : ℂ, NormedSpace.exp (z • (K + c • 1))
      = (NormedSpace.exp (z * c)) • NormedSpace.exp (z • K) := by
    intro z
    have h1 : z • (K + c • 1)
        = z • K + (z * c) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      rw [smul_add, smul_smul]
    have hcomm : Commute (z • K)
        ((z * c) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      ((Commute.one_right K).smul_left z).smul_right (z * c)
    rw [h1, Matrix.exp_add_of_commute _ _ hcomm, hscalar, Matrix.mul_smul,
      Matrix.mul_one]
  have hprod : NormedSpace.exp ((-(Complex.I * (s : ℂ))) * c)
      * NormedSpace.exp ((Complex.I * (s : ℂ)) * c) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.all _ _), neg_mul,
      neg_add_cancel, NormedSpace.exp_zero]
  unfold modularFlow
  rw [hexp, hexp, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, hprod, one_smul]

/-- **The conversion theorem with the full Gibbs generator**
    (Tier T1 — proved): the Gibbs state's own modular Hamiltonian is
    `−ln ρ_{β,K} = β • K + (ln Z) • I` (see the `GibbsClock`
    docstring); by the scalar-shift lemma its scalar part is
    invisible, so the conversion `gibbs_conversion` holds for the
    FULL generator, not only for its non-scalar part β • K:
    flowing with `β • K + logZ • I` for thermal time s is flowing
    with the laboratory Hamiltonian K for physical time β·s. -/
theorem gibbs_conversion_full_generator {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (β : ℝ) (logZ : ℂ) (s : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow ((β : ℂ) • K + logZ • 1) s B
      = modularFlow K (β * s) B := by
  rw [modularFlow_add_smul_one]
  exact gibbs_conversion K β s B

end ThetLogos
