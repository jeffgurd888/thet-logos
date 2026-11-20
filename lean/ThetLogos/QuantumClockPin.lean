import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import ThetLogos.ThermalClock
import ThetLogos.GibbsSpan
import ThetLogos.ModularTime
import ThetLogos.PartnerThermal
import ThetLogos.ResonanceTransport
import ThetLogos.AqftKmsGibbs
import ThetLogos.FlowKernel

open Matrix NormedSpace

namespace ThetLogos

/-!
# ThetLogos.QuantumClockPin — the finite quantum clock: tick spectrum,
ticking dichotomy, state-first form (lane grade, 2026-11-19)

Scope of record: `your_files/quantum-clock-pin-scope-2026-11-19.md`.
The corpus already owns the finite thermal clock itself
(`ThermalClock.modularFlow` and its group law, the packaged
`GibbsClock`, `ThermalTimeBridge`, the eigen-action
`hamiltonianFlow_apply` / `GibbsSpan.gibbs_flow_eigenbasis`, the finite
KMS identity three times over). This pin is only the delta the scope
priced, in the scope's firing order:

* **QC-2** — the *named* tick spectrum: the finset of gap frequencies
  `β(E j − E k)` of a Hermitian generator's Gibbs flow, with its
  entrywise phase characterization, `0` always present, negation
  symmetry.
* **QC-3** — the ticking dichotomy: on the full matrix algebra the
  Gibbs flow is the identity at all times iff the generator is scalar
  or `β = 0` (the stopped cases are the corpus's own theorems:
  scalar state, commutant restriction, `β = 0`).
* **QC-1** — the state-first clock: a faithful density's own spectral
  powers `ρ^(it)` and modular Hamiltonian `K_ρ = −ln ρ`, identified
  with the owned generator-first `modularFlow`.

FENCES (on the face, per the scope): this pin proves finite algebraic
identities about a finite state's flow. It is NOT evidence that
physical time is thermal (the Connes–Rovelli hypothesis stays T5
literature, cited as such), it does not quantize or upgrade the
LogicLock calendar (a T5 design study; a different object sharing a
word), and it moves no dial — pre-registered DIAL-INELIGIBLE.
NO CLAIM; dials 0/4.
-/

/-! ## QC-2 — the tick spectrum -/

/-- **The tick spectrum** of an energy profile `E` at inverse
temperature `β`: the finset of gap frequencies `β * (E j − E k)` over
all index pairs. Until this brick the corpus owned the phase action
of the Gibbs flow entrywise (`hamiltonianFlow_apply`,
`GibbsSpan.gibbs_flow_eigenbasis`) but never named the set of
frequencies a finite thermal clock can tick at. Defined over the
eigenvalue function, so it instantiates at `hH.eigenvalues` for a
Hermitian generator `H` (the scope's `E = hH.eigenvalues`). -/
noncomputable def tickSpectrum {N : ℕ} (E : Fin N → ℝ) (β : ℝ) :
    Finset ℝ :=
  (Finset.univ : Finset (Fin N × Fin N)).image
    (fun p => β * (E p.1 - E p.2))

/-- Membership in the tick spectrum is the existence of a gap
realizing the frequency. -/
theorem mem_tickSpectrum {N : ℕ} (E : Fin N → ℝ) (β : ℝ) (ω : ℝ) :
    ω ∈ tickSpectrum E β ↔ ∃ j k : Fin N, ω = β * (E j - E k) := by
  simp only [tickSpectrum, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨j, k, h⟩
    exact ⟨j, k, h.symm⟩
  · rintro ⟨j, k, h⟩
    exact ⟨j, k, h.symm⟩

/-- `0` is always a tick frequency (any diagonal pair `j = k`): the
state's own stationarity, read spectrally. -/
theorem tickSpectrum_zero_mem {N : ℕ} [Nonempty (Fin N)]
    (E : Fin N → ℝ) (β : ℝ) : 0 ∈ tickSpectrum E β := by
  obtain ⟨j⟩ := ‹Nonempty (Fin N)›
  rw [mem_tickSpectrum]
  exact ⟨j, j, by simp⟩

/-- The tick spectrum is closed under negation (the gap `(j, k)` read
backwards is the gap `(k, j)`). -/
theorem neg_mem_tickSpectrum {N : ℕ} (E : Fin N → ℝ) (β : ℝ) {ω : ℝ}
    (hω : ω ∈ tickSpectrum E β) : -ω ∈ tickSpectrum E β := by
  rw [mem_tickSpectrum] at hω ⊢
  obtain ⟨j, k, rfl⟩ := hω
  exact ⟨k, j, by ring⟩

/-- **The phase characterization of the tick spectrum** (the scope's
`tickSpectrum_eq`, stated in the entrywise form the corpus owns):
pulled back into the eigenbasis of a Hermitian `H`, the `(j, k)`
entry of the Gibbs flow `modularFlow ((β:ℂ) • H)` is the entry of
`A` times a pure phase at the tick frequency
`ω = β * (E j − E k) ∈ tickSpectrum hH.eigenvalues β` — the phase is
`exp (i · ω · t)`, the orientation fixed by the corpus's dictionary
(`GibbsSpan.gibbs_flow_eigenbasis`: the matrix picture conjugates by
`exp (+itK)`). So the frequencies at which entries of the flow
rotate are exactly the tick spectrum: every entry rotates at a
frequency in the finset, and every member of the finset occurs at
its own matrix-unit entry (QC-3 exhibits the nontrivial ones). -/
theorem tickSpectrum_eq {N : ℕ} [NeZero N]
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (β t : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (j k : Fin N) :
    (star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * modularFlow ((β : ℂ) • H) t A
        * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) j k
      = Complex.exp (Complex.I
          * ((β * (hH.eigenvalues j - hH.eigenvalues k) * t : ℝ) : ℂ))
        * (star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
            * A
            * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) j k := by
  have h0 : (β : ℂ) • H
      = (β : ℂ) • H + (0 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    simp
  rw [h0, GibbsSpan.gibbs_flow_eigenbasis hH β (0 : ℂ) t A,
    hamiltonianFlow_apply]
  have h3 : -(Complex.I * ((-(β * t) : ℝ) : ℂ)
        * ((hH.eigenvalues j : ℂ)))
      + Complex.I * ((-(β * t) : ℝ) : ℂ)
        * ((hH.eigenvalues k : ℂ))
      = Complex.I
        * ((β * (hH.eigenvalues j - hH.eigenvalues k) * t : ℝ) : ℂ) := by
    push_cast
    ring
  have h4 : Complex.exp (-(Complex.I * ((-(β * t) : ℝ) : ℂ)
        * ((hH.eigenvalues j : ℂ))))
      * Complex.exp (Complex.I * ((-(β * t) : ℝ) : ℂ)
        * ((hH.eigenvalues k : ℂ)))
      = Complex.exp (Complex.I
          * ((β * (hH.eigenvalues j - hH.eigenvalues k) * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, h3]
  linear_combination h4
    * (star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * A
        * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) j k

/-! ## QC-3 — the clock ticks (drafted 2026-11-19, awaiting build slot)

Append before `end ThetLogos`. Depends on QC-2 (`tickSpectrum_eq`).
Strike-check: `exists_flow_ne` / `flow_eq_id_iff` — no existence or
iff form of nontriviality exists on the shelf (ModularTime owns only
the stopped direction); survives K-QC-DUPLICATE. -/

/-- A Hermitian matrix that is not a scalar multiple of the identity
has two distinct eigenvalues. (Contrapositive of the spectral form:
constant eigenvalues collapse `H` to a scalar matrix.) -/
theorem exists_eigenvalue_ne_of_not_smul_one {N : ℕ} [NeZero N]
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hHns : ¬ ∃ c : ℂ, H = c • (1 : Matrix (Fin N) (Fin N) ℂ)) :
    ∃ j k : Fin N, hH.eigenvalues j ≠ hH.eigenvalues k := by
  by_contra hcon
  push_neg at hcon
  apply hHns
  refine ⟨((hH.eigenvalues ⟨0, NeZero.pos N⟩ : ℝ) : ℂ), ?_⟩
  have hdiag : (fun j => ((hH.eigenvalues j : ℂ)))
      = (fun _ => ((hH.eigenvalues ⟨0, NeZero.pos N⟩ : ℂ))) := by
    funext j
    exact congrArg (fun r : ℝ => ((r : ℂ))) (hcon j ⟨0, NeZero.pos N⟩)
  calc H = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * Matrix.diagonal (fun j => ((hH.eigenvalues j : ℂ)))
        * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) :=
      hermitian_spectral_form hH
    _ = ((hH.eigenvalues ⟨0, NeZero.pos N⟩ : ℂ))
        • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      rw [hdiag, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul,
        show (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
            * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          = 1 from Unitary.coe_mul_star_self _]

/-- **The clock ticks**: a non-scalar Hermitian generator at
`β ≠ 0` has an observable and a time at which its Gibbs flow moves
the observable — the matrix unit at a nonzero tick frequency
`ω = β * (E j − E k)`, read at `t = π / ω`, where its phase is
`−1 ≠ 1` (via QC-2's `tickSpectrum_eq`). -/
theorem exists_flow_ne {N : ℕ} [NeZero N]
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hHns : ¬ ∃ c : ℂ, H = c • (1 : Matrix (Fin N) (Fin N) ℂ))
    {β : ℝ} (hβ : β ≠ 0) :
    ∃ (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ),
      modularFlow ((β : ℂ) • H) t A ≠ A := by
  obtain ⟨j, k, hjk⟩ := exists_eigenvalue_ne_of_not_smul_one hH hHns
  have hω : β * (hH.eigenvalues j - hH.eigenvalues k) ≠ 0 :=
    mul_ne_zero hβ (sub_ne_zero.mpr hjk)
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * matUnitCoeff j k (1 : ℂ)
      * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ),
    Real.pi / (β * (hH.eigenvalues j - hH.eigenvalues k)), ?_⟩
  intro hcon
  have hU1 : star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hA : star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          * matUnitCoeff j k (1 : ℂ)
          * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
        * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      = matUnitCoeff j k (1 : ℂ) :=
    star_conj_collapse _ _ hU1
  have hentry := congrArg
    (fun M : Matrix (Fin N) (Fin N) ℂ =>
      (star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * M
        * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) j k) hcon
  rw [tickSpectrum_eq hH β _ _ j k, hA] at hentry
  have hunit : matUnitCoeff j k (1 : ℂ) j k = 1 := by
    simp [matUnitCoeff]
  rw [hunit, mul_one] at hentry
  have harg : β * (hH.eigenvalues j - hH.eigenvalues k)
      * (Real.pi / (β * (hH.eigenvalues j - hH.eigenvalues k)))
      = Real.pi := by
    field_simp
  rw [harg] at hentry
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [mul_comm]
    exact Complex.exp_pi_mul_I
  rw [hpi] at hentry
  have hre := congrArg Complex.re hentry
  norm_num at hre

/-- **The ticking dichotomy**: on the full matrix algebra, the Gibbs
flow of a Hermitian `H` at inverse temperature `β` is the identity
at all times iff `H` is scalar or `β = 0`. The stopped direction is
the corpus's own content (scalar generator — `modularFlow` of a
scalar matrix is scalar conjugation; `β = 0` — the generator
vanishes); the ticking direction is `exists_flow_ne`. Together with
`ModularTime`'s stopped-clock theorems (scalar state, commutant
restriction) this closes the iff the scope's triviality trap
demands, in its corrected form. -/
theorem flow_eq_id_iff {N : ℕ} [NeZero N]
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (∀ (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ),
        modularFlow ((β : ℂ) • H) t A = A)
      ↔ (∃ c : ℂ, H = c • (1 : Matrix (Fin N) (Fin N) ℂ)) ∨ β = 0 := by
  constructor
  · intro hall
    by_contra hcon
    have hβ : β ≠ 0 := fun hβ => hcon (Or.inr hβ)
    have hns : ¬ ∃ c : ℂ, H = c • (1 : Matrix (Fin N) (Fin N) ℂ) :=
      fun hc => hcon (Or.inl hc)
    obtain ⟨A, t, hne⟩ := exists_flow_ne hH hns hβ
    exact hne (hall A t)
  · rintro (⟨c, rfl⟩ | rfl)
    · intro A t
      have hgen : (β : ℂ) • (c • (1 : Matrix (Fin N) (Fin N) ℂ))
          = (0 : Matrix (Fin N) (Fin N) ℂ) + ((β : ℂ) * c) • 1 := by
        rw [smul_smul, zero_add]
      rw [hgen, modularFlow_add_smul_one]
      simp [modularFlow]
    · intro A t
      simp [modularFlow]

/-! ## QC-1 — the state-first clock (drafted 2026-11-19, awaiting build slot)

Append before `end ThetLogos`. Depends: census only.
Strike-check record: `stateModularK` / `stateFlow` as objects — the
scope's §0 audit read the whole shelf (ThermalClock, GibbsSpan,
ModularTime, KMSBridge, PartnerThermal, AqftKmsGibbs) and found the
generator-first direction only; the general faithful state's own
`ρ^(it)` exists nowhere as a matrix. Survives K-QC-DUPLICATE.
K-QC-RENAME guard: `stateFlow` is built ONLY from `cpowI` on `ρ`'s
eigenvalues conjugated by `ρ`'s eigenvector unitary; `modularFlow`
is built from `NormedSpace.exp` of a presented generator. The
identification `stateFlow_eq_modularFlow_stateModularK` is proved
through the transport lemma `exp_smul_stateModularK`, not by
unfolding one side into the other.

DISCLOSED NARROWING (for STATUS, full rank): the scope's
`stateFlow_eq_modularFlow` in its literal `gibbsForm H β` form
reduces to `stateModularK (gibbsForm H β) = (β:ℂ) • H + (log Z) • 1`,
whose only missing step is basis-independence of the spectral
logarithm (Mathlib's `eigenvectorUnitary` is a choice; identifying
the spectral log computed in `ρ`'s chosen basis with the one
computed in `H`'s basis is a uniqueness-of-Hermitian-logarithm
lemma, priced L — polynomial interpolation on the finite spectrum).
This brick ships the identification in the modular-Hamiltonian form
(item: `stateFlow_eq_modularFlow_stateModularK`) plus the exact
exp-characterization `exp_neg_stateModularK` and the KMS corollary
the scope priced (`state_kms_own`, by citation of
`gibbsForm_isKMSFlow`). The `H`-form is reported as the brick's
named open residue, NOT silently dropped. -/

/-- **The state's own modular Hamiltonian** `K_ρ = −ln ρ`, built
spectrally from a Hermitian `ρ` alone: conjugate the diagonal of
`−log (eigenvalues ρ)` by `ρ`'s eigenvector unitary. No Hamiltonian
is presented; this is the state-first direction the corpus did not
own. (The bare spectral log needs no faithfulness — `Real.log 0 = 0`
on a dead mode; faithfulness is carried by `stateFlow` and by every
theorem that exponentiates `K_ρ` back to `ρ`, per K-QC-LOG.) -/
noncomputable def stateModularK {N : ℕ} {ρ : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρ.IsHermitian) : Matrix (Fin N) (Fin N) ℂ :=
  (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
    * Matrix.diagonal
      (fun j => ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ))
    * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

/-- **The state-first flow**: conjugation by the state's own
spectral complex powers `ρ^(it)`, in `ModularTime`'s `cpowI`
dialect — `ρ^(it)` is the diagonal of `cpowI (w j) t` in `ρ`'s
eigenbasis, conjugated out. No matrix exponential is introduced.
Faithfulness (`∀ j, 0 < eigenvalues j`) is a hypothesis on the
definition's face (K-QC-LOG): at `w = 0`, `cpowI` silently returns
phase `1` by the `log 0 = 0` convention, and the flow is not
stated for such a `ρ`. -/
noncomputable def stateFlow {N : ℕ} {ρ : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρ.IsHermitian) (hpos : ∀ j, 0 < hρ.eigenvalues j) (t : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
    * Matrix.diagonal (fun j => cpowI (hρ.eigenvalues j) t)
    * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
  * A
  * ((hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
    * Matrix.diagonal (fun j => cpowI (hρ.eigenvalues j) (-t))
    * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))

/-- The modular Hamiltonian of a state is Hermitian (a real diagonal
conjugated by a unitary). -/
theorem stateModularK_isHermitian {N : ℕ}
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian) :
    (stateModularK hρ).IsHermitian := by
  have hD : star (Matrix.diagonal
        (fun j => ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
      = Matrix.diagonal
        (fun j => ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.star_apply, Matrix.diagonal_apply_eq,
        Complex.star_def, Complex.conj_ofReal]
    · simp [Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
  unfold stateModularK Matrix.IsHermitian
  rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul,
    star_star, hD]
  simp only [Matrix.mul_assoc]

/-- **Transport for the state's own generator**: the exponential of
a scalar multiple of `K_ρ`, in `ρ`'s own eigenbasis. Proved in this
basis directly (the pattern of `exp_smul_conj_diag`, but with the
unitary of `stateModularK`'s definition — `exp_smul_conj_diag`
itself is stated for the chosen unitary of the matrix it is applied
to, which for `K_ρ` is a different choice; this lemma is the
same-basis computation the identification needs). -/
theorem exp_smul_stateModularK {N : ℕ}
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian) (z : ℂ) :
    NormedSpace.exp (z • stateModularK hρ)
      = (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * Matrix.diagonal (fun j => Complex.exp
          (z * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
        * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
  have hU1 : star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hsmul : z • stateModularK hρ
      = (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * (z • Matrix.diagonal
          (fun j => ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
        * star (hρ.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    unfold stateModularK
    rw [mul_smul_comm, smul_mul_assoc]
  have hdiag : z • Matrix.diagonal
        (fun j => ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ))
      = Matrix.diagonal (fun j => z
        * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.diagonal_apply, h, Matrix.smul_apply, smul_eq_mul]
  have hfun : NormedSpace.exp (fun j => z
        * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ))
      = (fun j => Complex.exp (z
        * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ))) := by
    funext j
    rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]
  rw [hsmul, exp_conj_star _ _ hU1 hU2, hdiag, Matrix.exp_diagonal,
    hfun]

/-- **The identification** (state-first = generator-first, at the
state's own modular Hamiltonian): the state-first flow of a
faithful `ρ` at time `t` is the owned `modularFlow` of
`K_ρ = −ln ρ` at time `−t` — the orientation of the corpus's
dictionary (`modularFlow K s` conjugates by `exp (+isK)`, and
`exp (−itK_ρ) = ρ^(it)`). A theorem, not a definition: the two
sides are built from `cpowI` spectral powers and from
`NormedSpace.exp` respectively, and meet through
`exp_smul_stateModularK` (K-QC-RENAME respected). -/
theorem stateFlow_eq_modularFlow_stateModularK {N : ℕ}
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian)
    (hpos : ∀ j, 0 < hρ.eigenvalues j) (t : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    stateFlow hρ hpos t A
      = modularFlow (stateModularK hρ) (-t) A := by
  have hd1 : Matrix.diagonal (fun j => Complex.exp
        ((Complex.I * ((-t : ℝ) : ℂ))
          * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
      = Matrix.diagonal (fun j => cpowI (hρ.eigenvalues j) t) := by
    congr 1
    funext j
    unfold cpowI
    congr 1
    push_cast
    ring
  have hd2 : Matrix.diagonal (fun j => Complex.exp
        ((-(Complex.I * ((-t : ℝ) : ℂ)))
          * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
      = Matrix.diagonal (fun j => cpowI (hρ.eigenvalues j) (-t)) := by
    congr 1
    funext j
    unfold cpowI
    congr 1
    push_cast
    ring
  unfold modularFlow stateFlow
  rw [exp_smul_stateModularK hρ, exp_smul_stateModularK hρ, hd1, hd2]

/-- **The state is the Gibbs state of its own modular
Hamiltonian**: `exp (−K_ρ) = ρ` for a faithful `ρ` — the exact
characterization from which the KMS corollary is cited. (This is
where faithfulness is spent: `Real.exp (Real.log w) = w` needs
`0 < w`.) -/
theorem exp_neg_stateModularK {N : ℕ}
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian)
    (hpos : ∀ j, 0 < hρ.eigenvalues j) :
    NormedSpace.exp (-(stateModularK hρ)) = ρ := by
  have hneg : -(stateModularK hρ) = (-1 : ℂ) • stateModularK hρ := by
    rw [neg_smul, one_smul]
  have hdiag : Matrix.diagonal (fun j => Complex.exp
        ((-1 : ℂ) * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)))
      = Matrix.diagonal (fun j => ((hρ.eigenvalues j : ℂ))) := by
    congr 1
    funext j
    have harg : (-1 : ℂ) * ((-Real.log (hρ.eigenvalues j) : ℝ) : ℂ)
        = ((Real.log (hρ.eigenvalues j) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp, Real.exp_log (hpos j)]
  rw [hneg, exp_smul_stateModularK hρ, hdiag,
    ← hermitian_spectral_form hρ]

/-- `ρ` is the Gibbs form of its own modular Hamiltonian at
`β = 1`: the partition trace is `Tr ρ = 1` by hypothesis, so the
normalization is invisible. -/
theorem gibbsForm_stateModularK {N : ℕ}
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian)
    (hpos : ∀ j, 0 < hρ.eigenvalues j) (htr : Matrix.trace ρ = 1) :
    gibbsForm (stateModularK hρ) 1 = ρ := by
  have h1 : (-((1 : ℝ) : ℂ)) • stateModularK hρ
      = -(stateModularK hρ) := by
    rw [show (-((1 : ℝ) : ℂ)) = (-1 : ℂ) by push_cast; ring,
      neg_smul, one_smul]
  unfold gibbsForm
  rw [h1, exp_neg_stateModularK hρ hpos, htr]
  simp

/-- **A faithful state is KMS at `β = 1` for its own clock**:
cited from the census `gibbsForm_isKMSFlow` through
`gibbsForm_stateModularK` — not re-proved (the finite KMS identity
is owned three times over; K-QC-DUPLICATE respected). The KMS
generator is the state's own `K_ρ`, and by
`stateFlow_eq_modularFlow_stateModularK` its flow is the
state-first flow. -/
theorem state_kms_own {N : ℕ} [NeZero N]
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian)
    (hpos : ∀ j, 0 < hρ.eigenvalues j) (htr : Matrix.trace ρ = 1) :
    IsKMSFlow ρ (stateModularK hρ) 1 := by
  have hne : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (NeZero.pos N)
  have h := gibbsForm_isKMSFlow (stateModularK_isHermitian hρ) (1 : ℝ)
  rwa [gibbsForm_stateModularK hρ hpos htr] at h

end ThetLogos
