/-
# AqftFiniteTT — AQFT-2: the finite Tomita–Takesaki package

**Scope: the AQFT adjacency map
(~/workspace/your_files/aqft-adjacency-scope-2026-11-09.md
§8), fired by Zero; pricing note
~/workspace/your_files/aqft2-pricing-2026-11-14.md.
NO CLAIM. Dial-ineligible.**

THE CAMPAIGN: the finite Tomita–Takesaki package at the
full-matrix seat, in three components — (a) the modular
operator Δ_ρ in tensor (Kronecker) form, with its flow
identified against the corpus's existing
`modularFlow`/`heisenbergFlow` forms; (b) the modular
conjugation J (entrywise conjugation composed with the
adjoint flip, i.e. conjugate transpose — the standard-form
J at the trace seat) and the finite commutant theorem
J M J = M′ with M′ computed as the commutant of the left
multiplications; (c) the triviality statement: the finite
modular group is inner, implemented by ρ^{it} inside the
algebra — the finite flow-of-weights is trivial.

FENCES (the adjacency map's): this is the finite special
case of Tomita–Takesaki theory, NOT the theory;
`KMSBridge.TomitaTakesakiWindow` stays in place for the
infinite statement, untouched. K-AQFT-UPGRADE stays FIRED
(finite bookkeeping, not an ACMD upgrade);
K-AQFT-TYPEIII-FINITE armed (no Type III structure exists
or is claimed at finite seats); K-AQFT2-STATEMENT armed
(any component false as scoped fires it at full rank).

CONVENTIONS (disclosed, per the pricing note §4): Δ_ρ uses
plain `Matrix.inv`, with invertibility carried as explicit
hypotheses; the tensor form is `(ρ⁻¹)ᵀ ⊗ₖ ρ`, forced by
Mathlib's `Matrix.kronecker_mulVec_vec`; flow conventions
are the corpus's own (`modularFlow` = Ad exp(isK),
K = −log ρ), and the identification theorems state exactly
the equalities those conventions force.

STATUS: STATUS-AQFT2.md (per brick).
-/

import Mathlib
import ThetLogos.AqftKmsGibbs
import ThetLogos.FlowKernel
import ThetLogos.GibbsSpan
import ThetLogos.ModularTime
import ThetLogos.ThermalClock

open Matrix NormedSpace

namespace ThetLogos

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## §A1 — the modular operator -/

/-- The modular operator of `ρ`, as an action on the matrix
    space: `Δ_ρ (X) = ρ * X * ρ⁻¹` — the conjugation-sandwich.
    For a faithful state `ρ` this is the finite-dimensional
    modular operator of Tomita–Takesaki theory, acting on the
    algebra in its standard (Hilbert–Schmidt) representation. -/
noncomputable def modularOp (ρ X : Matrix m m ℂ) : Matrix m m ℂ :=
  ρ * X * ρ⁻¹

theorem modularOp_apply (ρ X : Matrix m m ℂ) :
    modularOp ρ X = ρ * X * ρ⁻¹ := rfl

/-- The modular operator in tensor form: the matrix of `Δ_ρ`
    on the matrix space, in the `Matrix.vec` basis. Defined
    entrywise (the direct Kronecker expression mis-elaborates
    against the stated return type in this pin — probe
    R1/R2); the bridge lemma below identifies it with the
    Kronecker product `Matrix.kronecker (ρ⁻¹)ᵀ ρ` — the
    `ρ ⊗ ρ⁻¹` action of the pin. The entry pairing follows
    Mathlib's `vec` index convention, as the bridge lemma's
    entry computation fixes it (probe R4). -/
noncomputable def modularMatrix (ρ : Matrix m m ℂ) :
    Matrix (m × m) (m × m) ℂ :=
  fun (i, j) (k, l) => ρ⁻¹ k i * ρ j l

/-- Entry formula for the tensor form, in the `vec` basis:
    `(Δ_ρ)_{(i,j),(k,l)} = (ρ⁻¹)_{ki} · ρ_{jl}`. -/
theorem modularMatrix_apply (ρ : Matrix m m ℂ) (i j k l : m) :
    modularMatrix ρ (i, j) (k, l) = ρ⁻¹ k i * ρ j l := rfl

/-- The tensor form IS the Kronecker product
    `Matrix.kronecker (ρ⁻¹)ᵀ ρ`. (The `⊗ₖ` notation is
    `scoped[Kronecker]` in this pin and is not opened here;
    the function form is used throughout.) -/
theorem modularMatrix_eq_kronecker (ρ : Matrix m m ℂ) :
    modularMatrix ρ = Matrix.kronecker (ρ⁻¹)ᵀ ρ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [modularMatrix, Matrix.transpose_apply]

/-- The tensor form acts as the sandwich: multiplication by
    `modularMatrix ρ` on vectorized matrices is `Δ_ρ`. -/
theorem modularMatrix_mulVec_vec (ρ X : Matrix m m ℂ) :
    (modularMatrix ρ) *ᵥ Matrix.vec X = Matrix.vec (modularOp ρ X) := by
  have h := Matrix.kronecker_mulVec_vec ρ X (ρ⁻¹)ᵀ
  rw [Matrix.transpose_transpose] at h
  rw [modularMatrix_eq_kronecker, modularOp_apply]
  exact h

/-- `Δ_ρ` fixes the identity when `ρ` is invertible. -/
theorem modularOp_one (ρ : Matrix m m ℂ) (hρ : ρ * ρ⁻¹ = 1) :
    modularOp ρ 1 = 1 := by
  rw [modularOp_apply, Matrix.mul_one]
  exact hρ

/-- `Δ_ρ` is multiplicative when `ρ` is invertible: the modular
    operator is an algebra automorphism of the matrix space. -/
theorem modularOp_mul (ρ X Y : Matrix m m ℂ) (hρ : ρ⁻¹ * ρ = 1) :
    modularOp ρ (X * Y) = modularOp ρ X * modularOp ρ Y := by
  simp only [modularOp_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ρ⁻¹ ρ (Y * ρ⁻¹), hρ, Matrix.one_mul]

/-! ## §A2 — flow identification at the diagonal seat -/

/-- The modular operator at the diagonal seat acts entrywise
    by the weight ratio:
    `(Δ_{diag(w)} X) i j = (w i / w j) · X i j`. The
    eigenvalues of `Δ` at the diagonal seat are the ratios
    `w i / w j` — the finite shadow of the modular
    spectrum. -/
theorem modularOp_diagState_entry {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) (X : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    modularOp (diagState w) X i j
      = ((w i / w j : ℝ) : ℂ) * X i j := by
  have hinv : (diagState w)⁻¹
      = diagonal (fun j => ((w j : ℂ))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    show diagState w * diagonal (fun j => ((w j : ℂ))⁻¹) = 1
    rw [show diagState w = diagonal (fun j => (w j : ℂ))
        from rfl, Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases h : j = k
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact mul_inv_cancel₀
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (hw j)))
    · simp only [Matrix.diagonal_apply_ne _ h,
        Matrix.one_apply_ne h]
  rw [modularOp_apply, hinv]
  show (diagonal (fun j => (w j : ℂ)) * X
    * diagonal (fun j => ((w j : ℂ))⁻¹)) i j = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Complex.ofReal_div, div_eq_mul_inv]
  ring

/-- The `Δ`-power at the diagonal seat acts entrywise by
    the ratio power: `(σ_s X) i j = (w i / w j)^{is} · X i j`
    — `diagFlow` is `Ad Δ^{is}`, read entrywise. -/
theorem diagFlow_entry_ratio {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) (s : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    diagFlow w s X i j = cpowI (w i / w j) s * X i j := by
  have hdiv : cpowI (w i / w j) s
      = cpowI (w i) s * cpowI (w j) (-s) := by
    unfold cpowI
    rw [Real.log_div (ne_of_gt (hw i)) (ne_of_gt (hw j)),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hdiv]
  show (diagonal (fun j => cpowI (w j) s) * X
    * diagonal (fun j => cpowI (w j) (-s))) i j = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- `diagFlow` is the sandwich by the diagonal unitary of
    the `ρ^{is}` and its inverse: `σ_s (X) = D_s X D_s⁻¹`
    with `D_s = diagonal (w^{is})` — the `Ad Δ^{is}` form
    of the diagonal seat's flow. -/
theorem diagFlow_eq_sandwich_inv {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow w s X = diagonal (fun j => cpowI (w j) s) * X
      * (diagonal (fun j => cpowI (w j) s))⁻¹ := by
  have h : (diagonal (fun j => cpowI (w j) s))⁻¹
      = diagonal (fun j => cpowI (w j) (-s)) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases h : j = k
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [cpowI_neg]
      exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    · simp only [Matrix.diagonal_apply_ne _ h,
        Matrix.one_apply_ne h]
  unfold diagFlow
  rw [h]

/-! ## §A3 — flow identification at the Gibbs seat -/

/-- `Δ` is invariant under rescaling of the state at an
    invertible seat: `Δ_{cρ} = Δ_ρ` for `c ≠ 0`. The
    modular operator sees the ray of the state, not its
    normalization — this is what lets unnormalized Gibbs
    weights carry the same `Δ` as the normalized state.
    (Invertibility in the house form `ρ * ρ⁻¹ = 1`, as
    in `modularOp_one`/`modularOp_mul`; the fully
    general form would need the adjugate computation,
    since `Matrix.inv_smul` requires a unit
    determinant.) -/
theorem modularOp_smul (c : ℂ) (hc : c ≠ 0)
    (ρ : Matrix m m ℂ) (hρ : ρ * ρ⁻¹ = 1)
    (X : Matrix m m ℂ) :
    modularOp (c • ρ) X = modularOp ρ X := by
  have hinv : (c • ρ)⁻¹ = c⁻¹ • ρ⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hρ,
      mul_inv_cancel₀ hc, one_smul]
  rw [modularOp_apply, modularOp_apply, hinv,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- At the Gibbs-weight seat — `c • diag(exp w)` for any
    normalization scalar `c ≠ 0` — the modular operator's
    entries are the exponential ratios:
    `(Δ X) i j = (e^{w i} / e^{w j}) · X i j`. -/
theorem modularOp_gibbsSeat_entry {N : ℕ} (c : ℂ)
    (hc : c ≠ 0) (w : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    modularOp (c • diagState (fun j => Real.exp (w j))) X i j
      = ((Real.exp (w i) / Real.exp (w j) : ℝ) : ℂ)
        * X i j := by
  have hρ : diagState (fun j => Real.exp (w j))
      * (diagState (fun j => Real.exp (w j)))⁻¹ = 1 := by
    have hinv : (diagState (fun j => Real.exp (w j)))⁻¹
        = diagonal (fun j => ((Real.exp (w j) : ℂ))⁻¹) := by
      apply Matrix.inv_eq_right_inv
      show diagState (fun j => Real.exp (w j))
        * diagonal (fun j => ((Real.exp (w j) : ℂ))⁻¹) = 1
      rw [show diagState (fun j => Real.exp (w j))
          = diagonal (fun j => ((Real.exp (w j) : ℝ) : ℂ))
          from rfl, Matrix.diagonal_mul_diagonal]
      ext a b
      by_cases h : a = b
      · subst h
        simp only [Matrix.diagonal_apply_eq,
          Matrix.one_apply_eq]
        exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Real.exp_pos (w a))))
      · simp only [Matrix.diagonal_apply_ne _ h,
          Matrix.one_apply_ne h]
    rw [hinv]
    show diagonal (fun j => ((Real.exp (w j) : ℝ) : ℂ))
      * diagonal (fun j => ((Real.exp (w j) : ℂ))⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.exp_pos (w a))))
    · simp only [Matrix.diagonal_apply_ne _ h,
        Matrix.one_apply_ne h]
  rw [modularOp_smul c hc _ hρ]
  exact modularOp_diagState_entry (fun j => Real.exp (w j))
    (fun j => Real.exp_pos (w j)) X i j

/-- The eigenbasis flow IS the corpus's matrix modular
    flow, generated by the log of the state:
    `diagFlow w s = modularFlow (log ρ_w) s` with
    `log ρ_w = diagonal (log w)`. -/
theorem diagFlow_eq_modularFlow_log {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow w s X = modularFlow
      (diagonal (fun j => (Real.log (w j) : ℂ))) s X := by
  have e1 : NormedSpace.exp ((Complex.I * (s : ℂ))
        • diagonal (fun j => (Real.log (w j) : ℂ)))
      = diagonal (fun j => cpowI (w j) s) := by
    have hsmul : (Complex.I * (s : ℂ))
          • diagonal (fun j => (Real.log (w j) : ℂ))
        = diagonal (fun j => (Complex.I * (s : ℂ))
            * (Real.log (w j) : ℂ)) := by
      ext a b
      simp [Matrix.smul_apply, Matrix.diagonal_apply]
    rw [hsmul, Matrix.exp_diagonal]
    congr 1
    funext j
    simp only [Pi.exp_def]
    unfold cpowI
    rw [← congr_fun Complex.exp_eq_exp_ℂ
      ((Complex.I * (s : ℂ)) * (Real.log (w j) : ℂ))]
  have e2 : NormedSpace.exp ((-(Complex.I * (s : ℂ)))
        • diagonal (fun j => (Real.log (w j) : ℂ)))
      = diagonal (fun j => cpowI (w j) (-s)) := by
    have hsmul : (-(Complex.I * (s : ℂ)))
          • diagonal (fun j => (Real.log (w j) : ℂ))
        = diagonal (fun j => (-(Complex.I * (s : ℂ)))
            * (Real.log (w j) : ℂ)) := by
      ext a b
      simp [Matrix.smul_apply, Matrix.diagonal_apply]
    rw [hsmul, Matrix.exp_diagonal]
    congr 1
    funext j
    simp only [Pi.exp_def]
    unfold cpowI
    rw [← congr_fun Complex.exp_eq_exp_ℂ
      ((-(Complex.I * (s : ℂ))) * (Real.log (w j) : ℂ))]
    congr 1
    push_cast
    ring
  unfold diagFlow modularFlow
  rw [e1, e2]

/-- At the corpus's own Gibbs weights, the diagonal
    modular flow is the Heisenberg flow of the diagonal
    Hamiltonian `diag(λ²)` at time `−β·s`: the finite
    `σ_s = α_{−βs}` identification, through `GibbsSpan`'s
    landed bridge
    `gibbs_modularFlow_eq_heisenbergFlow`. -/
theorem diagFlow_gibbsWeights_eq_heisenbergFlow {N : ℕ}
    (β : ℝ) (lam : Fin N → ℝ) (logZ : ℝ) (s : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (gibbsDiagWeights β lam logZ) s X
      = GibbsSpan.heisenbergFlow
          (diagonal (fun j => ((lam j ^ 2 : ℝ) : ℂ)))
          ((-β) * s) X := by
  have hH : (diagonal (fun j => ((lam j ^ 2 : ℝ) : ℂ))).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro j
    simp [IsSelfAdjoint, Complex.conj_ofReal]
  have hgen : diagonal
        (fun j => (Real.log (gibbsDiagWeights β lam logZ j) : ℂ))
      = ((-β : ℝ) : ℂ)
          • diagonal (fun j => ((lam j ^ 2 : ℝ) : ℂ))
        + (-(logZ : ℂ)) • 1 := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [gibbsDiagWeights, modularEigenvalue,
        Real.log_exp, Matrix.diagonal_apply_eq,
        Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul]
      push_cast
      ring
    · simp [Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply_ne h, h]
  rw [diagFlow_eq_modularFlow_log, hgen]
  exact GibbsSpan.gibbs_modularFlow_eq_heisenbergFlow hH
    (-β) (-(logZ : ℂ)) s X

/-! ## §C — the finite modular group is inner -/

/-- The adjoint of the diagonal `Δ^{is}` is the diagonal
    of the inverse power: `D_sᴴ = D_{−s}` (each
    `cpowI` entry has modulus 1, and
    `star (w^{is}) = w^{−is}`). -/
theorem diagonal_cpowI_conjTranspose {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) :
    (diagonal (fun j => cpowI (w j) s))ᴴ
      = diagonal (fun j => cpowI (w j) (-s)) := by
  have key : ∀ z : ℂ, star (Complex.exp z)
      = Complex.exp (star z) := by
    intro z
    rw [congr_fun Complex.exp_eq_exp_ℂ z,
      NormedSpace.star_exp,
      ← congr_fun Complex.exp_eq_exp_ℂ (star z)]
  have hstar : ∀ (a t : ℝ), star (cpowI a t) = cpowI a (-t) := by
    intro a t
    simp only [cpowI, key, star_mul, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  exact hstar (w j) s

/-- The inverse of the diagonal `Δ^{is}` is the diagonal
    of the inverse power: `D_s⁻¹ = D_{−s}`. -/
theorem diagonal_cpowI_inv {N : ℕ} (w : Fin N → ℝ) (s : ℝ) :
    (diagonal (fun j => cpowI (w j) s))⁻¹
      = diagonal (fun j => cpowI (w j) (-s)) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [cpowI_neg]
    exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
  · simp only [Matrix.diagonal_apply_ne _ h,
      Matrix.one_apply_ne h]

/-- The diagonal `Δ^{is}` is unitary: `D_sᴴ D_s = 1` and
    `D_s D_sᴴ = 1`. -/
theorem diagonal_cpowI_isUnitary {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) :
    (diagonal (fun j => cpowI (w j) s))ᴴ
        * diagonal (fun j => cpowI (w j) s) = 1
      ∧ diagonal (fun j => cpowI (w j) s)
        * (diagonal (fun j => cpowI (w j) s))ᴴ = 1 := by
  rw [diagonal_cpowI_conjTranspose]
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq]
      rw [cpowI_neg]
      exact inv_mul_cancel₀ (Complex.exp_ne_zero _)
    · simp only [Matrix.diagonal_apply_ne _ h,
        Matrix.one_apply_ne h]
  · rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq]
      rw [cpowI_neg]
      exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    · simp only [Matrix.diagonal_apply_ne _ h,
        Matrix.one_apply_ne h]

/-- **The finite modular group is inner at the diagonal
    seat**: `diagFlow w s` is conjugation by the unitary
    `D_s = diagonal (w^{is})` — `σ_s (X) = D_s X D_sᴴ`
    with `D_s` an element of the algebra itself (a
    diagonal matrix). -/
theorem diagFlow_inner {N : ℕ} (w : Fin N → ℝ) (s : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow w s X = diagonal (fun j => cpowI (w j) s) * X
      * (diagonal (fun j => cpowI (w j) s))ᴴ := by
  rw [diagFlow_eq_sandwich_inv, diagonal_cpowI_inv,
    ← diagonal_cpowI_conjTranspose]

/-- Innerness at the corpus's Gibbs weights: the Gibbs
    modular flow is conjugation by the diagonal unitary
    of the Gibbs `ρ^{is}`. -/
theorem gibbsFlow_inner {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) (s : ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (gibbsDiagWeights β lam logZ) s X
      = diagonal
          (fun j => cpowI (gibbsDiagWeights β lam logZ j) s)
        * X
        * (diagonal
            (fun j => cpowI (gibbsDiagWeights β lam logZ j) s))ᴴ :=
  diagFlow_inner _ _ _

/-- **Capstone of §C — the finite flow-of-weights is
    trivial at the diagonal seat.** For every `s`, the
    modular automorphism `σ_s = diagFlow w s` is
    implemented by a unitary `D_s = diagonal (w^{is})`
    lying in the algebra itself (indeed in its diagonal
    subalgebra): `σ_s = Ad D_s`, `D_sᴴ D_s = D_s D_sᴴ
    = 1`. With §A3, the same flow is the corpus's
    `modularFlow` of `log ρ` and, at the Gibbs weights,
    the Heisenberg flow at `−β·s`. This is the finite
    triviality statement of the pin's clause (c); it is
    a statement about finite matrices — no type-III
    content (K-AQFT-TYPEIII-FINITE stays armed). -/
theorem finite_modular_inner {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow w s X = diagonal (fun j => cpowI (w j) s) * X
        * (diagonal (fun j => cpowI (w j) s))ᴴ
      ∧ (diagonal (fun j => cpowI (w j) s))ᴴ
          * diagonal (fun j => cpowI (w j) s) = 1
      ∧ diagonal (fun j => cpowI (w j) s)
          * (diagonal (fun j => cpowI (w j) s))ᴴ = 1 :=
  ⟨diagFlow_inner w s X, diagonal_cpowI_isUnitary w s⟩

/-! ## §B1 — the modular conjugation -/

/-- The modular conjugation at the trace seat:
    `J X = Xᴴ` — entrywise conjugation composed with
    the adjoint flip, exactly the scope's clause (b)
    form. (At the full-matrix seat with the trace
    state, Tomita's `J` is the adjoint itself.) -/
def modConj {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m m ℂ) : Matrix m m ℂ :=
  Xᴴ

/-- `J` is involutive: `J (J X) = X`. -/
theorem modConj_involutive {m : Type*} [Fintype m]
    [DecidableEq m] (X : Matrix m m ℂ) :
    modConj (modConj X) = X :=
  Matrix.conjTranspose_conjTranspose X

/-- `J` is anti-multiplicative:
    `J (X * Y) = J Y * J X`. -/
theorem modConj_mul {m : Type*} [Fintype m]
    [DecidableEq m] (X Y : Matrix m m ℂ) :
    modConj (X * Y) = modConj Y * modConj X :=
  Matrix.conjTranspose_mul X Y

/-- `J` is conjugate-linear:
    `J (c • X) = (star c) • J X`. -/
theorem modConj_smul {m : Type*} [Fintype m]
    [DecidableEq m] (c : ℂ) (X : Matrix m m ℂ) :
    modConj (c • X) = star c • modConj X := by
  ext i j
  simp only [modConj, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, star_mul]
  rw [mul_comm]

/-- `J` exchanges left multiplication by `A` with right
    multiplication by `Aᴴ`: `J (A * J X) = X * Aᴴ` —
    the pointwise form of `J L_A J = R_{Aᴴ}`. -/
theorem modConj_leftMul {m : Type*} [Fintype m]
    [DecidableEq m] (A X : Matrix m m ℂ) :
    modConj (A * modConj X) = X * modConj A := by
  simp only [modConj, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- `J` exchanges right multiplication by `A` with left
    multiplication by `Aᴴ`: `J (J X * A) = Aᴴ * X` —
    the pointwise form of `J R_A J = L_{Aᴴ}`. -/
theorem modConj_rightMul {m : Type*} [Fintype m]
    [DecidableEq m] (A X : Matrix m m ℂ) :
    modConj (modConj X * A) = modConj A * X := by
  simp only [modConj, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-! ## §B2 — the finite commutant theorem -/

/-- **The finite commutant theorem: `J M J = M′`.** As
    sets of operators on the matrix space, the
    `J`-conjugate of the algebra — the operators
    `X ↦ J (A * J X) = X * Aᴴ` as `A` ranges over the
    algebra — is exactly the commutant of the
    left-multiplication action: the operators `T`
    satisfying `T (A * Y) = A * T Y` for all `A, Y`
    (such a `T` is right multiplication by `T 1`).
    This is the finite form of the pin's clause (b),
    in the operator-set formulation pre-registered in
    the pricing note (§6): `M` acts by left
    multiplication, `M′` is its commutant, and `J`
    carries one onto the other. -/
theorem jConj_image_eq_commutant {m : Type*} [Fintype m]
    [DecidableEq m] :
    {T : Matrix m m ℂ → Matrix m m ℂ |
        ∃ A, T = fun X => modConj (A * modConj X)}
      = {T : Matrix m m ℂ → Matrix m m ℂ |
          ∀ A Y, T (A * Y) = A * T Y} := by
  ext T
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, rfl⟩ B Y
    show modConj (A * modConj (B * Y))
      = B * modConj (A * modConj Y)
    have hinj : ∀ U V : Matrix m m ℂ,
        modConj U = modConj V → U = V := by
      intro U V h
      have h2 := congrArg modConj h
      simpa only [modConj_involutive] using h2
    apply hinj
    rw [modConj_involutive, modConj_leftMul, modConj_mul,
      mul_assoc]
  · intro hT
    refine ⟨modConj (T 1), ?_⟩
    funext X
    have hX : T X = X * T 1 := by
      have h := hT X 1
      rwa [Matrix.mul_one] at h
    rw [hX, modConj_leftMul, modConj_involutive]

end ThetLogos
