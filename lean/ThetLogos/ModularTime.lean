import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# ThetLogos.ModularTime — the corrected formal core (Tiers T1/T2/T3)

After the four mathematical corrections of 2026-09-25
(`spectral/modular-time.md`):

1. **Synthesis.** Time is derived, not primitive:
   `(ρ, D_F, β) → K(ρ,D_F,β) → σ_s → T`.
   Information + Heat + Geometry → Modular Time.
2. **Non-centrality.** The flow σ_s(a) = ρ^{is}aρ^{−is} is trivial iff
   [ρ,a] = 0; on M_N(ℂ) this means ρ = I/N. Nontrivial time requires ρ
   non-central *relative to the observable algebra* — ρ ≠ I/N alone does
   not guarantee nontrivial flow on every subalgebra. (The converse is
   deliberately not formalized: on a proper subalgebra a non-scalar ρ can
   lie in the commutant and give trivial flow there.)
3. **K_ρ := −ln ρ.** For the thermal state K_ρ = βD_F² + (ln Z)·I, and the
   scalar (ln Z)·I cancels in conjugation:
   σ_s(a) = e^{isβD_F²} a e^{−isβD_F²}.
4. **Precise ternary data.** 𝔗 = ρ, ℌ = β, 𝔊 = D_F; the temporal generator
   K = −ln ρ is synthesized, never postulated.

Tier T1 (proved): `modularEigenvalue_diff` (ln Z cancellation, spectral
form); `diagFlow_trivial_of_commute` ([ρ,a] = 0 ⟹ σ_s(a) = a, eigenbasis
form); `scalar_conj_trivial` (scalar modular unitaries act trivially);
`diagFlow_trivial_of_const` and `maximallyMixed_flow_trivial` (at maximal
ignorance the modular flow is trivial). Tier T3 target (labeled `sorry`):
the KMS identity in the eigenbasis. Numerical checks live in
`python/thet_logos/` (T3/T4).
-/

open Matrix NormedSpace

namespace ThetLogos

/-- The thermal triple (𝔗, ℌ, 𝔊): a state ρ (information), an inverse
    temperature β (heat), and a Dirac operator D (geometry). Time is
    derived from this triple via the modular flow — never postulated.
    Tier T2. -/
structure ThermalTriple (N : ℕ) where
  rho : Matrix (Fin N) (Fin N) ℂ
  beta : ℝ
  D : Matrix (Fin N) (Fin N) ℂ

/-- Modular eigenvalue: for D_F ψ_j = λ_j ψ_j, the thermal state
    ρ = e^{−βD_F²}/Z has κ_j = βλ_j² + ln Z. Tier T2. -/
noncomputable def modularEigenvalue (β lam logZ : ℝ) : ℝ :=
  β * lam ^ 2 + logZ

/-- Correction 3, spectral form (Tier T1 — proved): the ln Z term cancels
    in modular eigenvalue differences, so the modular flow sees only
    βD_F²: σ_s(a) = e^{isβD_F²} a e^{−isβD_F²}. -/
theorem modularEigenvalue_diff (β li lj logZ : ℝ) :
    modularEigenvalue β li logZ - modularEigenvalue β lj logZ
      = β * (li ^ 2 - lj ^ 2) := by
  unfold modularEigenvalue
  ring

/-- Complex power w^{is} for a weight w, via the principal logarithm.
    This is the eigenbasis form of ρ^{is}. -/
noncomputable def cpowI (w : ℝ) (s : ℝ) : ℂ :=
  Complex.exp (Complex.I * (s : ℂ) * (Real.log w : ℂ))

/-- w^{i(−s)} is the inverse of w^{is}. -/
theorem cpowI_neg (w : ℝ) (s : ℝ) : cpowI w (-s) = (cpowI w s)⁻¹ := by
  have hmul : cpowI w (-s) * cpowI w s = 1 := by
    unfold cpowI
    rw [← Complex.exp_add]
    have hexp : Complex.I * (((-s : ℝ) : ℂ)) * (Real.log w : ℂ)
        + Complex.I * ((s : ℝ) : ℂ) * (Real.log w : ℂ) = 0 := by
      have hcast : (((-s : ℝ) : ℂ)) = -((s : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]; ring
    rw [hexp, Complex.exp_zero]
  exact eq_inv_of_mul_eq_one_left hmul

/-- Modular flow in the eigenbasis: σ_s(a) = ρ^{is} a ρ^{−is} for
    ρ = diag(w). -/
noncomputable def diagFlow {N : ℕ} (w : Fin N → ℝ) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun j => cpowI (w j) s) * a
    * diagonal (fun j => cpowI (w j) (-s))

/-- Conjugation by constant diagonal matrices scales by the product. -/
theorem diag_const_conj {N : ℕ} (e e' : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    diagonal (fun _ => e) * A * diagonal (fun _ => e')
      = (e * e') • A := by
  ext i j
  simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A scalar matrix is a constant diagonal. -/
theorem smul_one_eq_diagonal {N : ℕ} (e : ℂ) :
    (e • (1 : Matrix (Fin N) (Fin N) ℂ)) = diagonal (fun _ => e) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

/-- Scalar-conjugation triviality (Tier T1 — proved): conjugating by a
    nonzero scalar matrix is the identity. For ρ = I/N the modular power
    ρ^{is} = N^{−is}·I is scalar, so this is the computational core of
    "at maximal ignorance, the modular flow is trivial". -/
theorem scalar_conj_trivial {N : ℕ} (e : ℂ) (he : e ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (e • (1 : Matrix (Fin N) (Fin N) ℂ)) * A
      * (e⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) = A := by
  rw [smul_one_eq_diagonal, smul_one_eq_diagonal, diag_const_conj,
    mul_inv_cancel₀ he, one_smul]

/-- At constant weights the eigenbasis flow is scalar conjugation. -/
theorem diagFlow_const_eq_scalarConj {N : ℕ} (c : ℝ) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (fun _ => c) s a
      = (cpowI c s • (1 : Matrix (Fin N) (Fin N) ℂ)) * a
        * ((cpowI c s)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  unfold diagFlow
  show diagonal (fun _ => cpowI c s) * a
    * diagonal (fun _ => cpowI c (-s)) = _
  rw [cpowI_neg, smul_one_eq_diagonal, smul_one_eq_diagonal]

/-- Correction 2, eigenbasis form (Tier T1 — proved):
    [ρ,a] = 0 ⟹ σ_s(a) = a. Where two weights coincide the modular phases
    cancel; where they differ, the commutator forces the matrix entry to
    vanish. The fully general statement follows by unitary diagonalization
    (reduction target, not formalized here). -/
theorem diagFlow_trivial_of_commute {N : ℕ} (w : Fin N → ℝ)
    (s : ℝ) (a : Matrix (Fin N) (Fin N) ℂ)
    (hcomm : diagonal (fun j => (w j : ℂ)) * a
      = a * diagonal (fun j => (w j : ℂ))) :
    diagFlow w s a = a := by
  have hentry : ∀ i j, (diagFlow w s a) i j
      = cpowI (w i) s * a i j * cpowI (w j) (-s) := by
    intro i j
    unfold diagFlow
    rw [mul_diagonal, diagonal_mul]
  have hcomm_ij : ∀ i j, (w i : ℂ) * a i j = a i j * (w j : ℂ) := by
    intro i j
    have h3 := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hcomm
    simp only [diagonal_mul, mul_diagonal] at h3
    exact h3
  ext i j
  rw [hentry i j]
  by_cases hwij : w i = w j
  · -- Equal weights: the modular phases cancel.
    have hphase : cpowI (w i) s * cpowI (w j) (-s) = 1 := by
      unfold cpowI
      rw [← Complex.exp_add]
      have hexp : Complex.I * (s : ℂ) * (Real.log (w i) : ℂ)
          + Complex.I * (((-s : ℝ) : ℂ)) * (Real.log (w j) : ℂ) = 0 := by
        have hcast : (((-s : ℝ) : ℂ)) = -((s : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, hwij]
        ring
      rw [hexp, Complex.exp_zero]
    calc cpowI (w i) s * a i j * cpowI (w j) (-s)
        = (cpowI (w i) s * cpowI (w j) (-s)) * a i j := by ring
      _ = a i j := by rw [hphase, one_mul]
  · -- Distinct weights: the commutator forces the entry to vanish.
    have haij : a i j = 0 := by
      have hne : (w i : ℂ) ≠ (w j : ℂ) := by
        intro hcon
        apply hwij
        exact_mod_cast hcon
      have hsub : ((w i : ℂ) - (w j : ℂ)) * a i j = 0 := by
        linear_combination hcomm_ij i j
      exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
    rw [haij]
    simp

/-- Constant weights give trivial flow, via scalar conjugation. -/
theorem diagFlow_trivial_of_const {N : ℕ} (c : ℝ) (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (fun _ => c) s a = a := by
  rw [diagFlow_const_eq_scalarConj]
  exact scalar_conj_trivial (cpowI c s) (by unfold cpowI; exact Complex.exp_ne_zero _) a

/-- Slogan, precise form (Tier T1 — proved): maximal ignorance gives
    trivial modular flow. (Non-central information gives temporal flow —
    see `diagFlow_trivial_of_commute`.) -/
theorem maximallyMixed_flow_trivial {N : ℕ} [NeZero N] (s : ℝ)
    (a : Matrix (Fin N) (Fin N) ℂ) :
    diagFlow (fun _ => 1 / (N : ℝ)) s a = a :=
  diagFlow_trivial_of_const _ s a

/-- A diagonal state from weights (the eigenbasis picture). -/
noncomputable def diagState {N : ℕ} (w : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun j => (w j : ℂ))

/-- Its modular Hamiltonian K_ρ = −ln ρ (diagonal in the eigenbasis). -/
noncomputable def diagModularK {N : ℕ} (w : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun j => ((-Real.log (w j) : ℝ) : ℂ))

/-- Correction 6 (Tier T3 target): the KMS identity in the eigenbasis.
    For weights w_j > 0 summing to 1, with σ_{−i}(B) = e^{−K}Be^{K}:
    Tr(ρAσ_{−i}(B)) = Tr(ρBA). This — not [ρ,K] = 0 — is the stationarity
    check the engines verify (numerically, to 1e-15–1e-20). -/
theorem kms_identity_diagonal {N : ℕ} (w : Fin N → ℝ) (hw : ∀ j, 0 < w j)
    (hw1 : ∑ j, w j = 1) (A B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (diagState w * A *
      (exp (-diagModularK w) * B * exp (diagModularK w)))
      = Matrix.trace (diagState w * B * A) := by
  sorry

end ThetLogos
