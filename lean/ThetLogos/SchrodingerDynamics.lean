import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import ThetLogos.FermionicInteraction

/-!
# Schrödinger dynamics in finite dimensions (T1)

Finite-dimensional Schrödinger dynamics for Hermitian (symmetric) Hamiltonians
on the corpus's finite-dimensional inner product spaces, with the headline
application to Pitch 3 Campaign 1's interacting fermionic Hamiltonian
`hamInt` (`FermionicInteraction.lean`).

For a symmetric operator `T` on a finite-dimensional complex inner product
space `H` this module constructs the one-parameter unitary group
`U(t) = exp (−i t T)` directly from the spectral theorem (Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis`, whose eigenvalues are real), and
proves: the group law, unitarity (as a `LinearIsometryEquiv`), the adjoint
identity `U(t)† = U(−t)`, the eigenphase action, the explicit solution formula,
the Schrödinger equation `dψ/dt = −i • T ψ(t)` in the finite-dimensional ODE
sense, uniqueness of solutions, invariance of every eigenspace (hence of the
two spectral clusters of `hamInt_gap_persistence`), the Heisenberg-picture
evolution of observables with its equation `dA/dt = i • [T, A(t)]`, and the
agreement of expectation values between the two pictures.

## Honesty clause (mandatory, per the Schrödinger gauntlet)

* **Finite dimensions only.** Every statement here is about a
  finite-dimensional inner product space (headline instance: `FermionicFock d`).
* The Schrödinger and Heisenberg pictures are **unitarily equivalent
  bookkeeping**; `picture_equiv` below is exactly that statement and nothing
  more. This module takes **no interpretation position**: interpretations of
  quantum mechanics (Copenhagen, many-worlds, QBism, Bohmian mechanics,
  wave-function realism, the measurement problem) are **T5** per the gauntlet
  dossier `whitepaper/gauntlet-schrodinger-2026-10-16.md` §5 and are neither
  proved, refuted, nor used here.
* Dynamics of the **bosonic / whole-space** theory is **FRONTIER** and is NOT
  in this module: the bosonic Hamiltonian is unbounded, Mathlib has no
  unbounded Stone theorem, and no claim about bosonic time evolution is made
  or implied. (Sectorwise bosonic dynamics is a separate, Campaign-2-adjacent
  item, also not claimed here.)
* Nothing here concerns the continuum Schrödinger PDE; that is Pitch 4
  territory and is not touched.

Asset note (gauntlet verification): the gauntlet priced this exhibit as
"¾ prebuilt" from `stone_finiteDim` (`StoneFiniteDim2.lean`), `jointFC`
(`SpectralFrontier.lean`) and the exp-unitarity pattern of `modularUnitary`
(`FlowKernel.lean`). In the event, `stone_finiteDim` runs the wrong direction
for this construction (it starts from a unitary group and recovers a
generator), and Mathlib's packaged spectral theorem (`eigenvectorBasis`)
subsumes the role the gauntlet assigned to `jointFC`; neither corpus asset is
imported. What *is* consumed from the corpus is Pitch 3 Campaign 1 itself
(`hamInt`, `hamInt_isSymmetric`, `hamInt_gap_persistence`, `intBound`,
`hamiltonianDens_isSymmetric`).
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## §1. The scalar phase `exp (−i μ t)` -/

/-- The unitary phase picked up by an eigenvector of eigenvalue `μ` (real)
after time `t`: `exp ((−μ t) · i)`. -/
noncomputable def evolPhase (μ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (↑((-μ) * t) * Complex.I)

theorem evolPhase_zero (μ : ℝ) : evolPhase μ 0 = 1 := by
  simp [evolPhase]

theorem evolPhase_norm (μ : ℝ) (t : ℝ) : ‖evolPhase μ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem evolPhase_add (μ : ℝ) (s t : ℝ) :
    evolPhase μ (s + t) = evolPhase μ s * evolPhase μ t := by
  have h : (-μ) * (s + t) = (-μ) * s + (-μ) * t := by ring
  simp only [evolPhase, h, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem evolPhase_conj_neg (μ : ℝ) (t : ℝ) :
    (starRingEnd ℂ) (evolPhase μ (-t)) = evolPhase μ t := by
  have h1 : (-μ) * -t = μ * t := by ring
  have h2 : (-μ) * t = -(μ * t) := by ring
  simp only [evolPhase, h1, h2, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_neg,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem evolPhase_neg_arg (μ : ℝ) (t : ℝ) : evolPhase μ (-t) = evolPhase (-μ) t := by
  have e : (-μ) * -t = (- -μ) * t := by ring
  simp only [evolPhase, e]

theorem hasDerivAt_evolPhase (μ : ℝ) (t : ℝ) :
    HasDerivAt (evolPhase μ) (evolPhase μ t * (↑(-μ) * Complex.I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (-μ) * s) (-μ) t := by
    simpa using (hasDerivAt_id t).const_mul (-μ)
  have h2 : HasDerivAt (fun s : ℝ => (↑((-μ) * s) : ℂ) * Complex.I)
      ((↑(-μ) : ℂ) * Complex.I) t :=
    h1.ofReal_comp.mul_const Complex.I
  have h3 := h2.cexp
  exact h3

theorem hasDerivAt_evolPhase_neg (μ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => evolPhase μ (-s)) (evolPhase μ (-t) * (↑μ * Complex.I)) t := by
  have hfun : (fun s => evolPhase μ (-s)) = evolPhase (-μ) :=
    funext fun s => evolPhase_neg_arg μ s
  rw [hfun, evolPhase_neg_arg]
  simpa using hasDerivAt_evolPhase (-μ) t

/-! ## §2. Spectral data of a symmetric operator -/

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)

/-- The eigenbasis of a symmetric operator, from Mathlib's spectral theorem. -/
noncomputable def evolBasis (hT : T.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  hT.eigenvectorBasis rfl

/-- The (real) eigenvalues of a symmetric operator. -/
noncomputable def evolEig (hT : T.IsSymmetric) (k : Fin (Module.finrank ℂ H)) : ℝ :=
  hT.eigenvalues rfl k

theorem evolBasis_apply_eig (k : Fin (Module.finrank ℂ H)) :
    T ((evolBasis hT) k) = (evolEig hT k : ℂ) • (evolBasis hT) k :=
  hT.apply_eigenvectorBasis rfl k

theorem evolBasis_repr_T (x : H) (k : Fin (Module.finrank ℂ H)) :
    ((evolBasis hT).repr (T x)).ofLp k
      = (evolEig hT k : ℂ) * ((evolBasis hT).repr x).ofLp k :=
  hT.eigenvectorBasis_apply_self_apply rfl x k

/-- Expansion of a vector in the eigenbasis, in `repr`-coordinate form. -/
theorem sum_repr_ofLp (x : H) :
    ∑ k, ((evolBasis hT).repr x).ofLp k • (evolBasis hT) k = x := by
  have h : ∀ k : Fin (Module.finrank ℂ H),
      ((evolBasis hT).repr x).ofLp k • (evolBasis hT) k
        = ⟪(evolBasis hT) k, x⟫_ℂ • (evolBasis hT) k :=
    fun k => by rw [(evolBasis hT).repr_apply_apply]
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  exact (evolBasis hT).sum_repr' x

/-- Two vectors with the same eigenbasis coordinates are equal. -/
theorem eq_of_forall_inner_basis {z w : H}
    (h : ∀ k, ⟪(evolBasis hT) k, z⟫_ℂ = ⟪(evolBasis hT) k, w⟫_ℂ) : z = w := by
  apply (evolBasis hT).repr.injective
  apply PiLp.ext
  intro k
  rw [(evolBasis hT).repr_apply_apply, (evolBasis hT).repr_apply_apply]
  exact h k

/-! ## §3. The evolution operator -/

/-- `evolOp hT t = exp (−i t • T)`: the Schrödinger evolution operator of the
symmetric Hamiltonian `T`, defined diagonally in the eigenbasis of `T`. -/
noncomputable def evolOp (hT : T.IsSymmetric) (t : ℝ) : H →ₗ[ℂ] H :=
  (evolBasis hT).toBasis.constr ℂ
    fun k => evolPhase (evolEig hT k) t • (evolBasis hT) k

theorem evolOp_apply_basis (t : ℝ) (k : Fin (Module.finrank ℂ H)) :
    evolOp hT t ((evolBasis hT) k) = evolPhase (evolEig hT k) t • (evolBasis hT) k :=
  Module.Basis.constr_basis _ _ _ _

theorem evolOp_apply (t : ℝ) (x : H) :
    evolOp hT t x = ∑ k, (evolPhase (evolEig hT k) t
      * ((evolBasis hT).repr x).ofLp k) • (evolBasis hT) k := by
  have step : evolOp hT t x
      = evolOp hT t (∑ k, ((evolBasis hT).repr x).ofLp k • (evolBasis hT) k) :=
    congrArg _ (sum_repr_ofLp hT x).symm
  rw [step, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, evolOp_apply_basis, smul_smul]
  congr 1
  ring

/-- The solution formula: the evolved state's eigenbasis coefficients are the
initial coefficients multiplied by the eigenphases. This *is* the wave
function in the occupation/eigen basis, in coefficient dialect. -/
theorem evolOp_solution_formula (t : ℝ) (ψ : H) :
    evolOp hT t ψ = ∑ k, (evolPhase (evolEig hT k) t
      * ⟪(evolBasis hT) k, ψ⟫_ℂ) • (evolBasis hT) k := by
  rw [evolOp_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [(evolBasis hT).repr_apply_apply]

theorem evolOp_repr (t : ℝ) (x : H) (k : Fin (Module.finrank ℂ H)) :
    ((evolBasis hT).repr (evolOp hT t x)).ofLp k
      = evolPhase (evolEig hT k) t * ((evolBasis hT).repr x).ofLp k := by
  rw [(evolBasis hT).repr_apply_apply, evolOp_solution_formula, inner_sum]
  rw [Finset.sum_eq_single k]
  · rw [inner_smul_right,
      orthonormal_iff_ite.mp (evolBasis hT).orthonormal k k, if_pos rfl, mul_one,
      (evolBasis hT).repr_apply_apply]
  · intro j _ hjk
    rw [inner_smul_right,
      orthonormal_iff_ite.mp (evolBasis hT).orthonormal k j, if_neg hjk.symm, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem evolOp_inner_basis (t : ℝ) (x : H) (k : Fin (Module.finrank ℂ H)) :
    ⟪(evolBasis hT) k, evolOp hT t x⟫_ℂ
      = evolPhase (evolEig hT k) t * ⟪(evolBasis hT) k, x⟫_ℂ := by
  rw [← (evolBasis hT).repr_apply_apply, evolOp_repr,
    (evolBasis hT).repr_apply_apply]

/-! ## §4. Group law, unitarity, adjoint -/

theorem evolOp_zero : evolOp hT 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [evolOp_apply]
  simp only [evolPhase_zero, one_mul, LinearMap.id_apply]
  exact sum_repr_ofLp hT x

theorem evolOp_add (s t : ℝ) : evolOp hT (s + t) = (evolOp hT s).comp (evolOp hT t) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, evolOp_apply hT t x, map_sum, evolOp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, evolOp_apply_basis, smul_smul, evolPhase_add]
  congr 1
  ring

theorem evolOp_add_neg (t : ℝ) :
    (evolOp hT t).comp (evolOp hT (-t)) = LinearMap.id := by
  rw [← evolOp_add, add_neg_cancel, evolOp_zero]

theorem evolOp_neg_add (t : ℝ) :
    (evolOp hT (-t)).comp (evolOp hT t) = LinearMap.id := by
  rw [← evolOp_add, neg_add_cancel, evolOp_zero]

theorem evolOp_apply_neg_apply (t : ℝ) (y : H) : evolOp hT t (evolOp hT (-t) y) = y := by
  have h := evolOp_add_neg hT t
  calc evolOp hT t (evolOp hT (-t) y)
      = ((evolOp hT t).comp (evolOp hT (-t))) y := rfl
    _ = y := by rw [h]; rfl

theorem evolOp_neg_apply_apply (t : ℝ) (y : H) : evolOp hT (-t) (evolOp hT t y) = y := by
  have h := evolOp_neg_add hT t
  calc evolOp hT (-t) (evolOp hT t y)
      = ((evolOp hT (-t)).comp (evolOp hT t)) y := rfl
    _ = y := by rw [h]; rfl

/-- The evolution operator is an isometry. -/
theorem evolOp_isometry (t : ℝ) (x : H) : ‖evolOp hT t x‖ = ‖x‖ := by
  have e1 : ‖evolOp hT t x‖ = ‖(evolBasis hT).repr (evolOp hT t x)‖ :=
    ((evolBasis hT).repr.norm_map _).symm
  have e2 : ‖x‖ = ‖(evolBasis hT).repr x‖ := ((evolBasis hT).repr.norm_map _).symm
  rw [e1, e2, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [evolOp_repr, norm_mul, evolPhase_norm, one_mul]

/-- `evolOp hT t` packaged as a unitary: a linear isometry equivalence. -/
noncomputable def evolUnitary (hT : T.IsSymmetric) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := evolOp hT t, norm_map' := evolOp_isometry hT t }
    (fun y => ⟨evolOp hT (-t) y, evolOp_apply_neg_apply hT t y⟩)

theorem evolUnitary_apply (t : ℝ) (x : H) : evolUnitary hT t x = evolOp hT t x :=
  rfl

theorem evolUnitary_symm_apply (t : ℝ) (x : H) :
    (evolUnitary hT t).symm x = evolOp hT (-t) x := by
  apply (evolUnitary hT t).injective
  rw [LinearIsometryEquiv.apply_symm_apply, evolUnitary_apply]
  exact (evolOp_apply_neg_apply hT t x).symm

/-- The adjoint of the evolution operator is the backward evolution. -/
theorem evolOp_adjoint (t : ℝ) : (evolOp hT t).adjoint = evolOp hT (-t) := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro x y
  have key : ∀ z w : H, ⟪z, w⟫_ℂ
      = ∑ k, ((evolBasis hT).repr w).ofLp k
        * (starRingEnd ℂ) (((evolBasis hT).repr z).ofLp k) := by
    intro z w
    rw [← (evolBasis hT).repr.inner_map_map z w, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => RCLike.inner_apply _ _
  rw [key, key]
  apply Finset.sum_congr rfl
  intro k _
  rw [evolOp_repr, evolOp_repr, map_mul, evolPhase_conj_neg]
  ring

/-! ## §5. Eigenspace invariance -/

/-- Eigenbasis coordinates of `T x`: multiplication by the eigenvalue. -/
theorem inner_basis_T (x : H) (k : Fin (Module.finrank ℂ H)) :
    ⟪(evolBasis hT) k, T x⟫_ℂ = (evolEig hT k : ℂ) * ⟪(evolBasis hT) k, x⟫_ℂ := by
  have h2 : ⟪(evolBasis hT) k, T x⟫_ℂ = ⟪T ((evolBasis hT) k), x⟫_ℂ := by
    have hsym := hT x ((evolBasis hT) k)
    have h3 : (starRingEnd ℂ) ⟪T x, (evolBasis hT) k⟫_ℂ
        = ⟪(evolBasis hT) k, T x⟫_ℂ := inner_conj_symm _ _
    have h4 : (starRingEnd ℂ) ⟪x, T ((evolBasis hT) k)⟫_ℂ
        = ⟪T ((evolBasis hT) k), x⟫_ℂ := inner_conj_symm _ _
    rw [← h3, hsym]
    exact h4
  rw [h2, evolBasis_apply_eig, inner_smul_left, Complex.conj_ofReal]

/-- The evolution commutes with its generator. -/
theorem evolOp_commute (t : ℝ) : (evolOp hT t).comp T = T.comp (evolOp hT t) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, evolOp_apply hT t (T x),
    evolOp_apply hT t x, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [evolBasis_repr_T, map_smul, evolBasis_apply_eig, smul_smul]
  congr 1
  ring

theorem evolOp_apply_commute (t : ℝ) (x : H) : evolOp hT t (T x) = T (evolOp hT t x) := by
  calc evolOp hT t (T x) = ((evolOp hT t).comp T) x := rfl
    _ = (T.comp (evolOp hT t)) x := by rw [evolOp_commute]
    _ = T (evolOp hT t x) := rfl

/-- Every eigenspace of `T` is invariant under the evolution. -/
theorem evolOp_map_eigenspace_le (t : ℝ) (μ : ℂ) :
    (Module.End.eigenspace T μ).map (evolOp hT t) ≤ Module.End.eigenspace T μ := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← evolOp_apply_commute, hx, map_smul]

/-- On an eigenvector, the evolution is exactly the eigenphase. The eigenvalue
of a symmetric operator is real, so the phase is taken at `μ.re`. -/
theorem evolOp_apply_mem_eigenspace (t : ℝ) {ψ : H} {μ : ℂ}
    (hψ : ψ ∈ Module.End.eigenspace T μ) :
    evolOp hT t ψ = evolPhase μ.re t • ψ := by
  rw [Module.End.mem_eigenspace_iff] at hψ
  by_cases h0 : ψ = 0
  · rw [h0, map_zero, smul_zero]
  have hEig : Module.End.HasEigenvalue T μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hψ, h0⟩
  have him : μ.im = 0 := Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self hEig)
  have hμre : μ = (μ.re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im μ]
    rw [him]
    simp
  apply eq_of_forall_inner_basis hT
  intro k
  rw [evolOp_inner_basis, inner_smul_right]
  by_cases hc : ⟪(evolBasis hT) k, ψ⟫_ℂ = 0
  · rw [hc, mul_zero, mul_zero]
  · have hcoord : (evolEig hT k : ℂ) * ⟪(evolBasis hT) k, ψ⟫_ℂ
        = μ * ⟪(evolBasis hT) k, ψ⟫_ℂ := by
      have h1 := inner_basis_T hT ψ k
      rw [hψ, inner_smul_right] at h1
      exact h1.symm
    have hEk : evolEig hT k = μ.re := by
      have h5 : (evolEig hT k : ℂ) = μ := mul_right_cancel₀ hc hcoord
      rw [hμre] at h5
      exact Complex.ofReal_inj.mp h5
    rw [hEk]

/-! ## §6. The Schrödinger equation -/

/-- The evolved state solves the Schrödinger equation
`dψ/dt = −i • T ψ(t)` in the finite-dimensional ODE sense. -/
theorem hasDerivAt_evolOp_apply (ψ : H) (t : ℝ) :
    HasDerivAt (fun s => evolOp hT s ψ) ((-Complex.I) • T (evolOp hT t ψ)) t := by
  have hfun : (fun s => evolOp hT s ψ)
      = ∑ k, (fun s => (evolPhase (evolEig hT k) s * ⟪(evolBasis hT) k, ψ⟫_ℂ)
          • (evolBasis hT) k) := by
    funext s
    rw [Finset.sum_apply]
    exact evolOp_solution_formula hT s ψ
  rw [hfun]
  have hterm : ∀ k : Fin (Module.finrank ℂ H),
      HasDerivAt (fun s => (evolPhase (evolEig hT k) s * ⟪(evolBasis hT) k, ψ⟫_ℂ)
          • (evolBasis hT) k)
        ((evolPhase (evolEig hT k) t * (↑(-(evolEig hT k)) * Complex.I)
          * ⟪(evolBasis hT) k, ψ⟫_ℂ) • (evolBasis hT) k) t := by
    intro k
    have h1 := (hasDerivAt_evolPhase (evolEig hT k) t).mul
      (hasDerivAt_const t (⟪(evolBasis hT) k, ψ⟫_ℂ))
    simpa only [Pi.mul_apply, mul_zero, add_zero] using
      h1.smul_const ((evolBasis hT) k)
  have hsum : HasDerivAt
      (∑ k, (fun s => (evolPhase (evolEig hT k) s * ⟪(evolBasis hT) k, ψ⟫_ℂ)
        • (evolBasis hT) k))
      (∑ k, (evolPhase (evolEig hT k) t * (↑(-(evolEig hT k)) * Complex.I)
        * ⟪(evolBasis hT) k, ψ⟫_ℂ) • (evolBasis hT) k) t :=
    HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  convert hsum using 1
  rw [evolOp_solution_formula, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, evolBasis_apply_eig, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- Uniqueness: a `C¹` curve satisfying the Schrödinger equation with initial
value `ψ₀` is the evolution of `ψ₀`. Proved coordinatewise with an integrating
factor — no ODE library is needed in finite dimensions. -/
theorem evolOp_unique (ψ : ℝ → H) (ψ₀ : H)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I) • T (ψ s)) s) (h0 : ψ 0 = ψ₀) (t : ℝ) :
    ψ t = evolOp hT t ψ₀ := by
  have hcoord : ∀ (k : Fin (Module.finrank ℂ H)) (s : ℝ),
      HasDerivAt (fun u => ⟪(evolBasis hT) k, ψ u⟫_ℂ)
        (((-Complex.I) * (evolEig hT k : ℂ)) * ⟪(evolBasis hT) k, ψ s⟫_ℂ) s := by
    intro k s
    have h1 := (hasDerivAt_const s ((evolBasis hT) k)).inner ℂ (hψ s)
    have hval : ⟪(evolBasis hT) k, (-Complex.I) • T (ψ s)⟫_ℂ + ⟪(0 : H), ψ s⟫_ℂ
        = ((-Complex.I) * (evolEig hT k : ℂ)) * ⟪(evolBasis hT) k, ψ s⟫_ℂ := by
      rw [inner_zero_left, add_zero, inner_smul_right, inner_basis_T]
      ring
    rwa [hval] at h1
  have hkey : ∀ k : Fin (Module.finrank ℂ H),
      ⟪(evolBasis hT) k, ψ t⟫_ℂ
        = ⟪(evolBasis hT) k, ψ₀⟫_ℂ * evolPhase (evolEig hT k) t := by
    intro k
    set a : ℂ := (-Complex.I) * (evolEig hT k : ℂ) with ha
    have he : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (-(a * (u : ℂ))))
        (Complex.exp (-(a * (s : ℂ))) * (-a)) s := by
      intro s
      have hlin : HasDerivAt (fun u : ℝ => a * (u : ℂ)) a s := by
        have hh := ((hasDerivAt_id s).ofReal_comp).const_mul a
        simpa using hh
      exact (hlin.neg).cexp
    have hprod : ∀ s : ℝ, HasDerivAt
        (fun u => ⟪(evolBasis hT) k, ψ u⟫_ℂ * Complex.exp (-(a * (u : ℂ))))
        0 s := by
      intro s
      have hp := (hcoord k s).mul (he s)
      have hzero : (a * ⟪(evolBasis hT) k, ψ s⟫_ℂ) * Complex.exp (-(a * (s : ℂ)))
          + ⟪(evolBasis hT) k, ψ s⟫_ℂ * (Complex.exp (-(a * (s : ℂ))) * -a) = 0 := by
        ring
      rwa [hzero] at hp
    have hdiff : Differentiable ℝ
        (fun u => ⟪(evolBasis hT) k, ψ u⟫_ℂ * Complex.exp (-(a * (u : ℂ)))) :=
      fun s => (hprod s).differentiableAt
    have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hprod s).deriv) t 0
    have he0 : Complex.exp (-(a * ((0 : ℝ) : ℂ))) = 1 := by simp
    have hne : Complex.exp (-(a * (t : ℂ))) ≠ 0 := Complex.exp_ne_zero _
    have hfin : ⟪(evolBasis hT) k, ψ t⟫_ℂ * Complex.exp (-(a * (t : ℂ)))
        = ⟪(evolBasis hT) k, ψ₀⟫_ℂ := by
      have hcc := hconst
      rw [he0, mul_one, h0] at hcc
      exact hcc
    have hexp : Complex.exp (a * (t : ℂ)) = evolPhase (evolEig hT k) t := by
      rw [ha, evolPhase]
      congr 1
      push_cast
      ring
    calc ⟪(evolBasis hT) k, ψ t⟫_ℂ
        = ⟪(evolBasis hT) k, ψ t⟫_ℂ
          * (Complex.exp (-(a * (t : ℂ))) * (Complex.exp (-(a * (t : ℂ))))⁻¹) := by
          rw [mul_inv_cancel₀ hne, mul_one]
      _ = (⟪(evolBasis hT) k, ψ t⟫_ℂ * Complex.exp (-(a * (t : ℂ))))
          * (Complex.exp (-(a * (t : ℂ))))⁻¹ := by
          rw [← mul_assoc]
      _ = ⟪(evolBasis hT) k, ψ₀⟫_ℂ * (Complex.exp (-(a * (t : ℂ))))⁻¹ := by
          rw [hfin]
      _ = ⟪(evolBasis hT) k, ψ₀⟫_ℂ * Complex.exp (a * (t : ℂ)) := by
          rw [← Complex.exp_neg, neg_neg]
      _ = ⟪(evolBasis hT) k, ψ₀⟫_ℂ * evolPhase (evolEig hT k) t := by
          rw [hexp]
  apply eq_of_forall_inner_basis hT
  intro k
  rw [evolOp_inner_basis, hkey k]
  exact mul_comm _ _

end General

/-! ## §7. The Heisenberg picture -/

section Heisenberg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)

/-- Heisenberg-picture evolution of an observable:
`A(t) = U(−t) ∘ A ∘ U(t)`. -/
noncomputable def heisenbergEvol (hT : T.IsSymmetric) (t : ℝ) (A : H →ₗ[ℂ] H) :
    H →ₗ[ℂ] H :=
  (evolOp hT (-t)).comp (A.comp (evolOp hT t))

theorem heisenbergEvol_apply (t : ℝ) (A : H →ₗ[ℂ] H) (ψ : H) :
    heisenbergEvol hT t A ψ = evolOp hT (-t) (A (evolOp hT t ψ)) :=
  rfl

theorem heisenbergEvol_zero (A : H →ₗ[ℂ] H) : heisenbergEvol hT 0 A = A := by
  simp only [heisenbergEvol, neg_zero, evolOp_zero, LinearMap.comp_id,
    LinearMap.id_comp]

theorem heisenbergEvol_add (s t : ℝ) (A : H →ₗ[ℂ] H) :
    heisenbergEvol hT (s + t) A = heisenbergEvol hT s (heisenbergEvol hT t A) := by
  have key : (evolOp hT t).comp (evolOp hT s) = (evolOp hT s).comp (evolOp hT t) := by
    rw [← evolOp_add hT t s, ← evolOp_add hT s t, add_comm t s]
  simp only [heisenbergEvol, neg_add, evolOp_add, LinearMap.comp_assoc]
  rw [key]

theorem heisenbergEvol_mul (t : ℝ) (A B : H →ₗ[ℂ] H) :
    heisenbergEvol hT t (A.comp B)
      = (heisenbergEvol hT t A).comp (heisenbergEvol hT t B) := by
  apply LinearMap.ext
  intro ψ
  have e1 : heisenbergEvol hT t B ψ = evolOp hT (-t) (B (evolOp hT t ψ)) :=
    heisenbergEvol_apply hT t B ψ
  rw [LinearMap.comp_apply, heisenbergEvol_apply, heisenbergEvol_apply, e1,
    evolOp_apply_neg_apply, LinearMap.comp_apply]

theorem heisenbergEvol_one (t : ℝ) :
    heisenbergEvol hT t LinearMap.id = LinearMap.id := by
  simp only [heisenbergEvol, LinearMap.id_comp, evolOp_neg_add]

/-- The `k`-th eigenbasis coordinate of a Heisenberg-evolved observable applied
to `ψ`, as a function of time: a phase-weighted matrix-element sum. -/
noncomputable def heisCoord (hT : T.IsSymmetric) (A : H →ₗ[ℂ] H) (ψ : H)
    (k : Fin (Module.finrank ℂ H)) (s : ℝ) : ℂ :=
  evolPhase (evolEig hT k) (-s) * ∑ l, (evolPhase (evolEig hT l) s
    * ⟪(evolBasis hT) l, ψ⟫_ℂ) * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ

/-- The time derivative of `heisCoord`, in the raw product-rule form. -/
noncomputable def heisCoordDeriv (hT : T.IsSymmetric) (A : H →ₗ[ℂ] H) (ψ : H)
    (k : Fin (Module.finrank ℂ H)) (t : ℝ) : ℂ :=
  evolPhase (evolEig hT k) (-t) * (↑(evolEig hT k) * Complex.I)
      * (∑ l, (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)
    + evolPhase (evolEig hT k) (-t)
      * (∑ l, ((evolPhase (evolEig hT l) t * (↑(-(evolEig hT l)) * Complex.I))
          * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)

theorem heisenbergEvol_inner_basis (s : ℝ) (A : H →ₗ[ℂ] H) (ψ : H)
    (k : Fin (Module.finrank ℂ H)) :
    ⟪(evolBasis hT) k, heisenbergEvol hT s A ψ⟫_ℂ = heisCoord hT A ψ k s := by
  simp only [heisCoord]
  rw [heisenbergEvol_apply, evolOp_inner_basis]
  congr 1
  have hA : ∀ y : H, ⟪(evolBasis hT) k, A y⟫_ℂ
      = ∑ l, ⟪(evolBasis hT) l, y⟫_ℂ
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ := by
    intro y
    conv_lhs => rw [← sum_repr_ofLp hT y]
    rw [map_sum, inner_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_smul, inner_smul_right, (evolBasis hT).repr_apply_apply]
  rw [hA]
  apply Finset.sum_congr rfl
  intro l _
  rw [evolOp_inner_basis]

theorem hasDerivAt_heisCoord (A : H →ₗ[ℂ] H) (ψ : H)
    (k : Fin (Module.finrank ℂ H)) (t : ℝ) :
    HasDerivAt (heisCoord hT A ψ k) (heisCoordDeriv hT A ψ k t) t := by
  have hS : HasDerivAt
      (∑ l, (fun s => (evolPhase (evolEig hT l) s * ⟪(evolBasis hT) l, ψ⟫_ℂ)
          * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ))
      (∑ l, ((evolPhase (evolEig hT l) t * (↑(-(evolEig hT l)) * Complex.I))
          * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ) t := by
    apply HasDerivAt.sum
    intro l _
    exact ((hasDerivAt_evolPhase (evolEig hT l) t).mul_const _).mul_const _
  have hSeq : (fun s => ∑ l, (evolPhase (evolEig hT l) s
        * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)
      = ∑ l, (fun s => (evolPhase (evolEig hT l) s * ⟪(evolBasis hT) l, ψ⟫_ℂ)
          * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ) := by
    funext s
    rw [Finset.sum_apply]
  have hS' : HasDerivAt (fun s => ∑ l, (evolPhase (evolEig hT l) s
        * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)
      (∑ l, ((evolPhase (evolEig hT l) t * (↑(-(evolEig hT l)) * Complex.I))
          * ⟪(evolBasis hT) l, ψ⟫_ℂ)
        * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ) t :=
    hSeq.symm ▸ hS
  have hprod := (hasDerivAt_evolPhase_neg (evolEig hT k) t).mul hS'
  exact hprod

/-- The raw derivative of a Heisenberg coordinate, in commutator form:
`i • (μ_k · coord − (the coordinate for T ψ))`. -/
theorem heisCoordDeriv_eq (A : H →ₗ[ℂ] H) (ψ : H)
    (k : Fin (Module.finrank ℂ H)) (t : ℝ) :
    heisCoordDeriv hT A ψ k t
      = Complex.I * ((evolEig hT k : ℂ) * heisCoord hT A ψ k t
        - evolPhase (evolEig hT k) (-t) * ∑ l, ((evolEig hT l : ℂ)
            * (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ))
            * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ) := by
  have step1 : evolPhase (evolEig hT k) (-t) * (↑(evolEig hT k) * Complex.I)
        * (∑ l, (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ)
          * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)
      = Complex.I * ((evolEig hT k : ℂ) * (evolPhase (evolEig hT k) (-t)
          * ∑ l, (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ)
            * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)) := by
    ring
  have step2 : evolPhase (evolEig hT k) (-t)
        * (∑ l, ((evolPhase (evolEig hT l) t * (↑(-(evolEig hT l)) * Complex.I))
            * ⟪(evolBasis hT) l, ψ⟫_ℂ)
          * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)
      = - (Complex.I * (evolPhase (evolEig hT k) (-t)
          * ∑ l, ((evolEig hT l : ℂ)
              * (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ))
            * ⟪(evolBasis hT) k, A ((evolBasis hT) l)⟫_ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    push_cast
    ring
  simp only [heisCoordDeriv, heisCoord]
  rw [step1, step2]
  ring

/-- The Heisenberg equation: `dA(t)/dt = i • [T, A(t)]`, applied to a vector,
proved in the eigenbasis coordinate dialect. -/
theorem heisenberg_equation (A : H →ₗ[ℂ] H) (ψ : H) (t : ℝ) :
    HasDerivAt (fun s => heisenbergEvol hT s A ψ)
      ((Complex.I • (T.comp (heisenbergEvol hT t A)
        - (heisenbergEvol hT t A).comp T)) ψ) t := by
  have hRHS : ∀ j, ⟪(evolBasis hT) j, ((Complex.I
        • (T.comp (heisenbergEvol hT t A)
          - (heisenbergEvol hT t A).comp T)) ψ)⟫_ℂ
      = heisCoordDeriv hT A ψ j t := by
    intro j
    have e1 : ⟪(evolBasis hT) j, heisenbergEvol hT t A (T ψ)⟫_ℂ
        = evolPhase (evolEig hT j) (-t) * ∑ l, ((evolEig hT l : ℂ)
            * (evolPhase (evolEig hT l) t * ⟪(evolBasis hT) l, ψ⟫_ℂ))
            * ⟪(evolBasis hT) j, A ((evolBasis hT) l)⟫_ℂ := by
      rw [heisenbergEvol_inner_basis]
      simp only [heisCoord]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [inner_basis_T]
      ring
    rw [heisCoordDeriv_eq, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, inner_smul_right,
      inner_sub_right, inner_basis_T, heisenbergEvol_inner_basis, e1]
  have hF : (fun s => heisenbergEvol hT s A ψ)
      = ∑ k, (fun s => heisCoord hT A ψ k s • (evolBasis hT) k) := by
    funext s
    rw [Finset.sum_apply]
    apply eq_of_forall_inner_basis hT
    intro j
    rw [heisenbergEvol_inner_basis, inner_sum]
    rw [Finset.sum_eq_single j]
    · rw [inner_smul_right,
        orthonormal_iff_ite.mp (evolBasis hT).orthonormal j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [inner_smul_right,
        orthonormal_iff_ite.mp (evolBasis hT).orthonormal j i, if_neg hij.symm,
        mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hF]
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_heisCoord hT A ψ k t).smul_const ((evolBasis hT) k))
  convert hsum using 1
  apply eq_of_forall_inner_basis hT
  intro j
  rw [inner_sum]
  rw [Finset.sum_eq_single j]
  · rw [inner_smul_right,
      orthonormal_iff_ite.mp (evolBasis hT).orthonormal j j, if_pos rfl, mul_one]
    exact hRHS j
  · intro i _ hij
    rw [inner_smul_right,
      orthonormal_iff_ite.mp (evolBasis hT).orthonormal j i, if_neg hij.symm,
      mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Picture equivalence: expectation values agree between the Schrödinger and
Heisenberg pictures. This is a statement about bookkeeping only; it takes no
interpretation position (interpretations are T5, per the gauntlet). -/
theorem picture_equiv (t : ℝ) (A : H →ₗ[ℂ] H) (ψ : H) :
    ⟪evolOp hT t ψ, A (evolOp hT t ψ)⟫_ℂ
      = ⟪ψ, heisenbergEvol hT t A ψ⟫_ℂ := by
  rw [heisenbergEvol_apply, ← evolOp_adjoint]
  exact (LinearMap.adjoint_inner_right (evolOp hT t) ψ (A (evolOp hT t ψ))).symm

end Heisenberg

/-! ## §8. Application: Pitch 3 Campaign 1's interacting Hamiltonian -/

section Clusters

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)

/-- Any span of eigenbasis vectors selected by an index predicate is an
invariant subspace for the evolution. -/
theorem evolOp_map_cluster_le (t : ℝ) (P : Fin (Module.finrank ℂ H) → Prop) :
    (⨆ k, ⨆ _ : P k, ℂ ∙ (evolBasis hT) k).map (evolOp hT t)
      ≤ ⨆ k, ⨆ _ : P k, ℂ ∙ (evolBasis hT) k := by
  have hsingle : ∀ k, (ℂ ∙ (evolBasis hT) k).map (evolOp hT t)
      ≤ ℂ ∙ (evolBasis hT) k := by
    intro k
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_comap, evolOp_apply_basis]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [Submodule.map_iSup]
  apply iSup_le
  intro k
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hk
  exact le_trans (hsingle k) (le_iSup_of_le k (le_iSup_of_le hk le_rfl))

end Clusters

section HamInt

variable (d : ℕ)

/-- The ground cluster of `hamInt_gap_persistence` as a subspace: the span of
the eigenvectors of `hamInt` whose eigenvalue is `≤ |g| · intBound W`. -/
noncomputable def groundCluster (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) : Submodule ℂ (FermionicFock d) :=
  ⨆ (k : Fin (Module.finrank ℂ (FermionicFock d)))
    (_ : evolEig (hamInt_isSymmetric d lam W g) k ≤ |g| * intBound d W),
    ℂ ∙ (evolBasis (hamInt_isSymmetric d lam W g)) k

/-- The high cluster of `hamInt_gap_persistence` as a subspace: the span of
the eigenvectors of `hamInt` whose eigenvalue is `≥ Δ / 2`. -/
noncomputable def highCluster (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (Δ : ℝ) :
    Submodule ℂ (FermionicFock d) :=
  ⨆ (k : Fin (Module.finrank ℂ (FermionicFock d)))
    (_ : Δ / 2 ≤ evolEig (hamInt_isSymmetric d lam W g) k),
    ℂ ∙ (evolBasis (hamInt_isSymmetric d lam W g)) k

/-- The evolution of the interacting Hamiltonian: on any eigenvector of
`hamInt`, it acts by the eigenphase. -/
theorem evolOp_hamInt_apply_mem_eigenspace (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (t : ℝ) {ψ : FermionicFock d}
    {μ : ℂ} (hψ : ψ ∈ Module.End.eigenspace (hamInt d lam W g) μ) :
    evolOp (hamInt_isSymmetric d lam W g) t ψ = evolPhase μ.re t • ψ :=
  evolOp_apply_mem_eigenspace _ t hψ

/-- The evolution of the diagonal density Hamiltonian `hamiltonianDens`:
on any eigenvector, it acts by the eigenphase. -/
theorem evolOp_hamiltonianDens_apply_mem_eigenspace (lam : Fin d → ℝ)
    (U : Fin d → Fin d → ℝ) (g : ℝ) (t : ℝ) {ψ : FermionicFock d} {μ : ℂ}
    (hψ : ψ ∈ Module.End.eigenspace (hamiltonianDens d lam U g) μ) :
    evolOp (hamiltonianDens_isSymmetric d lam U g) t ψ = evolPhase μ.re t • ψ :=
  evolOp_apply_mem_eigenspace _ t hψ

/-- The ground cluster is invariant under the interacting evolution. -/
theorem groundCluster_invariant (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (t : ℝ) :
    (groundCluster d lam W g).map (evolOp (hamInt_isSymmetric d lam W g) t)
      ≤ groundCluster d lam W g :=
  evolOp_map_cluster_le _ t _

/-- The high cluster is invariant under the interacting evolution. -/
theorem highCluster_invariant (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (Δ : ℝ) (t : ℝ) :
    (highCluster d lam W g Δ).map (evolOp (hamInt_isSymmetric d lam W g) t)
      ≤ highCluster d lam W g Δ :=
  evolOp_map_cluster_le _ t _

/-- Under the hypotheses of `hamInt_gap_persistence`, the two clusters cover
the whole space and the ground cluster is nontrivial: the spectral dichotomy
of the gap-persistence theorem is a decomposition into two
`U(t)`-invariant subspaces (with the invariance proved above). -/
theorem hamInt_clusters_cover_and_nontrivial (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (hthr : 2 * |g| * intBound d W ≤ Δ / 4) :
    groundCluster d lam W g ⊔ highCluster d lam W g Δ = ⊤
      ∧ groundCluster d lam W g ≠ ⊥ := by
  obtain ⟨E₀, hE₀eig, hE₀bound, hdich⟩ :=
    hamInt_gap_persistence d lam W g Δ hΔ hlam hgap hthr
  have hb0 : ∀ k, (evolBasis (hamInt_isSymmetric d lam W g)) k ≠ 0 := by
    intro k h0
    have h1 : ‖(evolBasis (hamInt_isSymmetric d lam W g)) k‖ = 1 :=
      (evolBasis (hamInt_isSymmetric d lam W g)).orthonormal.1 k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hbk : ∀ k, (evolBasis (hamInt_isSymmetric d lam W g)) k
      ∈ groundCluster d lam W g ⊔ highCluster d lam W g Δ := by
    intro k
    have heig : hamInt d lam W g ((evolBasis (hamInt_isSymmetric d lam W g)) k)
        = (evolEig (hamInt_isSymmetric d lam W g) k : ℂ)
          • (evolBasis (hamInt_isSymmetric d lam W g)) k :=
      evolBasis_apply_eig _ k
    rcases hdich (hb0 k) heig with h | h
    · have hmem : (evolBasis (hamInt_isSymmetric d lam W g)) k
          ∈ groundCluster d lam W g := by
        apply Submodule.mem_iSup_of_mem k
        apply Submodule.mem_iSup_of_mem (show evolEig (hamInt_isSymmetric d lam W g) k
            ≤ |g| * intBound d W by
          have hh := h
          rwa [Complex.ofReal_re] at hh)
        exact Submodule.mem_span_singleton_self _
      exact Submodule.mem_sup_left hmem
    · have hmem : (evolBasis (hamInt_isSymmetric d lam W g)) k
          ∈ highCluster d lam W g Δ := by
        apply Submodule.mem_iSup_of_mem k
        apply Submodule.mem_iSup_of_mem (show Δ / 2
            ≤ evolEig (hamInt_isSymmetric d lam W g) k by
          have hh := h
          rwa [Complex.ofReal_re] at hh)
        exact Submodule.mem_span_singleton_self _
      exact Submodule.mem_sup_right hmem
  refine ⟨?_, ?_⟩
  · apply le_antisymm le_top
    intro x _
    rw [← sum_repr_ofLp (hamInt_isSymmetric d lam W g) x]
    apply Submodule.sum_mem
    intro k _
    apply Submodule.smul_mem
    exact hbk k
  · obtain ⟨ψ₀, hψ₀mem, hψ₀ne⟩ := hE₀eig.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hψ₀mem
    obtain ⟨k, hk⟩ : ∃ k, ((evolBasis (hamInt_isSymmetric d lam W g)).repr ψ₀).ofLp k
        ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hψ₀ne
      rw [← sum_repr_ofLp (hamInt_isSymmetric d lam W g) ψ₀]
      simp [hcon]
    have hcoord : (evolEig (hamInt_isSymmetric d lam W g) k : ℂ)
          * ((evolBasis (hamInt_isSymmetric d lam W g)).repr ψ₀).ofLp k
        = (E₀ : ℂ) * ((evolBasis (hamInt_isSymmetric d lam W g)).repr ψ₀).ofLp k := by
      have h1 := evolBasis_repr_T (hamInt_isSymmetric d lam W g) ψ₀ k
      rw [hψ₀mem] at h1
      simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at h1
      exact h1.symm
    have hEk : evolEig (hamInt_isSymmetric d lam W g) k = E₀ := by
      have h5 : (evolEig (hamInt_isSymmetric d lam W g) k : ℂ) = (E₀ : ℂ) :=
        mul_right_cancel₀ hk hcoord
      exact Complex.ofReal_inj.mp h5
    intro hbot
    have hbmem : (evolBasis (hamInt_isSymmetric d lam W g)) k
        ∈ groundCluster d lam W g := by
      apply Submodule.mem_iSup_of_mem k
      apply Submodule.mem_iSup_of_mem (show evolEig (hamInt_isSymmetric d lam W g) k
          ≤ |g| * intBound d W by
        rw [hEk]
        exact le_trans (le_abs_self E₀) hE₀bound)
      exact Submodule.mem_span_singleton_self _
    rw [hbot] at hbmem
    exact hb0 k ((Submodule.mem_bot ℂ).mp hbmem)

end HamInt

/-! ## §9. Axiom audit

The headline theorems of this module, checked in the fermionic environment
only. Expected: `propext`, `Classical.choice`, `Quot.sound` — and nothing else. -/

#print axioms evolOp_add
#print axioms evolOp_adjoint
#print axioms evolUnitary_apply
#print axioms hasDerivAt_evolOp_apply
#print axioms evolOp_unique
#print axioms heisenberg_equation
#print axioms picture_equiv
#print axioms evolOp_hamInt_apply_mem_eigenspace
#print axioms groundCluster_invariant
#print axioms hamInt_clusters_cover_and_nontrivial
