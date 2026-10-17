import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ThetLogos.SecondQuantDGamma

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.FermionicInteraction — Pitch 3, Campaign 1: the first interacting Hamiltonian

**Mandatory honesty clause (Pitch 3 scoping §6, adapted to this fermionic module
with identical content).** *Interacting Hamiltonian at finite modes: H = H₀ + gV
with V a Wick polynomial in the corpus's creation/annihilation operators. The gap
statements are in the eigenvalue sense of Rungs 9–10 (fermions: finite-dimensional).
This is matter self-interaction only — no gauge field, no continuum, no
Poincaré — and is not the interacting Yang–Mills mass gap.*

This module builds Campaign 1 of the Pitch 3 scoping
(`whitepaper/pitch-3-interaction-scoping-DRAFT-2026-10-16.md`, Tasks A0–A3):

- **A0 (§1).** Per-mode number operators `numMode i = a†ᵢ ∘ aᵢ`, their commutation,
  and the corpus's first operator-norm bounds: `‖a†ᵢ‖, ‖aᵢ‖ ≤ 1` in pointwise form
  (`‖a†ᵢ x‖ ≤ ‖x‖`) and as continuous-linear-map operator norms.
- **A1 (§2).** The density–density exhibit `densityInt U = ∑_{i<j} Uᵢⱼ nᵢnⱼ`: a genuine
  quartic Wick polynomial (normal form as a sum of `a†∘a∘a†∘a` monomials), diagonal in
  the occupation basis with explicit eigenvalues, self-adjoint, with an exact gap
  theorem; the **not-a-dΓ certificate** `densityInt_not_dgamma` — the corpus's first
  proof that one of its own operators is *not* a one-particle (free) lift; and the
  diagonal interacting Hamiltonian `hamiltonianDens`, recovering `freeHamiltonian`
  at `g = 0`.
- **A2 (§3).** The general quartic calculus: normal-ordered monomials `wickMono i j k l`,
  their basis action (at most one output basis vector, coefficient of norm `≤ 1`),
  the inner-product adjoint of a monomial and of the general quartic `wickQuartic W`,
  the self-adjoint symmetrization `intOp W`, and its coefficient/row-sum bounds in
  the occupation basis (the Gershgorin-ready estimates).
- **A3 (§§4–5).** The general interacting Hamiltonian `hamInt = H₀ + g • intOp W`:
  self-adjointness (Hermiticity), its matrix in the occupation basis, the
  Gershgorin transport of eigenvalues (the Weyl substitute — Mathlib has no Weyl
  perturbation inequalities; `Matrix.eigenvalue_mem_ball` plus the corpus's
  coefficient dialect does the work), and the **gap persistence theorem**: for
  `2|g|·intBound ≤ Δ/4`, the ground eigenvalue stays in the ball of radius
  `2|g|·intBound` about `0`, no eigenvalue lies in `(2|g|·intBound, Δ − 2|g|·intBound)`,
  an interval of length `≥ Δ/2`.

Everything is in the eigenvalue sense of Rungs 9–10: eigenvalue statements are
about eigenvectors of the operator (equivalently, coefficients on the occupation
basis), never about an abstract spectrum. Fermions only; `FermionicFock d` is
finite-dimensional (dimension `2^d`), so `hamInt` is a finite Hermitian matrix
in operator clothing.
-/

variable (d : ℕ)

/-- The eigenvalue of the free Hamiltonian on the configuration `S` (a real number). -/
noncomputable def freeEig (lam : Fin d → ℝ) (S : Finset (Fin d)) : ℝ :=
  ∑ i ∈ S, lam i

-- ============================================================================
-- §0. Coordinate helpers
-- ============================================================================

/-- Coordinates of a finite sum over an arbitrary finite index type. -/
theorem ofLp_sum_gen {ι : Type*} [Fintype ι] (v : ι → FermionicFock d)
    (T : Finset (Fin d)) :
    (∑ i, v i).ofLp T = ∑ i, (v i).ofLp T := by
  show ((fockEquiv d).symm (∑ i, v i)) T = ∑ i, ((fockEquiv d).symm (v i)) T
  rw [map_sum, Finset.sum_apply]

/-- The inner product against a basis vector reads off the coordinate. -/
theorem inner_fockBasis_left (S : Finset (Fin d)) (y : FermionicFock d) :
    ⟪fockBasis d S, y⟫_ℂ = y.ofLp S := by
  rw [PiLp.inner_apply, Finset.sum_eq_single S]
  · rw [RCLike.inner_apply, fockBasis_ofLp, if_pos rfl, map_one, mul_one]
  · intro T _ hTS
    rw [RCLike.inner_apply, fockBasis_ofLp, if_neg hTS, map_zero, mul_zero]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- The inner product with a basis vector on the right is the conjugate coordinate. -/
theorem inner_fockBasis_right (y : FermionicFock d) (S : Finset (Fin d)) :
    ⟪y, fockBasis d S⟫_ℂ = (starRingEnd ℂ) (y.ofLp S) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single S]
  · rw [RCLike.inner_apply, fockBasis_ofLp, if_pos rfl, one_mul]
  · intro T _ hTS
    rw [RCLike.inner_apply, fockBasis_ofLp, if_neg hTS, zero_mul]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- Two operators agreeing on the occupation basis are equal. -/
theorem end_ext_basis {f g : Module.End ℂ (FermionicFock d)}
    (h : ∀ S, f (fockBasis d S) = g (fockBasis d S)) : f = g := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [fock_expand d x]
  conv_rhs => rw [fock_expand d x]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun S _ => by rw [map_smul, map_smul, h S])

/-- The Koszul sign has norm `1`. -/
theorem norm_sgn (i : Fin d) (S : Finset (Fin d)) : ‖sgn d i S‖ = 1 := by
  simp [sgn]

-- ============================================================================
-- §1. Task A0 — per-mode number operators and the first norm bounds
-- ============================================================================

/-- The per-mode number operator `nᵢ = a†ᵢ ∘ aᵢ`. -/
noncomputable def numMode (i : Fin d) : Module.End ℂ (FermionicFock d) :=
  (adag d i).comp (ann d i)

/-- `nᵢ` is diagonal on the occupation basis with eigenvalue the indicator of `i ∈ S`. -/
theorem numMode_basis (i : Fin d) (S : Finset (Fin d)) :
    numMode d i (fockBasis d S)
      = (if i ∈ S then (1 : ℂ) else 0) • fockBasis d S :=
  numberOp_basis d i S

/-- Per-mode number operators commute (they are simultaneously diagonal). -/
theorem numMode_comm (i j : Fin d) :
    (numMode d i).comp (numMode d j) = (numMode d j).comp (numMode d i) := by
  apply end_ext_basis
  intro S
  rw [LinearMap.comp_apply, LinearMap.comp_apply, numMode_basis, numMode_basis,
    map_smul, map_smul, numMode_basis, numMode_basis, smul_smul, smul_smul, mul_comm]

/-- **Pointwise norm bound for creation (T1): `‖a†ᵢ x‖ ≤ ‖x‖`.**
The corpus's first operator-norm estimate; proved from the coordinate formula
by reindexing the occupied configurations via `erase i`. -/
theorem norm_adag_apply_le (i : Fin d) (x : FermionicFock d) :
    ‖adag d i x‖ ≤ ‖x‖ := by
  have hsum : (∑ T : Finset (Fin d), ‖(adag d i x).ofLp T‖ ^ 2)
      ≤ ∑ T : Finset (Fin d), ‖x.ofLp T‖ ^ 2 := by
    have h1 : (∑ T : Finset (Fin d), ‖(adag d i x).ofLp T‖ ^ 2)
        = ∑ T : Finset (Fin d), (if i ∈ T then ‖x.ofLp (T.erase i)‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [adag_apply]
      by_cases hT : i ∈ T
      · rw [if_pos hT, if_pos hT, norm_mul, norm_sgn, one_mul]
      · rw [if_neg hT, if_neg hT, norm_zero]
        norm_num
    rw [h1, ← Finset.sum_filter]
    calc ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin d) => i ∈ T), ‖x.ofLp (T.erase i)‖ ^ 2
        = ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin d) => i ∉ U), ‖x.ofLp U‖ ^ 2 := by
          apply Finset.sum_bij (fun T _ => T.erase i)
          · intro T hT
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
            exact Finset.notMem_erase i T
          · intro T₁ h₁ T₂ h₂ h
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
            have e1 : insert i (T₁.erase i) = T₁ := Finset.insert_erase h₁
            have e2 : insert i (T₂.erase i) = T₂ := Finset.insert_erase h₂
            rw [← e1, ← e2, h]
          · intro U hU
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
            exact ⟨insert i U, Finset.mem_insert_self i U, Finset.erase_insert hU⟩
          · intro T _
            rfl
      _ ≤ ∑ U : Finset (Fin d), ‖x.ofLp U‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun U _ _ => sq_nonneg _)
  have h2 : ‖adag d i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    exact hsum
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg x)
  rwa [abs_norm] at habs

/-- **Pointwise norm bound for annihilation (T1): `‖aᵢ x‖ ≤ ‖x‖`.** -/
theorem norm_ann_apply_le (i : Fin d) (x : FermionicFock d) :
    ‖ann d i x‖ ≤ ‖x‖ := by
  have hsum : (∑ T : Finset (Fin d), ‖(ann d i x).ofLp T‖ ^ 2)
      ≤ ∑ T : Finset (Fin d), ‖x.ofLp T‖ ^ 2 := by
    have h1 : (∑ T : Finset (Fin d), ‖(ann d i x).ofLp T‖ ^ 2)
        = ∑ T : Finset (Fin d), (if i ∉ T then ‖x.ofLp (insert i T)‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [ann_apply]
      by_cases hT : i ∉ T
      · rw [if_pos hT, if_pos hT, norm_mul, norm_sgn, one_mul]
      · rw [if_neg hT, if_neg hT, norm_zero]
        norm_num
    rw [h1, ← Finset.sum_filter]
    calc ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin d) => i ∉ T), ‖x.ofLp (insert i T)‖ ^ 2
        = ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin d) => i ∈ U), ‖x.ofLp U‖ ^ 2 := by
          apply Finset.sum_bij (fun T _ => insert i T)
          · intro T hT
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
            exact Finset.mem_insert_self i T
          · intro T₁ h₁ T₂ h₂ h
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
            have e1 : (insert i T₁).erase i = T₁ := Finset.erase_insert h₁
            have e2 : (insert i T₂).erase i = T₂ := Finset.erase_insert h₂
            rw [← e1, ← e2, h]
          · intro U hU
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
            exact ⟨U.erase i, Finset.notMem_erase i U, Finset.insert_erase hU⟩
          · intro T _
            rfl
      _ ≤ ∑ U : Finset (Fin d), ‖x.ofLp U‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun U _ _ => sq_nonneg _)
  have h2 : ‖ann d i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    exact hsum
  have habs := abs_le_of_sq_le_sq h2 (norm_nonneg x)
  rwa [abs_norm] at habs

/-- Operator norm of creation, as a continuous linear map: `‖a†ᵢ‖ ≤ 1` (T1). -/
theorem opNorm_adag_le (i : Fin d) :
    ‖LinearMap.toContinuousLinearMap (adag d i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  show ‖(adag d i) x‖ ≤ 1 * ‖x‖
  simpa using norm_adag_apply_le d i x

/-- Operator norm of annihilation, as a continuous linear map: `‖aᵢ‖ ≤ 1` (T1). -/
theorem opNorm_ann_le (i : Fin d) :
    ‖LinearMap.toContinuousLinearMap (ann d i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  show ‖(ann d i) x‖ ≤ 1 * ‖x‖
  simpa using norm_ann_apply_le d i x

-- ============================================================================
-- §2. Task A1 — the density–density exhibit and the not-a-dΓ certificate
-- ============================================================================

/-- Coordinate formula for an operator diagonal in the occupation basis. -/
theorem diagOp_ofLp {T : Module.End ℂ (FermionicFock d)} {r : Finset (Fin d) → ℝ}
    (hT : ∀ S, T (fockBasis d S) = (r S : ℂ) • fockBasis d S)
    (x : FermionicFock d) (U : Finset (Fin d)) :
    (T x).ofLp U = (r U : ℂ) * x.ofLp U := by
  conv_lhs => rw [fock_expand d x]
  rw [map_sum, ofLp_sum_gen, Finset.sum_eq_single U]
  · simp only [map_smul, hT, PiLp.smul_apply, smul_eq_mul, fockBasis_ofLp, ite_true,
      mul_one]
    ring
  · intro S _ hSU
    simp only [map_smul, hT, PiLp.smul_apply, smul_eq_mul, fockBasis_ofLp,
      if_neg (Ne.symm hSU), mul_zero]
  · intro hU
    exact absurd (Finset.mem_univ U) hU

/-- An operator diagonal in the occupation basis with real eigenvalues is symmetric. -/
theorem diagOp_isSymmetric {T : Module.End ℂ (FermionicFock d)} {r : Finset (Fin d) → ℝ}
    (hT : ∀ S, T (fockBasis d S) = (r S : ℂ) • fockBasis d S) :
    T.IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [RCLike.inner_apply, RCLike.inner_apply, diagOp_ofLp d hT x U, diagOp_ofLp d hT y U]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Eigenvalue extraction for a diagonal operator (Rungs 9–10 dialect). -/
theorem diagOp_eigenvalue {T : Module.End ℂ (FermionicFock d)} {r : Finset (Fin d) → ℝ}
    (hT : ∀ S, T (fockBasis d S) = (r S : ℂ) • fockBasis d S)
    {ψ : FermionicFock d} (hψ : ψ ≠ 0) {μ : ℂ} (hμ : T ψ = μ • ψ) :
    ∃ S, μ = (r S : ℂ) := by
  obtain ⟨S, hS⟩ : ∃ S, ψ.ofLp S ≠ 0 := by
    by_contra h
    push_neg at h
    apply hψ
    apply PiLp.ext
    intro T
    rw [h T]
    rfl
  refine ⟨S, ?_⟩
  have hcoord := congrArg (fun z : FermionicFock d => z.ofLp S) hμ
  rw [diagOp_ofLp d hT ψ S, PiLp.smul_apply, smul_eq_mul] at hcoord
  exact (mul_right_cancel₀ hS hcoord).symm

/-- The density–density eigenvalue on configuration `S`: the sum of `U i j` over
occupied pairs `i < j`. -/
noncomputable def densEig (U : Fin d → Fin d → ℝ) (S : Finset (Fin d)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, if i < j then U i j else 0

/-- The density–density interaction `V = ∑_{i<j} Uᵢⱼ nᵢ nⱼ`, a quartic Wick
polynomial in `adag`/`ann` (two creation and two annihilation operators per term,
in normal `a†a` pair form). -/
noncomputable def densityInt (U : Fin d → Fin d → ℝ) : Module.End ℂ (FermionicFock d) :=
  ∑ i : Fin d, ∑ j : Fin d,
    (if i < j then (U i j : ℂ) else 0) • ((numMode d i).comp (numMode d j))

/-- `densityInt` is diagonal in the occupation basis with eigenvalue `densEig`. -/
theorem densityInt_basis (U : Fin d → Fin d → ℝ) (S : Finset (Fin d)) :
    densityInt d U (fockBasis d S) = (densEig d U S : ℂ) • fockBasis d S := by
  have hterm : ∀ i j : Fin d,
      ((if i < j then (U i j : ℂ) else 0) • ((numMode d i).comp (numMode d j)))
          (fockBasis d S)
        = ((if i < j then (U i j : ℂ) else 0)
            * (if i ∈ S then (1 : ℂ) else 0) * (if j ∈ S then (1 : ℂ) else 0))
            • fockBasis d S := by
    intro i j
    rw [LinearMap.smul_apply, LinearMap.comp_apply, numMode_basis, map_smul, numMode_basis,
      smul_smul, smul_smul]
    congr 1
    ring
  have step1 : ∀ i : Fin d,
      (∑ j : Fin d, (if i < j then (U i j : ℂ) else 0) • ((numMode d i).comp (numMode d j)))
          (fockBasis d S)
        = (∑ j : Fin d, (if i < j then (U i j : ℂ) else 0)
            * (if i ∈ S then (1 : ℂ) else 0) * (if j ∈ S then (1 : ℂ) else 0))
            • fockBasis d S := by
    intro i
    rw [LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)
  have e1 : (densEig d U S : ℂ)
      = ∑ i ∈ S, ∑ j ∈ S, (if i < j then (U i j : ℂ) else 0) := by
    show ((∑ i ∈ S, ∑ j ∈ S, if i < j then U i j else 0 : ℝ) : ℂ) = _
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i < j <;> simp [h]
  have hscalar : (∑ i : Fin d, ∑ j : Fin d,
        (if i < j then (U i j : ℂ) else 0) * (if i ∈ S then (1 : ℂ) else 0)
          * (if j ∈ S then (1 : ℂ) else 0))
      = ∑ i ∈ S, ∑ j ∈ S, (if i < j then (U i j : ℂ) else 0) := by
    refine (Finset.sum_subset (Finset.subset_univ S) (fun i _ hiS => ?_)).symm.trans ?_
    · refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg hiS, mul_zero, zero_mul]
    · refine Finset.sum_congr rfl (fun i hiS => ?_)
      refine (Finset.sum_subset (Finset.subset_univ S) (fun j _ hjS => ?_)).symm.trans ?_
      · rw [if_neg hjS, mul_zero]
      · refine Finset.sum_congr rfl (fun j hjS => ?_)
        rw [if_pos hiS, if_pos hjS, mul_one, mul_one]
  calc densityInt d U (fockBasis d S)
      = ∑ i : Fin d, (∑ j : Fin d, (if i < j then (U i j : ℂ) else 0)
          • ((numMode d i).comp (numMode d j))) (fockBasis d S) := by
        unfold densityInt
        rw [LinearMap.sum_apply]
    _ = ∑ i : Fin d, ((∑ j : Fin d, (if i < j then (U i j : ℂ) else 0)
          * (if i ∈ S then (1 : ℂ) else 0) * (if j ∈ S then (1 : ℂ) else 0))
          • fockBasis d S) :=
        Finset.sum_congr rfl (fun i _ => step1 i)
    _ = (∑ i : Fin d, ∑ j : Fin d, (if i < j then (U i j : ℂ) else 0)
          * (if i ∈ S then (1 : ℂ) else 0) * (if j ∈ S then (1 : ℂ) else 0))
          • fockBasis d S := by
        rw [Finset.sum_smul]
    _ = (densEig d U S : ℂ) • fockBasis d S := by
        rw [hscalar, ← e1]

/-- Quartic normal form: `densityInt` is a sum of four-fold monomials
`a†ᵢ ∘ aᵢ ∘ a†ⱼ ∘ aⱼ` in the creation/annihilation operators — the certificate
that it is a Wick polynomial, not a definition trick. -/
theorem densityInt_eq_quartic (U : Fin d → Fin d → ℝ) :
    densityInt d U
      = ∑ i : Fin d, ∑ j : Fin d, (if i < j then (U i j : ℂ) else 0)
          • ((adag d i).comp ((ann d i).comp ((adag d j).comp (ann d j)))) := by
  unfold densityInt numMode
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [LinearMap.comp_assoc]

/-- `densityInt` is self-adjoint (symmetric). -/
theorem densityInt_isSymmetric (U : Fin d → Fin d → ℝ) :
    (densityInt d U).IsSymmetric :=
  diagOp_isSymmetric d (densityInt_basis d U)

/-- The diagonal coefficient of a `dΓ` lift on configuration `S` is the sum of the
diagonal entries `M i i` over occupied modes. This additivity over occupied modes
is exactly what a quartic interaction violates (see `densityInt_not_dgamma`). -/
theorem dgamma_diag_coeff (M : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) :
    (dgamma d M (fockBasis d S)).ofLp S = ∑ i ∈ S, M i i := by
  have hterm : ∀ i j : Fin d,
      ⟪fockBasis d S, ((M i j) • ((adag d i).comp (ann d j))) (fockBasis d S)⟫_ℂ
        = if i ∈ S ∧ j = i then M i i else 0 := by
    intro i j
    rw [LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply,
      ← ann_adjoint d i (fockBasis d S) (ann d j (fockBasis d S)), ann_basis, ann_basis]
    by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S
    · rw [if_neg (not_not.mpr hiS), if_neg (not_not.mpr hjS), inner_smul_left,
        inner_smul_right, starRingEnd_sgn, fockBasis_inner]
      by_cases hij : i = j
      · subst hij
        simp [sgn_sq, hiS]
      · have herase : S.erase i ≠ S.erase j := by
          intro h
          have hmem : j ∈ S.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩
          rw [h] at hmem
          exact (Finset.notMem_erase j S) hmem
        have hne : ¬ (j = i) := fun h => hij h.symm
        simp [herase, hne, hiS, hjS]
    · rw [if_neg (not_not.mpr hiS), if_pos hjS, inner_zero_right, mul_zero]
      split_ifs with hh
      · exact absurd (hh.2.symm ▸ hiS) hjS
      · rfl
    · rw [if_pos hiS, inner_zero_left, mul_zero]
      split_ifs with hh
      · exact absurd hh.1 hiS
      · rfl
    · rw [if_pos hiS, inner_zero_left, mul_zero]
      split_ifs with hh
      · exact absurd hh.1 hiS
      · rfl
  have hcollapse : ∀ i : Fin d,
      (∑ j : Fin d, (if i ∈ S ∧ j = i then M i i else 0)) = if i ∈ S then M i i else 0 := by
    intro i
    refine (Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj h.2))
      (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
    by_cases hiS : i ∈ S <;> simp [hiS]
  have hfil : Finset.univ.filter (fun i : Fin d => i ∈ S) = S := by
    ext i
    simp
  have step1 : (∑ i : Fin d, ⟪fockBasis d S,
        (∑ j : Fin d, (M i j) • ((adag d i).comp (ann d j))) (fockBasis d S)⟫_ℂ)
      = ∑ i : Fin d, ∑ j : Fin d, (if i ∈ S ∧ j = i then M i i else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.sum_apply, inner_sum]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)
  have step2 : (∑ i : Fin d, ∑ j : Fin d, (if i ∈ S ∧ j = i then M i i else 0))
      = ∑ i ∈ S, M i i := by
    rw [Finset.sum_congr rfl (fun i _ => hcollapse i), ← Finset.sum_filter, hfil]
  rw [← inner_fockBasis_left]
  unfold dgamma
  rw [LinearMap.sum_apply, inner_sum]
  exact step1.trans step2

/-- **The not-a-dΓ certificate (T1).** For `U a b ≠ 0` with `a < b`, the density–density
interaction `densityInt U` is **not** `dgamma d M` for any one-particle matrix `M`:
its eigenvalue on `{a, b}` violates the additivity over occupied modes that every
`dΓ` lift satisfies. The corpus's first proof that one of its own operators is
genuinely interacting rather than a relabeled free operator. -/
theorem densityInt_not_dgamma (U : Fin d → Fin d → ℝ) {a b : Fin d} (hab : a < b)
    (hU : U a b ≠ 0) (M : Matrix (Fin d) (Fin d) ℂ) :
    densityInt d U ≠ dgamma d M := by
  intro hcon
  have habne : a ≠ b := ne_of_lt hab
  have key : ∀ S : Finset (Fin d), (densEig d U S : ℂ) = ∑ i ∈ S, M i i := by
    intro S
    have h1 : (densityInt d U (fockBasis d S)).ofLp S
        = (dgamma d M (fockBasis d S)).ofLp S := by rw [hcon]
    rw [densityInt_basis, PiLp.smul_apply, smul_eq_mul, fockBasis_ofLp, if_pos rfl,
      mul_one, dgamma_diag_coeff] at h1
    exact h1
  have ea : densEig d U {a} = 0 := by
    show (∑ i ∈ ({a} : Finset (Fin d)), ∑ j ∈ ({a} : Finset (Fin d)),
      if i < j then U i j else 0) = 0
    rw [Finset.sum_singleton, Finset.sum_singleton, if_neg (lt_irrefl a)]
  have eb : densEig d U {b} = 0 := by
    show (∑ i ∈ ({b} : Finset (Fin d)), ∑ j ∈ ({b} : Finset (Fin d)),
      if i < j then U i j else 0) = 0
    rw [Finset.sum_singleton, Finset.sum_singleton, if_neg (lt_irrefl b)]
  have eab : densEig d U {a, b} = U a b := by
    show (∑ i ∈ ({a, b} : Finset (Fin d)), ∑ j ∈ ({a, b} : Finset (Fin d)),
      if i < j then U i j else 0) = U a b
    rw [Finset.sum_insert (by simp [habne]), Finset.sum_singleton,
      Finset.sum_insert (by simp [habne]), Finset.sum_singleton, if_neg (lt_irrefl a),
      if_pos hab, Finset.sum_insert (by simp [habne]), Finset.sum_singleton,
      if_neg (not_lt.mpr (le_of_lt hab)), if_neg (lt_irrefl b)]
    simp
  have k1 : (∑ i ∈ ({a, b} : Finset (Fin d)), M i i) = M a a + M b b := by
    rw [Finset.sum_insert (by simp [habne]), Finset.sum_singleton]
  have k2 : (∑ i ∈ ({a} : Finset (Fin d)), M i i) = M a a := Finset.sum_singleton _ _
  have k3 : (∑ i ∈ ({b} : Finset (Fin d)), M i i) = M b b := Finset.sum_singleton _ _
  have h1 := key {a, b}
  have h2 := key {a}
  have h3 := key {b}
  rw [eab] at h1
  rw [ea, Complex.ofReal_zero, k2] at h2
  rw [eb, Complex.ofReal_zero, k3] at h3
  rw [k1, ← h2, ← h3, add_zero] at h1
  exact hU (Complex.ofReal_eq_zero.mp h1)

/-- The density–density interaction is not a `dΓ` lift, in the `d ≥ 2` form:
take `a = ⟨0, ·⟩ < b = ⟨1, ·⟩` and `U a b ≠ 0`. -/
theorem densityInt_not_dgamma_two (hd : 2 ≤ d) (U : Fin d → Fin d → ℝ)
    (hU : U ⟨0, by omega⟩ ⟨1, hd⟩ ≠ 0) (M : Matrix (Fin d) (Fin d) ℂ) :
    densityInt d U ≠ dgamma d M :=
  densityInt_not_dgamma d U (a := ⟨0, by omega⟩) (b := ⟨1, hd⟩)
    (by rw [Fin.mk_lt_mk]; norm_num) hU M

/-- The diagonal interacting Hamiltonian `H(g) = H₀ + g • densityInt U`. -/
noncomputable def hamiltonianDens (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ) :
    Module.End ℂ (FermionicFock d) :=
  freeHamiltonian d lam + (g : ℂ) • densityInt d U

/-- The eigenvalue of `hamiltonianDens` on configuration `S`. -/
noncomputable def densHamEig (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ)
    (S : Finset (Fin d)) : ℝ :=
  freeEig d lam S + g * densEig d U S

/-- `hamiltonianDens` is diagonal in the occupation basis. -/
theorem hamiltonianDens_basis (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ)
    (S : Finset (Fin d)) :
    hamiltonianDens d lam U g (fockBasis d S)
      = (densHamEig d lam U g S : ℂ) • fockBasis d S := by
  unfold hamiltonianDens
  rw [LinearMap.add_apply, LinearMap.smul_apply, freeHamiltonian_basis, densityInt_basis,
    smul_smul, ← add_smul]
  congr 1
  show ((∑ i ∈ S, lam i : ℝ) : ℂ) + (g : ℂ) * (densEig d U S : ℂ)
    = (((∑ i ∈ S, lam i) + g * densEig d U S : ℝ) : ℂ)
  push_cast
  ring

/-- `hamiltonianDens` is self-adjoint (symmetric). -/
theorem hamiltonianDens_isSymmetric (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ) :
    (hamiltonianDens d lam U g).IsSymmetric :=
  diagOp_isSymmetric d (hamiltonianDens_basis d lam U g)

/-- At `g = 0`, `hamiltonianDens` recovers the free Hamiltonian. -/
theorem hamiltonianDens_zero (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) :
    hamiltonianDens d lam U 0 = freeHamiltonian d lam := by
  unfold hamiltonianDens
  simp

/-- The density eigenvalue is nonnegative for nonnegative couplings. -/
theorem densEig_nonneg (U : Fin d → Fin d → ℝ) (hU : ∀ i j, 0 ≤ U i j)
    (S : Finset (Fin d)) :
    0 ≤ densEig d U S := by
  show 0 ≤ ∑ i ∈ S, ∑ j ∈ S, if i < j then U i j else 0
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  split_ifs with h
  · exact hU i j
  · exact le_rfl

/-- The interacting eigenvalue dominates the free one (for `g, U ≥ 0`). -/
theorem densHamEig_ge_freeEig (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ)
    (hg : 0 ≤ g) (hU : ∀ i j, 0 ≤ U i j) (S : Finset (Fin d)) :
    freeEig d lam S ≤ densHamEig d lam U g S := by
  show freeEig d lam S ≤ freeEig d lam S + g * densEig d U S
  exact le_add_of_nonneg_right (mul_nonneg hg (densEig_nonneg d U hU S))

/-- Eigenvalue form of `hamiltonianDens` under the Rung 9 dichotomy hypotheses:
every eigenvalue is a configuration eigenvalue `densHamEig S ≥ 0`, and the free
part obeys the free dichotomy. -/
theorem hamiltonianDens_eigenvalue_form (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ)
    (g : ℝ) (Δ : ℝ) (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (hg : 0 ≤ g) (hU : ∀ i j, 0 ≤ U i j)
    {ψ : FermionicFock d} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamiltonianDens d lam U g ψ = μ • ψ) :
    ∃ S, μ = (densHamEig d lam U g S : ℂ) ∧ 0 ≤ densHamEig d lam U g S
      ∧ ((∑ i ∈ S, lam i) = 0 ∨ Δ ≤ ∑ i ∈ S, lam i) := by
  obtain ⟨S, hS⟩ := diagOp_eigenvalue d (hamiltonianDens_basis d lam U g) hψ hμ
  refine ⟨S, hS, ?_, free_gap_dichotomy d lam Δ hlam hgap S⟩
  show 0 ≤ freeEig d lam S + g * densEig d U S
  exact add_nonneg (Finset.sum_nonneg (fun i _ => hlam i))
    (mul_nonneg hg (densEig_nonneg d U hU S))

/-- **Exact gap for the diagonal exhibit, no-zero-mode form (T1).** If every mode is
gapped (`Δ ≤ lam i` for all `i`, `Δ > 0`), `U ≥ 0`, and `g ≥ 0`, every eigenvalue of
`hamiltonianDens` is `0` (the vacuum configuration) or `≥ Δ`: the free gap persists
exactly, since the interaction only adds nonnegative energy.

(Honesty note: under the weaker Rung 9 dichotomy hypothesis with zero modes
present, the `0 ∨ ≥ Δ` alternative for the *interacting* eigenvalue is false in
general — two zero modes with `U a b > 0` and small `g > 0` give a configuration
eigenvalue `g • U a b ∈ (0, Δ)`. The true statement at that generality is
`hamiltonianDens_eigenvalue_form`: eigenvalues are `≥ 0`, and dominate the free
eigenvalue, so any configuration containing a gapped mode still has eigenvalue
`≥ Δ`.) -/
theorem hamiltonianDens_gap_exact (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) (g : ℝ)
    (Δ : ℝ) (hΔ : 0 < Δ) (hlamΔ : ∀ i, Δ ≤ lam i) (hg : 0 ≤ g)
    (hU : ∀ i j, 0 ≤ U i j)
    {ψ : FermionicFock d} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamiltonianDens d lam U g ψ = μ • ψ) :
    ∃ S, μ = (densHamEig d lam U g S : ℂ)
      ∧ (densHamEig d lam U g S = 0 ∨ Δ ≤ densHamEig d lam U g S) := by
  obtain ⟨S, hSμ, -, -⟩ := hamiltonianDens_eigenvalue_form d lam U g Δ
    (fun i => le_trans hΔ.le (hlamΔ i)) (fun i => Or.inr (hlamΔ i)) hg hU hψ hμ
  refine ⟨S, hSμ, ?_⟩
  by_cases hSe : S = ∅
  · left
    rw [hSe]
    show freeEig d lam ∅ + g * densEig d U ∅ = 0
    simp [freeEig, densEig]
  · right
    obtain ⟨i, hiS⟩ := Finset.nonempty_of_ne_empty hSe
    calc Δ ≤ lam i := hlamΔ i
      _ ≤ freeEig d lam S :=
          Finset.single_le_sum (fun j _ => le_trans hΔ.le (hlamΔ j)) hiS
      _ ≤ densHamEig d lam U g S := densHamEig_ge_freeEig d lam U g hg hU S

/-! ## §3. The general quartic interaction (Task A0/A2)

A general quartic matter self-interaction: an arbitrary coupling tensor
`W i j k l : ℂ`, the Wick monomials `a†ᵢ a†ⱼ aₖ aₗ` (normal-ordered, corpus
conventions), the raw quartic `wickQuartic W`, its adjoint-flip coupling
`adjCoupl W`, and the symmetrized interaction `intOp W = wickQuartic W +
wickQuartic (adjCoupl W)`, self-adjoint by construction. The bounds are the
Gershgorin-ready ones: every matrix coefficient of `intOp W` in the occupation
basis is `≤ intBound W = 2 · ∑ ‖W i j k l‖`, and every row sum is too. -/

/-- Coordinates of a sum: `(x + y).ofLp S = x.ofLp S + y.ofLp S`. -/
theorem ofLp_add_gen (x y : FermionicFock d) (S : Finset (Fin d)) :
    (x + y).ofLp S = x.ofLp S + y.ofLp S := by
  rw [← inner_fockBasis_left, ← inner_fockBasis_left, ← inner_fockBasis_left,
    inner_add_right]

/-- A normal-ordered quartic Wick monomial `a†ᵢ a†ⱼ aₖ aₗ` (rightmost factor
acts first), in the corpus's creation/annihilation operators. -/
noncomputable def wickMono (i j k l : Fin d) : Module.End ℂ (FermionicFock d) :=
  (adag d i).comp ((adag d j).comp ((ann d k).comp (ann d l)))

/-- Basis-monomial package: `f` sends every occupation basis vector to a scalar
multiple of a single basis vector, the scalars have norm `≤ 1`, and the
configuration map is injective on the support of the scalars. Creation,
annihilation, and hence every Wick monomial carry this package, and it is
exactly what makes both the coefficient bound and the row-sum bound work. -/
def IsBasisMono (f : Module.End ℂ (FermionicFock d)) : Prop :=
  ∃ (φ : Finset (Fin d) → Finset (Fin d)) (c : Finset (Fin d) → ℂ),
    (∀ S, f (fockBasis d S) = (c S) • fockBasis d (φ S))
    ∧ (∀ S, ‖c S‖ ≤ 1)
    ∧ (∀ S S', c S ≠ 0 → c S' ≠ 0 → φ S = φ S' → S = S')

/-- Creation is a basis monomial. -/
theorem isBasisMono_adag (i : Fin d) : IsBasisMono d (adag d i) := by
  refine ⟨fun S => insert i S, fun S => if i ∈ S then 0 else sgn d i S, ?_, ?_, ?_⟩
  · dsimp only
    intro S
    rw [adag_basis]
    by_cases hiS : i ∈ S
    · rw [ite_eq_left hiS, ite_eq_left hiS, zero_smul]
    · rw [ite_eq_right hiS, ite_eq_right hiS]
  · dsimp only
    intro S
    by_cases hiS : i ∈ S
    · rw [ite_eq_left hiS, norm_zero]
      exact zero_le_one
    · rw [ite_eq_right hiS]
      exact (norm_sgn d i S).le
  · intro S S' hS hS' hφ
    dsimp only at hS hS' hφ
    have hiS : i ∉ S := fun h => hS (ite_eq_left h)
    have hiS' : i ∉ S' := fun h => hS' (ite_eq_left h)
    calc S = (insert i S).erase i := (Finset.erase_insert hiS).symm
      _ = (insert i S').erase i := by rw [hφ]
      _ = S' := Finset.erase_insert hiS'

/-- Annihilation is a basis monomial. -/
theorem isBasisMono_ann (i : Fin d) : IsBasisMono d (ann d i) := by
  refine ⟨fun S => S.erase i, fun S => if i ∉ S then 0 else sgn d i S, ?_, ?_, ?_⟩
  · dsimp only
    intro S
    rw [ann_basis]
    by_cases hiS : i ∉ S
    · rw [ite_eq_left hiS, ite_eq_left hiS, zero_smul]
    · rw [ite_eq_right hiS, ite_eq_right hiS]
  · dsimp only
    intro S
    by_cases hiS : i ∉ S
    · rw [ite_eq_left hiS, norm_zero]
      exact zero_le_one
    · rw [ite_eq_right hiS]
      exact (norm_sgn d i S).le
  · intro S S' hS hS' hφ
    dsimp only at hS hS' hφ
    have hiS : i ∈ S := by
      by_contra h
      exact hS (ite_eq_left h)
    have hiS' : i ∈ S' := by
      by_contra h
      exact hS' (ite_eq_left h)
    calc S = insert i (S.erase i) := (Finset.insert_erase hiS).symm
      _ = insert i (S'.erase i) := by rw [hφ]
      _ = S' := Finset.insert_erase hiS'

/-- Basis monomials are closed under composition. -/
theorem isBasisMono_comp {f g : Module.End ℂ (FermionicFock d)}
    (hf : IsBasisMono d f) (hg : IsBasisMono d g) :
    IsBasisMono d (f.comp g) := by
  obtain ⟨φ₁, c₁, hact₁, hb₁, hinj₁⟩ := hg
  obtain ⟨φ₂, c₂, hact₂, hb₂, hinj₂⟩ := hf
  refine ⟨fun S => φ₂ (φ₁ S), fun S => c₁ S * c₂ (φ₁ S), ?_, ?_, ?_⟩
  · dsimp only
    intro S
    rw [LinearMap.comp_apply, hact₁ S, map_smul, hact₂ (φ₁ S), smul_smul]
  · dsimp only
    intro S
    calc ‖c₁ S * c₂ (φ₁ S)‖ = ‖c₁ S‖ * ‖c₂ (φ₁ S)‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hb₁ S) (hb₂ (φ₁ S)) (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · intro S S' hS hS' hφ
    dsimp only at hS hS' hφ
    have hc₁ : c₁ S ≠ 0 := fun h => hS (by rw [h, zero_mul])
    have hc₁' : c₁ S' ≠ 0 := fun h => hS' (by rw [h, zero_mul])
    have hc₂ : c₂ (φ₁ S) ≠ 0 := fun h => hS (by rw [h, mul_zero])
    have hc₂' : c₂ (φ₁ S') ≠ 0 := fun h => hS' (by rw [h, mul_zero])
    exact hinj₁ S S' hc₁ hc₁' (hinj₂ (φ₁ S) (φ₁ S') hc₂ hc₂' hφ)

/-- Every Wick monomial is a basis monomial. -/
theorem isBasisMono_wickMono (i j k l : Fin d) : IsBasisMono d (wickMono d i j k l) := by
  unfold wickMono
  exact isBasisMono_comp d (isBasisMono_adag d i)
    (isBasisMono_comp d (isBasisMono_adag d j)
      (isBasisMono_comp d (isBasisMono_ann d k) (isBasisMono_ann d l)))

/-- Coefficient bound for a basis monomial: every matrix entry has norm `≤ 1`. -/
theorem isBasisMono_coeff_bound {f : Module.End ℂ (FermionicFock d)}
    (hf : IsBasisMono d f) (S T : Finset (Fin d)) :
    ‖(f (fockBasis d T)).ofLp S‖ ≤ 1 := by
  obtain ⟨φ, c, hact, hb, -⟩ := hf
  rw [hact T, PiLp.smul_apply, smul_eq_mul, fockBasis_ofLp]
  by_cases h : S = φ T
  · rw [if_pos h, mul_one]
    exact hb T
  · rw [if_neg h, mul_zero, norm_zero]
    exact zero_le_one

/-- Row-sum bound for a basis monomial: at a fixed output configuration, the
coefficients over all input configurations sum to `≤ 1` (injectivity on the
support means at most one input contributes, with coefficient `≤ 1`). -/
theorem isBasisMono_col_sum_le {f : Module.End ℂ (FermionicFock d)}
    (hf : IsBasisMono d f) (T : Finset (Fin d)) :
    ∑ S : Finset (Fin d), ‖(f (fockBasis d S)).ofLp T‖ ≤ 1 := by
  obtain ⟨φ, c, hact, hb, hinj⟩ := hf
  have hterm : ∀ S : Finset (Fin d), ‖(f (fockBasis d S)).ofLp T‖
      = if T = φ S then ‖c S‖ else 0 := by
    intro S
    rw [hact S, PiLp.smul_apply, smul_eq_mul, fockBasis_ofLp]
    by_cases h : T = φ S <;> simp [h]
  rw [Finset.sum_congr rfl (fun S _ => hterm S)]
  by_cases hex : ∃ S₀, T = φ S₀ ∧ c S₀ ≠ 0
  · obtain ⟨S₀, hφ₀, hc₀⟩ := hex
    have hunique : ∀ S : Finset (Fin d), T = φ S → c S ≠ 0 → S = S₀ :=
      fun S hφ hc => hinj S S₀ hc hc₀ (hφ.symm.trans hφ₀)
    rw [Finset.sum_eq_single S₀]
    · rw [if_pos hφ₀]
      exact hb S₀
    · intro S _ hSS₀
      by_cases hφ : T = φ S
      · have hcS : c S = 0 := by
          by_contra hc
          exact hSS₀ (hunique S hφ hc)
        rw [if_pos hφ, hcS, norm_zero]
      · rw [if_neg hφ]
    · intro h
      exact absurd (Finset.mem_univ S₀) h
  · push_neg at hex
    have hzero : ∀ S : Finset (Fin d), (if T = φ S then ‖c S‖ else 0) = 0 := by
      intro S
      by_cases hφ : T = φ S
      · have hcS : c S = 0 := by simpa using hex S hφ
        rw [if_pos hφ, hcS, norm_zero]
      · rw [if_neg hφ]
    rw [Finset.sum_congr rfl (fun S _ => hzero S)]
    simp

/-- The raw quartic interaction with coupling tensor `W`:
`∑ᵢⱼₖₗ W i j k l • a†ᵢ a†ⱼ aₖ aₗ`. -/
noncomputable def wickQuartic (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    Module.End ℂ (FermionicFock d) :=
  ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
    (W i j k l) • wickMono d i j k l

/-- The adjoint-flipped coupling tensor: `(adjCoupl W) i j k l = conj (W l k j i)`.
The monomial adjoint reverses the four indices; the conjugation is the one
forced by `inner_smul_left`. -/
noncomputable def adjCoupl (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (i j k l : Fin d) : ℂ :=
  (starRingEnd ℂ) (W l k j i)

/-- The symmetrized general quartic interaction
`V = wickQuartic W + wickQuartic (adjCoupl W)`, self-adjoint by construction. -/
noncomputable def intOp (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    Module.End ℂ (FermionicFock d) :=
  wickQuartic d W + wickQuartic d (adjCoupl d W)

/-- The coupling mass `∑ᵢⱼₖₗ ‖W i j k l‖`: the total size of the coupling tensor. -/
noncomputable def couplingMass (W : Fin d → Fin d → Fin d → Fin d → ℂ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, ‖W i j k l‖

/-- The interaction bound `intBound W = 2 · couplingMass W`: the uniform bound on
every matrix coefficient and every row sum of `intOp W` in the occupation basis. -/
noncomputable def intBound (W : Fin d → Fin d → Fin d → Fin d → ℂ) : ℝ :=
  2 * couplingMass d W

/-- Reversing a quadruple sum over modes. -/
theorem sum_quadruple_rev {β : Type*} [AddCommMonoid β]
    (F : Fin d → Fin d → Fin d → Fin d → β) :
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, F i j k l)
      = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, F l k j i := by
  have key : ∀ G : Fin d → Fin d → Fin d → Fin d → β,
      (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, G i j k l)
        = ∑ t : ((Fin d × Fin d) × Fin d) × Fin d, G t.1.1.1 t.1.1.2 t.1.2 t.2 := by
    intro G
    exact (Fintype.sum_prod_type
      (fun p : Fin d × Fin d => ∑ k : Fin d, ∑ l : Fin d, G p.1 p.2 k l)).symm.trans
      ((Fintype.sum_prod_type
        (fun q : (Fin d × Fin d) × Fin d => ∑ l : Fin d, G q.1.1 q.1.2 q.2 l)).symm.trans
        (Fintype.sum_prod_type
          (fun t : ((Fin d × Fin d) × Fin d) × Fin d => G t.1.1.1 t.1.1.2 t.1.2 t.2)).symm)
  let rev : ((Fin d × Fin d) × Fin d) × Fin d ≃ ((Fin d × Fin d) × Fin d) × Fin d :=
    { toFun := fun t => (((t.2, t.1.2), t.1.1.2), t.1.1.1)
      invFun := fun t => (((t.2, t.1.2), t.1.1.2), t.1.1.1)
      left_inv := fun ⟨⟨⟨a, b⟩, c⟩, e⟩ => rfl
      right_inv := fun ⟨⟨⟨a, b⟩, c⟩, e⟩ => rfl }
  exact (key F).trans ((Equiv.sum_comp rev (fun t => F t.1.1.1 t.1.1.2 t.1.2 t.2)).symm.trans
    (key (fun i j k l => F l k j i)).symm)

/-- Moving a creation operator across the inner product (left-slot adjoint);
this is the corpus's `adag_adjoint`, recorded here in the chain's notation. -/
theorem adag_inner_left (i : Fin d) (x y : FermionicFock d) :
    ⟪adag d i x, y⟫_ℂ = ⟪x, ann d i y⟫_ℂ :=
  adag_adjoint d i x y

/-- The adjoint of a Wick monomial is the reversed Wick monomial. -/
theorem wickMono_inner_adjoint (i j k l : Fin d) (x y : FermionicFock d) :
    ⟪wickMono d i j k l x, y⟫_ℂ = ⟪x, wickMono d l k j i y⟫_ℂ := by
  unfold wickMono
  simp only [LinearMap.comp_apply]
  rw [adag_inner_left, adag_inner_left, ann_adjoint, ann_adjoint]

/-- The adjoint of the raw quartic is the raw quartic of the flipped coupling. -/
theorem wickQuartic_inner_adjoint (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (x y : FermionicFock d) :
    ⟪wickQuartic d W x, y⟫_ℂ = ⟪x, wickQuartic d (adjCoupl d W) y⟫_ℂ := by
  unfold wickQuartic
  simp only [LinearMap.sum_apply, sum_inner, inner_sum, LinearMap.smul_apply,
    inner_smul_left, inner_smul_right, wickMono_inner_adjoint]
  refine (sum_quadruple_rev d
    (fun i j k l => (starRingEnd ℂ) (W i j k l) * ⟪x, wickMono d l k j i y⟫_ℂ)).trans ?_
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
  rfl

/-- The flip is an involution on coupling tensors. -/
theorem adjCoupl_adjCoupl (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    adjCoupl d (adjCoupl d W) = W := by
  funext i j k l
  simp [adjCoupl]

/-- **The general quartic is self-adjoint (T1).** `intOp W` is symmetric for every
coupling tensor `W`, by the symmetrized construction. -/
theorem intOp_isSymmetric (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (intOp d W).IsSymmetric := by
  intro x y
  unfold intOp
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    wickQuartic_inner_adjoint, wickQuartic_inner_adjoint, adjCoupl_adjCoupl]
  exact add_comm _ _

/-- The coupling mass is invariant under the adjoint flip. -/
theorem couplingMass_adjCoupl (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    couplingMass d (adjCoupl d W) = couplingMass d W := by
  unfold couplingMass
  refine (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))).trans
    (sum_quadruple_rev d (fun a b c e => ‖W a b c e‖)).symm
  show ‖(starRingEnd ℂ) (W l k j i)‖ = ‖W l k j i‖
  exact RCLike.norm_conj _

/-- Coefficient bound for the raw quartic (Task A2). -/
theorem wickQuartic_coeff_bound (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (S T : Finset (Fin d)) :
    ‖(wickQuartic d W (fockBasis d T)).ofLp S‖ ≤ couplingMass d W := by
  have hcoord : (wickQuartic d W (fockBasis d T)).ofLp S
      = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        (W i j k l) * (wickMono d i j k l (fockBasis d T)).ofLp S := by
    unfold wickQuartic
    simp only [LinearMap.sum_apply, ofLp_sum_gen, LinearMap.smul_apply, PiLp.smul_apply,
      smul_eq_mul]
  rw [hcoord]
  calc ‖∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        (W i j k l) * (wickMono d i j k l (fockBasis d T)).ofLp S‖
      ≤ ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          ‖(W i j k l) * (wickMono d i j k l (fockBasis d T)).ofLp S‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        exact norm_sum_le _ _
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          ‖W i j k l‖ * ‖(wickMono d i j k l (fockBasis d T)).ofLp S‖ :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => norm_mul _ _))))
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, ‖W i j k l‖ := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))))
        exact (mul_le_mul_of_nonneg_left
          (isBasisMono_coeff_bound d (isBasisMono_wickMono d i j k l) S T)
          (norm_nonneg _)).trans_eq (mul_one _)
    _ = couplingMass d W := rfl

/-- Row-sum bound for the raw quartic (Task A2). -/
theorem wickQuartic_col_sum_le (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (S : Finset (Fin d)) :
    ∑ T : Finset (Fin d), ‖(wickQuartic d W (fockBasis d T)).ofLp S‖
      ≤ couplingMass d W := by
  have hcoord : ∀ T : Finset (Fin d), (wickQuartic d W (fockBasis d T)).ofLp S
      = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        (W i j k l) * (wickMono d i j k l (fockBasis d T)).ofLp S := by
    intro T
    unfold wickQuartic
    simp only [LinearMap.sum_apply, ofLp_sum_gen, LinearMap.smul_apply, PiLp.smul_apply,
      smul_eq_mul]
  calc ∑ T : Finset (Fin d), ‖(wickQuartic d W (fockBasis d T)).ofLp S‖
      = ∑ T : Finset (Fin d), ‖∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          (W i j k l) * (wickMono d i j k l (fockBasis d T)).ofLp S‖ :=
        Finset.sum_congr rfl (fun T _ => by rw [hcoord T])
    _ ≤ ∑ T : Finset (Fin d), ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          ‖W i j k l‖ * ‖(wickMono d i j k l (fockBasis d T)).ofLp S‖ := by
        refine Finset.sum_le_sum (fun T _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => ?_))
        exact le_of_eq (norm_mul _ _)
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          ∑ T : Finset (Fin d), ‖W i j k l‖ * ‖(wickMono d i j k l (fockBasis d T)).ofLp S‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, ‖W i j k l‖ := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))))
        calc ∑ T : Finset (Fin d), ‖W i j k l‖ * ‖(wickMono d i j k l (fockBasis d T)).ofLp S‖
            = ‖W i j k l‖ * ∑ T : Finset (Fin d),
                ‖(wickMono d i j k l (fockBasis d T)).ofLp S‖ := by
              rw [Finset.mul_sum]
          _ ≤ ‖W i j k l‖ * 1 :=
              mul_le_mul_of_nonneg_left
                (isBasisMono_col_sum_le d (isBasisMono_wickMono d i j k l) S) (norm_nonneg _)
          _ = ‖W i j k l‖ := mul_one _
    _ = couplingMass d W := rfl

/-- **Coefficient bound for the interaction (Task A2, T1).** Every matrix
coefficient of `intOp W` in the occupation basis is `≤ intBound W`. -/
theorem intOp_coeff_bound (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (S T : Finset (Fin d)) :
    ‖(intOp d W (fockBasis d T)).ofLp S‖ ≤ intBound d W := by
  have hcoord : (intOp d W (fockBasis d T)).ofLp S
      = (wickQuartic d W (fockBasis d T)).ofLp S
        + (wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S := by
    unfold intOp
    rw [LinearMap.add_apply, ofLp_add_gen]
  rw [hcoord]
  calc ‖(wickQuartic d W (fockBasis d T)).ofLp S
        + (wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S‖
      ≤ ‖(wickQuartic d W (fockBasis d T)).ofLp S‖
        + ‖(wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S‖ := norm_add_le _ _
    _ ≤ couplingMass d W + couplingMass d (adjCoupl d W) :=
        add_le_add (wickQuartic_coeff_bound d W S T) (wickQuartic_coeff_bound d _ S T)
    _ = intBound d W := by
        rw [couplingMass_adjCoupl]
        unfold intBound
        ring

/-- **Row-sum bound for the interaction (Task A2, T1).** At every output
configuration, the coefficients of `intOp W` over all input configurations sum
to `≤ intBound W`. This is the Gershgorin-ready estimate. -/
theorem intOp_col_sum_le (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (S : Finset (Fin d)) :
    ∑ T : Finset (Fin d), ‖(intOp d W (fockBasis d T)).ofLp S‖ ≤ intBound d W := by
  have hcoord : ∀ T : Finset (Fin d), (intOp d W (fockBasis d T)).ofLp S
      = (wickQuartic d W (fockBasis d T)).ofLp S
        + (wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S := by
    intro T
    unfold intOp
    rw [LinearMap.add_apply, ofLp_add_gen]
  calc ∑ T : Finset (Fin d), ‖(intOp d W (fockBasis d T)).ofLp S‖
      = ∑ T : Finset (Fin d), ‖(wickQuartic d W (fockBasis d T)).ofLp S
          + (wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S‖ :=
        Finset.sum_congr rfl (fun T _ => by rw [hcoord T])
    _ ≤ ∑ T : Finset (Fin d), (‖(wickQuartic d W (fockBasis d T)).ofLp S‖
          + ‖(wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S‖) :=
        Finset.sum_le_sum (fun T _ => norm_add_le _ _)
    _ = ∑ T : Finset (Fin d), ‖(wickQuartic d W (fockBasis d T)).ofLp S‖
          + ∑ T : Finset (Fin d),
            ‖(wickQuartic d (adjCoupl d W) (fockBasis d T)).ofLp S‖ :=
        Finset.sum_add_distrib
    _ ≤ couplingMass d W + couplingMass d (adjCoupl d W) :=
        add_le_add (wickQuartic_col_sum_le d W S) (wickQuartic_col_sum_le d _ S)
    _ = intBound d W := by
        rw [couplingMass_adjCoupl]
        unfold intBound
        ring

/-! ## §4. The interacting Hamiltonian and eigenvalue transport (Tasks A1/A3)

`H(g) = H₀ + g • V` with `V = intOp W` the general quartic. The transport
theorem is the Gershgorin argument in the corpus's coefficient dialect
(the scoping's priced route): at a maximal coordinate of an eigenvector, the
eigenvalue equation bounds `‖μ − (free eigenvalue)‖` by `|g| · intBound W`,
using the row-sum bound of §3. -/

/-- The interacting Hamiltonian `H(g) = H₀ + g • V`, with `H₀` the corpus's free
Hamiltonian and `V = intOp W` the general quartic interaction of §3. -/
noncomputable def hamInt (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) : Module.End ℂ (FermionicFock d) :=
  freeHamiltonian d lam + (g : ℂ) • intOp d W

/-- At `g = 0`, `hamInt` recovers the free Hamiltonian (Task A1). -/
theorem hamInt_zero (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    hamInt d lam W 0 = freeHamiltonian d lam := by
  unfold hamInt
  simp

/-- **The interacting Hamiltonian is self-adjoint (Task A1, T1).** -/
theorem hamInt_isSymmetric (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) : (hamInt d lam W g).IsSymmetric := by
  intro x y
  have hfree := diagOp_isSymmetric d (T := freeHamiltonian d lam)
    (r := fun S => ∑ i ∈ S, lam i) (freeHamiltonian_basis d lam) x y
  have hint := intOp_isSymmetric d W x y
  unfold hamInt
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hfree, hint, Complex.conj_ofReal]

/-- The coordinate form of `hamInt`: at output configuration `T`, the free part
multiplies the coordinate by the free eigenvalue, and the interaction mixes
coordinates through its occupation-basis matrix coefficients. -/
theorem hamInt_apply_coord (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) (ψ : FermionicFock d) (T : Finset (Fin d)) :
    (hamInt d lam W g ψ).ofLp T
      = ((∑ i ∈ T, lam i : ℝ) : ℂ) * ψ.ofLp T
        + (g : ℂ) * ∑ S : Finset (Fin d), (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S := by
  have hInt : (intOp d W ψ).ofLp T
      = ∑ S : Finset (Fin d), (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S := by
    conv_lhs => rw [fock_expand d ψ]
    rw [map_sum, ofLp_sum_gen]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]
  calc (hamInt d lam W g ψ).ofLp T
      = (freeHamiltonian d lam ψ).ofLp T + (((g : ℂ) • intOp d W) ψ).ofLp T := by
        unfold hamInt
        rw [LinearMap.add_apply, ofLp_add_gen]
    _ = ((∑ i ∈ T, lam i : ℝ) : ℂ) * ψ.ofLp T
        + (g : ℂ) * ∑ S : Finset (Fin d),
          (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S := by
        rw [freeHamiltonian_ofLp, LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, hInt]

/-- **Eigenvalue transport (Task A3 core, T1).** Every eigenvalue `μ` of `H(g)`
lies within `|g| · intBound W` of a free eigenvalue `∑ i ∈ T, lam i`: the
Gershgorin transport of the free spectrum, proved by the maximal-coordinate
argument with the row-sum bound `intOp_col_sum_le`. -/
theorem hamInt_eigenvalue_transport (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ)
    {ψ : FermionicFock d} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamInt d lam W g ψ = μ • ψ) :
    ∃ T : Finset (Fin d), ‖μ - ((∑ i ∈ T, lam i : ℝ) : ℂ)‖ ≤ |g| * intBound d W := by
  obtain ⟨T, -, hTmax⟩ := Finset.exists_max_image Finset.univ
    (fun S => ‖ψ.ofLp S‖) ⟨∅, Finset.mem_univ ∅⟩
  have hψT : ψ.ofLp T ≠ 0 := by
    intro h
    apply hψ
    apply PiLp.ext
    intro S
    have hle : ‖ψ.ofLp S‖ ≤ ‖ψ.ofLp T‖ := hTmax S (Finset.mem_univ S)
    rw [h, norm_zero] at hle
    rw [norm_le_zero_iff.mp hle]
    rfl
  have hcoord := congrArg (fun z : FermionicFock d => z.ofLp T) hμ
  rw [hamInt_apply_coord, PiLp.smul_apply, smul_eq_mul] at hcoord
  refine ⟨T, ?_⟩
  have hsub : (μ - ((∑ i ∈ T, lam i : ℝ) : ℂ)) * ψ.ofLp T
      = (g : ℂ) * ∑ S : Finset (Fin d),
        (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S := by
    rw [sub_mul, ← hcoord, add_sub_cancel_left]
  have hnorm : ‖μ - ((∑ i ∈ T, lam i : ℝ) : ℂ)‖ * ‖ψ.ofLp T‖
      ≤ (|g| * intBound d W) * ‖ψ.ofLp T‖ := by
    calc ‖μ - ((∑ i ∈ T, lam i : ℝ) : ℂ)‖ * ‖ψ.ofLp T‖
        = ‖(μ - ((∑ i ∈ T, lam i : ℝ) : ℂ)) * ψ.ofLp T‖ := (norm_mul _ _).symm
      _ = ‖(g : ℂ) * ∑ S : Finset (Fin d),
            (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S‖ := by rw [hsub]
      _ = |g| * ‖∑ S : Finset (Fin d),
            (intOp d W (fockBasis d S)).ofLp T * ψ.ofLp S‖ := by
          rw [norm_mul, show ‖((g : ℂ))‖ = |g| from RCLike.norm_ofReal g]
      _ ≤ |g| * ∑ S : Finset (Fin d),
            ‖(intOp d W (fockBasis d S)).ofLp T‖ * ‖ψ.ofLp S‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg g)
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum (fun S _ => le_of_eq (norm_mul _ _)))
      _ ≤ |g| * ∑ S : Finset (Fin d),
            ‖(intOp d W (fockBasis d S)).ofLp T‖ * ‖ψ.ofLp T‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg g)
          refine Finset.sum_le_sum (fun S _ => ?_)
          exact mul_le_mul_of_nonneg_left (hTmax S (Finset.mem_univ S)) (norm_nonneg _)
      _ = |g| * ((∑ S : Finset (Fin d),
            ‖(intOp d W (fockBasis d S)).ofLp T‖) * ‖ψ.ofLp T‖) := by
          rw [← Finset.sum_mul]
      _ ≤ (|g| * intBound d W) * ‖ψ.ofLp T‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (intOp_col_sum_le d W T) (norm_nonneg _))
            (abs_nonneg g)
  exact le_of_mul_le_mul_right hnorm (norm_pos_iff.mpr hψT)

/-! ## §5. Ground energy and gap persistence (Task A3)

The ground energy is the minimum of the spectral theorem's eigenvalue list of
the self-adjoint `hamInt`. The Rayleigh bound at the free vacuum controls it
from above; the transport of §4 controls it from the free dichotomy; together
they give the persistence theorem: at the explicit threshold
`2|g| · intBound W ≤ Δ/4`, the ground eigenvalue stays in the ball of radius
`|g| · intBound W` about `0`, and every other eigenvalue is `≥ Δ/2` — the free
gap persists with size at least `Δ/2` above the ground cluster, in the
eigenvalue sense throughout. -/

/-- The fermionic Fock space has dimension `2^d`. -/
theorem finrank_fermionicFock : Module.finrank ℂ (FermionicFock d) = 2 ^ d := by
  rw [finrank_euclideanSpace, Fintype.card_finset, Fintype.card_fin]

/-- The ground energy of `hamInt`: the minimum of its spectral eigenvalue list. -/
noncomputable def groundEnergy (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) : ℝ :=
  Finset.min' (Finset.univ.image (fun i : Fin (2 ^ d) =>
    (hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i))
    ⟨(hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d)
      ⟨0, pow_pos zero_lt_two d⟩,
      Finset.mem_image.mpr ⟨⟨0, pow_pos zero_lt_two d⟩, Finset.mem_univ _, rfl⟩⟩

/-- The ground energy is attained at a spectral index. -/
theorem groundEnergy_mem (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) :
    ∃ i : Fin (2 ^ d), groundEnergy d lam W g
      = (hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i := by
  have hne : (Finset.univ.image (fun i : Fin (2 ^ d) =>
    (hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i)).Nonempty :=
    ⟨(hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d)
      ⟨0, pow_pos zero_lt_two d⟩,
      Finset.mem_image.mpr ⟨⟨0, pow_pos zero_lt_two d⟩, Finset.mem_univ _, rfl⟩⟩
  have h := Finset.min'_mem _ hne
  rw [Finset.mem_image] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, hi.symm⟩

/-- The ground energy bounds every spectral eigenvalue below. -/
theorem groundEnergy_le (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) (i : Fin (2 ^ d)) :
    groundEnergy d lam W g
      ≤ (hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The ground energy is an eigenvalue of `hamInt`. -/
theorem groundEnergy_hasEigenvalue (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamInt d lam W g).HasEigenvalue (groundEnergy d lam W g : ℂ) := by
  obtain ⟨i, hi⟩ := groundEnergy_mem d lam W g
  rw [hi]
  exact (hamInt_isSymmetric d lam W g).hasEigenvalue_eigenvalues (finrank_fermionicFock d) i

/-- The expectation of `hamInt` in any state, expanded in its own eigenvector
basis: `⟪ψ, Hψ⟫ = ∑ᵢ eᵢ ‖⟪bᵢ, ψ⟫‖²` (a nonnegative real combination). -/
theorem hamInt_inner_eq (lam : Fin d → ℝ) (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (g : ℝ) (ψ : FermionicFock d) :
    ⟪ψ, hamInt d lam W g ψ⟫_ℂ = ((∑ i : Fin (2 ^ d),
      (hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i
        * ‖⟪(hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d) i,
            ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  have hEig : ∀ i : Fin (2 ^ d), hamInt d lam W g
      ((hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d) i)
      = ((hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i : ℂ)
        • (hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d) i :=
    fun i => (hamInt_isSymmetric d lam W g).apply_eigenvectorBasis
      (finrank_fermionicFock d) i
  have hH : hamInt d lam W g ψ = ∑ i : Fin (2 ^ d),
      (⟪(hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d) i, ψ⟫_ℂ
        * ((hamInt_isSymmetric d lam W g).eigenvalues (finrank_fermionicFock d) i : ℂ))
        • (hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d) i := by
    conv_lhs => rw [← ((hamInt_isSymmetric d lam W g).eigenvectorBasis
      (finrank_fermionicFock d)).sum_repr' ψ]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hEig i, smul_smul]
  rw [hH, inner_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_smul_right]
  have key : ∀ z : ℂ, ∀ a : ℝ, (z * (a : ℂ)) * (starRingEnd ℂ) z
      = ((a * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z a
    have h1 : (z * (a : ℂ)) * (starRingEnd ℂ) z
        = (a : ℂ) * (z * (starRingEnd ℂ) z) := by ring
    rw [h1, show z * (starRingEnd ℂ) z = ((‖z‖ : ℂ)) ^ 2 from RCLike.mul_conj z,
      ← Complex.ofReal_pow]
    exact (Complex.ofReal_mul _ _).symm
  rw [(inner_conj_symm ψ _).symm]
  exact key _ _

/-- The Rayleigh lower bound: `E₋ · ‖ψ‖² ≤ ⟪ψ, Hψ⟫` (real part). -/
theorem groundEnergy_mul_norm_sq_le (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (ψ : FermionicFock d) :
    groundEnergy d lam W g * ‖ψ‖ ^ 2
      ≤ (⟪ψ, hamInt d lam W g ψ⟫_ℂ).re := by
  rw [hamInt_inner_eq, Complex.ofReal_re,
    ← OrthonormalBasis.sum_sq_norm_inner_right
      ((hamInt_isSymmetric d lam W g).eigenvectorBasis (finrank_fermionicFock d)) ψ,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_right (groundEnergy_le d lam W g i) (sq_nonneg _)

/-- Occupation basis vectors are unit vectors. -/
theorem fockBasis_norm (S : Finset (Fin d)) : ‖fockBasis d S‖ = 1 := by
  have h := fockBasis_inner d S S
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖fockBasis d S‖ ^ 2 = (1 : ℝ) := by
    have h' : ((‖fockBasis d S‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      exact h
    exact_mod_cast h'
  calc ‖fockBasis d S‖ = Real.sqrt (‖fockBasis d S‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = 1 := by rw [h2, Real.sqrt_one]

/-- The ground energy is at most the vacuum expectation, which the interaction
bounds by `|g| · intBound W`: `E₋ ≤ |g| · intBound W`. -/
theorem groundEnergy_le_bound (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    groundEnergy d lam W g ≤ |g| * intBound d W := by
  have h1 := groundEnergy_mul_norm_sq_le d lam W g (fockBasis d ∅)
  rw [fockBasis_norm, one_pow, mul_one] at h1
  have hsum : ∑ S : Finset (Fin d), (intOp d W (fockBasis d S)).ofLp ∅
        * (fockBasis d ∅).ofLp S
      = (intOp d W (fockBasis d ∅)).ofLp ∅ := by
    rw [Finset.sum_eq_single ∅]
    · rw [fockBasis_ofLp, if_pos rfl, mul_one]
    · intro S _ hS
      rw [fockBasis_ofLp, if_neg hS, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ ∅) h
  have hcoord : (hamInt d lam W g (fockBasis d ∅)).ofLp ∅
      = (g : ℂ) * (intOp d W (fockBasis d ∅)).ofLp ∅ := by
    rw [hamInt_apply_coord, hsum, Finset.sum_empty]
    simp [fockBasis_ofLp]
  calc groundEnergy d lam W g
      ≤ (⟪fockBasis d ∅, hamInt d lam W g (fockBasis d ∅)⟫_ℂ).re := h1
    _ = ((hamInt d lam W g (fockBasis d ∅)).ofLp ∅).re := by rw [inner_fockBasis_left]
    _ = ((g : ℂ) * (intOp d W (fockBasis d ∅)).ofLp ∅).re := by rw [hcoord]
    _ ≤ ‖(g : ℂ) * (intOp d W (fockBasis d ∅)).ofLp ∅‖ :=
        Complex.re_le_norm _
    _ = |g| * ‖(intOp d W (fockBasis d ∅)).ofLp ∅‖ := by
        rw [norm_mul, show ‖((g : ℂ))‖ = |g| from RCLike.norm_ofReal g]
    _ ≤ |g| * intBound d W :=
        mul_le_mul_of_nonneg_left (intOp_coeff_bound d W ∅ ∅) (abs_nonneg g)

/-- **GAP PERSISTENCE (Task A3 headline, T1).** Under the Rung 9 free-gap
hypotheses — `0 ≤ lam i` and `lam i = 0 ∨ Δ ≤ lam i` for every mode, with
`Δ > 0` — and the explicit small-coupling threshold
`2 * |g| * intBound W ≤ Δ / 4`, the interacting Hamiltonian `H(g)` has a ground
eigenvalue `E₀` within `|g| · intBound W` of `0`, and **every** eigenvalue `μ`
satisfies `μ.re ≤ |g| · intBound W` (the ground cluster) or `Δ / 2 ≤ μ.re`:
the free gap persists as a gap of size at least `Δ / 2` above the perturbed
ground eigenvalue. Eigenvalue sense throughout. -/
theorem hamInt_gap_persistence (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (hthr : 2 * |g| * intBound d W ≤ Δ / 4) :
    ∃ E₀ : ℝ, (hamInt d lam W g).HasEigenvalue (E₀ : ℂ)
      ∧ |E₀| ≤ |g| * intBound d W
      ∧ ∀ {ψ : FermionicFock d} (hψ : ψ ≠ 0) {μ : ℂ},
        hamInt d lam W g ψ = μ • ψ
          → μ.re ≤ |g| * intBound d W ∨ Δ / 2 ≤ μ.re := by
  have hρ : |g| * intBound d W ≤ Δ / 8 := by
    have h2 : (2 : ℝ) * (|g| * intBound d W) = 2 * |g| * intBound d W := by ring
    linarith
  have hvac := groundEnergy_le_bound d lam W g
  refine ⟨groundEnergy d lam W g, groundEnergy_hasEigenvalue d lam W g, ?_, ?_⟩
  · -- |E₋| ≤ ρ: transport of the ground eigenvalue + the vacuum bound + dichotomy
    obtain ⟨ψ0, hψ01, hψ02⟩ :=
      (groundEnergy_hasEigenvalue d lam W g).exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hψ01
    obtain ⟨T, hT⟩ := hamInt_eigenvalue_transport d lam W g hψ02 hψ01
    have hT' : |groundEnergy d lam W g - ∑ i ∈ T, lam i| ≤ |g| * intBound d W := by
      have h := hT
      rwa [← Complex.ofReal_sub, show
        ‖((groundEnergy d lam W g - ∑ i ∈ T, lam i : ℝ) : ℂ)‖
          = |groundEnergy d lam W g - ∑ i ∈ T, lam i| from RCLike.norm_ofReal _] at h
    rcases free_gap_dichotomy d lam Δ hlam hgap T with hf | hf
    · rw [hf, sub_zero] at hT'
      exact hT'
    · have hge : Δ - |g| * intBound d W ≤ groundEnergy d lam W g := by
        have h := (abs_le.mp hT').1
        linarith
      linarith
  · -- every eigenvalue is in the ground cluster or above Δ/2
    intro ψ hψ μ hμ
    have hμeig : (hamInt d lam W g).HasEigenvalue μ :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hμ, hψ⟩
    have hconj := (hamInt_isSymmetric d lam W g).conj_eigenvalue_eq_self hμeig
    have him : μ.im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hμre : μ = (μ.re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im μ]
      rw [him]
      simp
    obtain ⟨T, hT⟩ := hamInt_eigenvalue_transport d lam W g hψ hμ
    have hT' : |μ.re - ∑ i ∈ T, lam i| ≤ |g| * intBound d W := by
      have h := hT
      rwa [hμre, ← Complex.ofReal_sub, show
        ‖((μ.re - ∑ i ∈ T, lam i : ℝ) : ℂ)‖ = |μ.re - ∑ i ∈ T, lam i|
          from RCLike.norm_ofReal _] at h
    rcases free_gap_dichotomy d lam Δ hlam hgap T with hf | hf
    · left
      rw [hf, sub_zero] at hT'
      exact le_trans (le_abs_self _) hT'
    · right
      have h := (abs_le.mp hT').1
      linarith

/-! ## §6. Axiom audit

The headline theorems of this campaign, checked in the fermionic environment
only. Expected: `propext`, `Classical.choice`, `Quot.sound` — and nothing else. -/

#print axioms hamInt_gap_persistence
#print axioms intOp_isSymmetric
#print axioms densityInt_not_dgamma
#print axioms hamInt_eigenvalue_transport
#print axioms hamiltonianDens_gap_exact
#print axioms intOp_col_sum_le
