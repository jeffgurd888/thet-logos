import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import ThetLogos.FermionicFock

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix

/-!
# ThetLogos.SecondQuantDGamma — the dΓ lift and the free Hamiltonian gap (Rung 9, Tasks 2–3)

The **dΓ lift** (differential of second quantization): for a one-particle
operator `M` (a matrix on the mode space `Fin d → ℂ`),

    dΓ(M) = ∑ i j, M i j • a†ᵢ ∘ aⱼ

on the fermionic Fock space of Rung 8 (`FermionicFock.lean`). Everything is
finite-dimensional, so all operators are bounded and adjoints are honest.

**T1 proved here.**
- `dgamma_adjoint` — `⟪dΓ(M) x, y⟫ = ⟪x, dΓ(Mᴴ) y⟫` (adjoint = dΓ of adjoint).
- `dgamma_one` — `dΓ(1) = numberOp`: the number operator is `dΓ(id)`.
- `dgamma_basis_diag` — for diagonal `M = diag(lam)`,
  `dΓ(M) e_S = (∑ i ∈ S, lam i) • e_S`: on the sector basis, `dΓ` acts as the
  **sum over occupied modes**.
- `dgamma_sector` — `dΓ(M)` preserves every n-particle sector, for all `M`.
- `dgamma_vacuum` — `dΓ(M)` annihilates the vacuum.

**The free Hamiltonian gap (Task 3) — DERIVED, free theory, finite modes.**
For real one-particle eigenvalues `lam i ≥ 0` with the dichotomy
`lam i = 0 ∨ Δ ≤ lam i` for some `Δ > 0`, the free Hamiltonian
`H = dΓ(diag lam)` satisfies:
- `freeHamiltonian_basis` — `H e_S = (∑ i ∈ S, lam i) • e_S` (spectrum = mode sums);
- `freeHamiltonian_vacuum` — vacuum eigenvalue `0`;
- `free_gap_dichotomy` — every basis eigenvalue is `0` or `≥ Δ`;
- `freeHamiltonian_eigenvalue_gap` — every operator eigenvalue of `H` is `0` or `≥ Δ`;
- `freeHamiltonian_expectation` — `⟪x, H x⟫ = ∑_T ‖x_T‖² · (∑ i ∈ T, lam i)`, real `≥ 0`.

This is the ladder's first **derived** gap: `Δ` is not inserted into the Fock
space; it is inherited from the one-particle gap through `dΓ`. SCOPE: free
(non-interacting) fermions, finitely many modes. It is NOT the interacting
Yang–Mills mass gap, and no statement here should be read as one.
-/

variable (d : ℕ)

/-- The dΓ lift of a one-particle operator `M`: `dΓ(M) = ∑ i j, M i j • a†ᵢ ∘ aⱼ`. -/
noncomputable def dgamma (M : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (FermionicFock d) :=
  ∑ i : Fin d, ∑ j : Fin d, (M i j) • (adag d i).comp (ann d j)

/-- `dΓ(M)` annihilates the vacuum (T1). -/
theorem dgamma_vacuum (M : Matrix (Fin d) (Fin d) ℂ) :
    dgamma d M (fockVac d) = 0 := by
  unfold dgamma
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, ann_vac, map_zero, smul_zero]

/-- The adjoint of `dΓ(M)` is `dΓ(Mᴴ)` (T1, inner-product form). -/
theorem dgamma_adjoint (M : Matrix (Fin d) (Fin d) ℂ)
    (x y : FermionicFock d) :
    ⟪dgamma d M x, y⟫_ℂ = ⟪x, dgamma d Mᴴ y⟫_ℂ := by
  have term : ∀ i j : Fin d,
      ⟪((M i j) • (adag d i).comp (ann d j)) x, y⟫_ℂ
        = ⟪x, ((Mᴴ j i) • (adag d j).comp (ann d i)) y⟫_ℂ := by
    intro i j
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
      inner_smul_right, LinearMap.comp_apply, LinearMap.comp_apply,
      adag_adjoint, ann_adjoint, Matrix.conjTranspose_apply, starRingEnd_apply]
  simp only [dgamma, LinearMap.sum_apply, inner_sum, sum_inner]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => term j i))

/-- The number operator is `dΓ(1)` (T1). -/
theorem dgamma_one : dgamma d (1 : Matrix (Fin d) (Fin d) ℂ) = numberOp d := by
  unfold dgamma numberOp
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine (Finset.sum_eq_single i (fun j _ hji => ?_)
    (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
  · rw [Matrix.one_apply_ne' hji, zero_smul]
  · rw [Matrix.one_apply_eq, one_smul]

/-- Each monomial `a†ᵢ ∘ aⱼ` maps the sector basis into the same sector (T1). -/
theorem dgamma_term_sector (i j : Fin d) (S : Finset (Fin d)) :
    ((adag d i).comp (ann d j)) (fockBasis d S) ∈ sector d S.card := by
  rw [LinearMap.comp_apply, ann_basis]
  by_cases hjS : j ∈ S
  · rw [ite_eq_right (not_not.mpr hjS), map_smul, adag_basis]
    by_cases hi : i ∈ S.erase j
    · rw [ite_eq_left hi, smul_zero]
      exact Submodule.zero_mem _
    · rw [ite_eq_right hi, smul_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨insert i (S.erase j), ?_, rfl⟩
      have hcard1 : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hjS
      have hcard2 : (insert i (S.erase j)).card = (S.erase j).card + 1 :=
        Finset.card_insert_of_notMem hi
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hjS⟩
      omega
  · rw [ite_eq_left hjS, map_zero]
    exact Submodule.zero_mem _

/-- `dΓ(M)` maps each sector basis vector into its own sector (T1). -/
theorem dgamma_basis_sector (M : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) :
    dgamma d M (fockBasis d S) ∈ sector d S.card := by
  unfold dgamma
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro j _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (dgamma_term_sector d i j S)

/-- `dΓ(M)` preserves every n-particle sector (T1). -/
theorem dgamma_sector (M : Matrix (Fin d) (Fin d) ℂ) (n : ℕ)
    (x : FermionicFock d) (hx : x ∈ sector d n) :
    dgamma d M x ∈ sector d n := by
  let p : Submodule ℂ (FermionicFock d) :=
    { carrier := {x | dgamma d M x ∈ sector d n}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add]; exact Submodule.add_mem _ ha hb
      zero_mem' := by simp [map_zero, Submodule.zero_mem]
      smul_mem' := fun c y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        rw [map_smul]; exact Submodule.smul_mem _ _ hy }
  have hle : sector d n ≤ p := by
    rw [sector, Submodule.span_le]
    rintro y ⟨S, hS, rfl⟩
    show dgamma d M (fockBasis d S) ∈ sector d n
    rw [← hS]
    exact dgamma_basis_sector d M S
  exact hle hx

/-- For diagonal `M = diag(lam)`, `dΓ(M)` acts on the sector basis as the
    **sum over occupied modes** (T1). -/
theorem dgamma_basis_diag (lam : Fin d → ℂ) (S : Finset (Fin d)) :
    dgamma d (Matrix.diagonal lam) (fockBasis d S)
      = (∑ j ∈ S, lam j) • fockBasis d S := by
  have step : ∀ i : Fin d,
      ((∑ j : Fin d, ((Matrix.diagonal lam) i j) • (adag d i).comp (ann d j))
        (fockBasis d S))
        = lam i • ((adag d i).comp (ann d i)) (fockBasis d S) := by
    intro i
    rw [LinearMap.sum_apply]
    refine (Finset.sum_eq_single i (fun j _ hji => ?_)
      (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_ne' _ hji, zero_smul]
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_eq]
  calc dgamma d (Matrix.diagonal lam) (fockBasis d S)
      = ∑ i : Fin d, lam i • ((adag d i).comp (ann d i)) (fockBasis d S) := by
        unfold dgamma
        rw [LinearMap.sum_apply]
        exact Finset.sum_congr rfl (fun i _ => step i)
    _ = ∑ i : Fin d, lam i • ((if i ∈ S then (1 : ℂ) else 0) • fockBasis d S) :=
        Finset.sum_congr rfl (fun i _ => by rw [numberOp_basis])
    _ = ∑ i : Fin d, (if i ∈ S then lam i • fockBasis d S else 0) :=
        Finset.sum_congr rfl (fun i _ => by
          by_cases hi : i ∈ S <;> simp [hi])
    _ = ∑ i ∈ S, lam i • fockBasis d S := by
        rw [← Finset.sum_filter]
        simp
    _ = (∑ j ∈ S, lam j) • fockBasis d S := Finset.sum_smul.symm

/-- Coordinates of a finite sum in the Fock space (T1 helper). -/
theorem ofLp_sum (v : Finset (Fin d) → FermionicFock d) (T : Finset (Fin d)) :
    (∑ S, v S).ofLp T = ∑ S, (v S).ofLp T := by
  show ((fockEquiv d).symm (∑ S, v S)) T = ∑ S, ((fockEquiv d).symm (v S)) T
  rw [map_sum, Finset.sum_apply]

/-- Every vector is the sum of its occupation-basis coordinates (T1). -/
theorem fock_expand (x : FermionicFock d) :
    x = ∑ S : Finset (Fin d), x.ofLp S • fockBasis d S := by
  apply PiLp.ext
  intro T
  rw [ofLp_sum, Finset.sum_eq_single T]
  · rw [PiLp.smul_apply, fockBasis_ofLp, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro S _ hST
    rw [PiLp.smul_apply, fockBasis_ofLp, ite_eq_right (Ne.symm hST), smul_eq_mul,
      mul_zero]
  · intro hT
    exact absurd (Finset.mem_univ T) hT

-- ============================================================================
-- Task 3. The free Hamiltonian and its DERIVED gap (free theory, finite modes)
-- ============================================================================

/-- The diagonal one-particle operator with real eigenvalues `lam`. -/
noncomputable def onePartDiag (lam : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (lam i : ℂ))

/-- The free Fock Hamiltonian `H = dΓ(diag lam)`. -/
noncomputable def freeHamiltonian (lam : Fin d → ℝ) :
    Module.End ℂ (FermionicFock d) :=
  dgamma d (onePartDiag d lam)

/-- `H` is diagonal in the occupation basis, eigenvalue = sum over occupied
    modes (T1). -/
theorem freeHamiltonian_basis (lam : Fin d → ℝ) (S : Finset (Fin d)) :
    freeHamiltonian d lam (fockBasis d S)
      = ((∑ i ∈ S, lam i : ℝ) : ℂ) • fockBasis d S := by
  unfold freeHamiltonian onePartDiag
  rw [dgamma_basis_diag, Complex.ofReal_sum]

/-- The vacuum is an eigenvector of `H` with eigenvalue `0` (T1). -/
theorem freeHamiltonian_vacuum (lam : Fin d → ℝ) :
    freeHamiltonian d lam (fockVac d) = 0 := by
  show freeHamiltonian d lam (fockBasis d ∅) = 0
  rw [freeHamiltonian_basis]
  simp

/-- The diagonal one-particle operator with real eigenvalues is self-adjoint (T1). -/
theorem onePartDiag_conjTranspose (lam : Fin d → ℝ) :
    (onePartDiag d lam)ᴴ = onePartDiag d lam := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [onePartDiag, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      Complex.conj_ofReal]
  · have h' : j ≠ i := Ne.symm h
    simp only [onePartDiag, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_ne' _ h, Matrix.diagonal_apply_ne' _ h', star_zero]

/-- `H` is self-adjoint (T1, inner-product form). -/
theorem freeHamiltonian_selfadjoint (lam : Fin d → ℝ)
    (x y : FermionicFock d) :
    ⟪freeHamiltonian d lam x, y⟫_ℂ = ⟪x, freeHamiltonian d lam y⟫_ℂ := by
  unfold freeHamiltonian
  rw [dgamma_adjoint, onePartDiag_conjTranspose]

/-- Coordinate formula for `H`: it multiplies the `T`-coordinate by the
    eigenvalue `∑ i ∈ T, lam i` (T1). -/
theorem freeHamiltonian_ofLp (lam : Fin d → ℝ) (x : FermionicFock d)
    (T : Finset (Fin d)) :
    (freeHamiltonian d lam x).ofLp T = ((∑ i ∈ T, lam i : ℝ) : ℂ) * x.ofLp T := by
  conv_lhs => rw [fock_expand d x]
  rw [map_sum, ofLp_sum, Finset.sum_eq_single T]
  · simp only [map_smul, freeHamiltonian_basis, PiLp.smul_apply, smul_eq_mul,
      fockBasis_ofLp, ite_true, mul_one]
    ring
  · intro S _ hST
    simp only [map_smul, freeHamiltonian_basis, PiLp.smul_apply, smul_eq_mul,
      fockBasis_ofLp, ite_eq_right (Ne.symm hST), mul_zero]
  · intro hT
    exact absurd (Finset.mem_univ T) hT

/-- The gap dichotomy for basis eigenvalues (T1): with `lam i ≥ 0` and the
    one-particle dichotomy `lam i = 0 ∨ Δ ≤ lam i`, every mode-sum is `0` or `≥ Δ`. -/
theorem free_gap_dichotomy (lam : Fin d → ℝ) (Δ : ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i) (S : Finset (Fin d)) :
    (∑ i ∈ S, lam i) = 0 ∨ Δ ≤ ∑ i ∈ S, lam i := by
  by_cases h : ∀ i ∈ S, lam i = 0
  · exact Or.inl (Finset.sum_eq_zero h)
  · push_neg at h
    obtain ⟨i, hiS, hi0⟩ := h
    rcases hgap i with h0 | hge
    · exact absurd h0 hi0
    · exact Or.inr (le_trans hge (Finset.single_le_sum (fun j _ => hlam j) hiS))

/-- **The DERIVED free gap (T1).** Every eigenvalue of the free Hamiltonian
    `H = dΓ(diag lam)` is `0` or `≥ Δ`, given the one-particle gap data
    (`lam i ≥ 0`, `lam i = 0 ∨ Δ ≤ lam i`). Free theory, finite modes — NOT the
    interacting Yang–Mills gap. -/
theorem freeHamiltonian_eigenvalue_gap (lam : Fin d → ℝ) (Δ : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (ψ : FermionicFock d) (hψ : ψ ≠ 0) (μ : ℂ)
    (hμ : freeHamiltonian d lam ψ = μ • ψ) :
    ∃ S : Finset (Fin d), μ = ((∑ i ∈ S, lam i : ℝ) : ℂ)
      ∧ ((∑ i ∈ S, lam i) = 0 ∨ Δ ≤ ∑ i ∈ S, lam i) := by
  obtain ⟨S, hS⟩ : ∃ S, ψ.ofLp S ≠ 0 := by
    by_contra h
    push_neg at h
    apply hψ
    apply PiLp.ext
    intro T
    rw [h T]
    rfl
  refine ⟨S, ?_, free_gap_dichotomy d lam Δ hlam hgap S⟩
  have hcoord := congrArg (fun z : FermionicFock d => z.ofLp S) hμ
  rw [freeHamiltonian_ofLp, PiLp.smul_apply, smul_eq_mul] at hcoord
  exact (mul_right_cancel₀ hS hcoord).symm

/-- The expectation of `H` is a nonneg real combination of mode sums (T1). -/
theorem freeHamiltonian_expectation (lam : Fin d → ℝ) (x : FermionicFock d) :
    ⟪x, freeHamiltonian d lam x⟫_ℂ
      = ((∑ T : Finset (Fin d),
          Complex.normSq (x.ofLp T) * (∑ i ∈ T, lam i) : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [RCLike.inner_apply, freeHamiltonian_ofLp]
  calc ((∑ i ∈ T, lam i : ℝ) : ℂ) * x.ofLp T * (starRingEnd ℂ) (x.ofLp T)
      = ((∑ i ∈ T, lam i : ℝ) : ℂ)
          * (x.ofLp T * (starRingEnd ℂ) (x.ofLp T)) := by
        ring
    _ = (((∑ i ∈ T, lam i) * Complex.normSq (x.ofLp T) : ℝ) : ℂ) := by
        rw [Complex.mul_conj, ← Complex.ofReal_mul]
    _ = ((Complex.normSq (x.ofLp T) * (∑ i ∈ T, lam i) : ℝ) : ℂ) := by
        rw [mul_comm]

/-- `H ≥ 0` as an operator: the real part of every expectation is `≥ 0` (T1). -/
theorem freeHamiltonian_expectation_nonneg (lam : Fin d → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (x : FermionicFock d) :
    0 ≤ (⟪x, freeHamiltonian d lam x⟫_ℂ).re := by
  rw [freeHamiltonian_expectation, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (Complex.normSq_nonneg _)
    (Finset.sum_nonneg (fun i _ => hlam i))

-- ============================================================================
-- Axiom audit
-- ============================================================================

#print axioms dgamma_adjoint
#print axioms dgamma_one
#print axioms dgamma_sector
#print axioms dgamma_basis_diag
#print axioms freeHamiltonian_eigenvalue_gap
#print axioms freeHamiltonian_expectation_nonneg

end ThetLogos
