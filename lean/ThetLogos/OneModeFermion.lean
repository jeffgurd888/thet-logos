import Mathlib.Analysis.InnerProductSpace.PiL2
import ThetLogos.ConcreteFiniteModel
import ThetLogos.ConcreteStar

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.OneModeFermion — one-mode fermionic Fock space (Rung 5 workhorse)

The free fermion over a single one-particle mode: ⋀(ℂ) ≅ ℂ² with the
Euclidean inner product. Finite-dimensionality dissolves the W0 gap —
adjoints exist, so genuine field operators are definable and the Wightman
targets become provable rather than priced windows.

The workhorse field is the **Majorana field** `ψ(c) = c • (a† + a)`:
complex-linear in the test function, Hermitian w.r.t. test-function
conjugation, with `ψ(f) ∘ ψ(g) = fg • 1`. It carries W1 (Hermiticity),
W2 (ℤ₂ fermion-parity covariance), and W4 (s = +1).

T1 proved here: CAR relations, adjoint relations, Majorana linearity /
Hermiticity / products, creator action on basis states, parity operator
facts, liftTop plumbing for the `D = ⊤` submodule.
-/

/-- One-mode Fock space. -/
abbrev Fock1 := EuclideanSpace ℂ (Fin 2)

/-- Creator / annihilator matrices. -/
def creatorMat1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
def annihilMat1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The creator and annihilator as operators. -/
noncomputable def creator1 : Module.End ℂ Fock1 := endAlgEquiv.symm creatorMat1
noncomputable def annihil1 : Module.End ℂ Fock1 := endAlgEquiv.symm annihilMat1

/-- Vacuum and 1-particle state. -/
def vac1 : Fock1 := WithLp.toLp 2 ![1, 0]
def e1Fock : Fock1 := WithLp.toLp 2 ![0, 1]

theorem endAlgEquiv_creator1 : endAlgEquiv creator1 = creatorMat1 :=
  AlgEquiv.apply_symm_apply _ _
theorem endAlgEquiv_annihil1 : endAlgEquiv annihil1 = annihilMat1 :=
  AlgEquiv.apply_symm_apply _ _

/-- Extensionality via coordinates. -/
theorem Fock1_ext {x y : Fock1} (h : ∀ k : Fin 2, x.ofLp k = y.ofLp k) : x = y := by
  have hfun : x.ofLp = y.ofLp := funext h
  have h2 := congrArg (WithLp.toLp 2) hfun
  rwa [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h2

theorem vac1_ofLp (k : Fin 2) : vac1.ofLp k = ![1, 0] k := by
  fin_cases k <;> rfl
theorem e1Fock_ofLp (k : Fin 2) : e1Fock.ofLp k = ![0, 1] k := by
  fin_cases k <;> rfl
theorem zero_ofLp (k : Fin 2) : (0 : Fock1).ofLp k = 0 := rfl

/-- `C² = 0` (Pauli exclusion, T1). -/
theorem creator1_sq : creator1.comp creator1 = 0 := by
  have h : (creator1 * creator1 : Module.End ℂ Fock1) = 0 := by
    apply endAlgEquiv.injective
    rw [map_mul, endAlgEquiv_creator1, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [creatorMat1, Matrix.mul_apply, Fin.sum_univ_two]
  rwa [Module.End.mul_eq_comp] at h

/-- `A² = 0` (T1). -/
theorem annihil1_sq : annihil1.comp annihil1 = 0 := by
  have h : (annihil1 * annihil1 : Module.End ℂ Fock1) = 0 := by
    apply endAlgEquiv.injective
    rw [map_mul, endAlgEquiv_annihil1, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [annihilMat1, Matrix.mul_apply, Fin.sum_univ_two]
  rwa [Module.End.mul_eq_comp] at h

/-- `{C, A} = 1` (T1). -/
theorem creator_annihil_anticomm :
    creator1.comp annihil1 + annihil1.comp creator1 = 1 := by
  have h : (creator1 * annihil1 + annihil1 * creator1 : Module.End ℂ Fock1) = 1 := by
    apply endAlgEquiv.injective
    rw [map_add, map_mul, map_mul, endAlgEquiv_creator1, endAlgEquiv_annihil1,
      map_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [creatorMat1, annihilMat1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]
  simp only [Module.End.mul_eq_comp] at h
  exact h

/-- `star C = A`: the star sends creator to annihilator (T1). -/
theorem star_creator1 : star creator1 = annihil1 := by
  apply endAlgEquiv.injective
  rw [pauliStar_apply, endAlgEquiv_creator1, endAlgEquiv_annihil1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [creatorMat1, annihilMat1, Matrix.star_apply]

/-- `star A = C` (T1). -/
theorem star_annihil1 : star annihil1 = creator1 := by
  have h : star (star creator1) = star annihil1 := congrArg star star_creator1
  rw [star_star] at h
  exact h.symm

/-- `A = C†`: the annihilator is the Hilbert adjoint of the creator (T1). -/
theorem creator1_adjoint (x y : Fock1) :
    ⟪creator1 x, y⟫_ℂ = ⟪x, annihil1 y⟫_ℂ := by
  rw [← star_creator1]
  exact pauliStar_is_adjoint creator1 x y

/-- Flipped adjoint relation (T1). -/
theorem annihil1_adjoint (x y : Fock1) :
    ⟪annihil1 x, y⟫_ℂ = ⟪x, creator1 y⟫_ℂ := by
  rw [← star_annihil1]
  exact pauliStar_is_adjoint annihil1 x y

/-- The Majorana combination `H = C + A` (T2 definition). -/
noncomputable def majorana1 : Module.End ℂ Fock1 := creator1 + annihil1

/-- `H` is Hermitian (T1). -/
theorem majorana1_hermitian (x y : Fock1) :
    ⟪majorana1 x, y⟫_ℂ = ⟪x, majorana1 y⟫_ℂ := by
  simp only [majorana1, LinearMap.add_apply, inner_add_left, inner_add_right,
    creator1_adjoint, annihil1_adjoint]
  exact add_comm _ _

/-- `H² = 1` (T1): from `{C,A} = 1` and `C² = A² = 0`. -/
theorem majorana1_sq : majorana1.comp majorana1 = 1 := by
  have hexpand : majorana1.comp majorana1
      = creator1.comp creator1 + creator1.comp annihil1
        + (annihil1.comp creator1 + annihil1.comp annihil1) := by
    simp only [majorana1, LinearMap.add_comp, LinearMap.comp_add]
    abel
  rw [hexpand, creator1_sq, annihil1_sq]
  simpa using creator_annihil_anticomm

/-- Coordinate action of an `endAlgEquiv.symm` matrix (T1 helper). -/
theorem symm_coord (M : Matrix (Fin 2) (Fin 2) ℂ) (y : Fock1) (k : Fin 2) :
    ((endAlgEquiv.symm M) y).ofLp k = ∑ j : Fin 2, M k j * y.ofLp j := by
  rw [symmM_apply]
  simp only [Matrix.mulVec, dotProduct, basis2_repr_apply]

/-- `C|0⟩ = |1⟩`, `C|1⟩ = 0` (T1). -/
theorem creator1_vac : creator1 vac1 = e1Fock := by
  apply Fock1_ext
  intro k
  have hc : creator1 = endAlgEquiv.symm creatorMat1 := rfl
  rw [hc, symm_coord]
  simp only [Fin.sum_univ_two, vac1_ofLp, e1Fock_ofLp]
  fin_cases k <;> simp [creatorMat1]

theorem creator1_e1 : creator1 e1Fock = 0 := by
  apply Fock1_ext
  intro k
  have hc : creator1 = endAlgEquiv.symm creatorMat1 := rfl
  rw [hc, symm_coord]
  simp only [Fin.sum_univ_two, e1Fock_ofLp, zero_ofLp]
  fin_cases k <;> simp [creatorMat1]

/-- `H|0⟩ = |1⟩`, `H|1⟩ = |0⟩` (T1). -/
theorem majorana1_vac : majorana1 vac1 = e1Fock := by
  have hA : annihil1 vac1 = 0 := by
    apply Fock1_ext
    intro k
    have ha : annihil1 = endAlgEquiv.symm annihilMat1 := rfl
    rw [ha, symm_coord]
    simp only [Fin.sum_univ_two, vac1_ofLp, zero_ofLp]
    fin_cases k <;> simp [annihilMat1]
  simp only [majorana1, LinearMap.add_apply, creator1_vac, hA, add_zero]

theorem majorana1_e1 : majorana1 e1Fock = vac1 := by
  have hA : annihil1 e1Fock = vac1 := by
    apply Fock1_ext
    intro k
    have ha : annihil1 = endAlgEquiv.symm annihilMat1 := rfl
    rw [ha, symm_coord]
    simp only [Fin.sum_univ_two, e1Fock_ofLp, vac1_ofLp]
    fin_cases k <;> simp [annihilMat1]
  simp only [majorana1, LinearMap.add_apply, creator1_e1, hA, zero_add]

/-- Orthogonality and norms (T1). -/
theorem vac1_e1_orth : ⟪vac1, e1Fock⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]
  simp [vac1, e1Fock, RCLike.inner_apply]

theorem norm_vac1 : ‖vac1‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  simp [vac1]

theorem norm_e1Fock : ‖e1Fock‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  simp [e1Fock]

/-- Vacuum is nonzero (T1). -/
theorem vac1_ne_zero : vac1 ≠ 0 := by
  intro h
  have h2 : (‖vac1‖ : ℝ) = 0 := by simp [h]
  rw [norm_vac1] at h2
  norm_num at h2

/-- The Majorana field `ψ(c) = c • H` (T2 definition). -/
noncomputable def fieldMajorana (c : ℂ) : Module.End ℂ Fock1 := c • majorana1

theorem fieldMajorana_add (a b : ℂ) :
    fieldMajorana (a + b) = fieldMajorana a + fieldMajorana b := by
  simp [fieldMajorana, add_smul]

theorem fieldMajorana_smul (z c : ℂ) :
    fieldMajorana (z * c) = z • fieldMajorana c := by
  simp [fieldMajorana, mul_smul]

/-- The field is Hermitian w.r.t. test-function conjugation (T1). -/
theorem fieldMajorana_hermitian (c : ℂ) (x y : Fock1) :
    ⟪fieldMajorana c x, y⟫_ℂ = ⟪x, fieldMajorana (star c) y⟫_ℂ := by
  simp only [fieldMajorana, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    majorana1_hermitian]
  -- LHS has (starRingEnd ℂ) c, RHS has star c; they are defeq
  rw [show (starRingEnd ℂ) c = star c from rfl]

/-- Scalar-times composition helper (T1). -/
theorem smul_comp_smul (c d : ℂ) (A B : Module.End ℂ Fock1) :
    (c • A).comp (d • B) = (c * d) • (A.comp B) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul, mul_comm d c]

/-- Field products reduce to scalars: `ψ(f)ψ(g) = fg • 1` (T1). -/
theorem fieldMajorana_comp (f g : ℂ) :
    (fieldMajorana f).comp (fieldMajorana g) = (f * g) • (1 : Module.End ℂ Fock1) := by
  rw [fieldMajorana, fieldMajorana, smul_comp_smul, majorana1_sq]

/-- Fermion parity operator `P = diag(1,-1)` (T2 definition). -/
noncomputable def parityOp : Module.End ℂ Fock1 :=
  endAlgEquiv.symm !![1, 0; 0, -1]

theorem parityOp_involutive : parityOp.comp parityOp = LinearMap.id := by
  have h : (parityOp * parityOp : Module.End ℂ Fock1) = 1 := by
    apply endAlgEquiv.injective
    rw [map_mul]
    have hm : endAlgEquiv parityOp = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) :=
      AlgEquiv.apply_symm_apply _ _
    rw [hm, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rwa [Module.End.mul_eq_comp] at h

/-- Parity anticommutes with the Majorana operator (T1): `P∘H = -(H∘P)`. -/
theorem parityOp_anticomm_majorana :
    parityOp.comp majorana1 = -(majorana1.comp parityOp) := by
  have h : (parityOp * majorana1 : Module.End ℂ Fock1)
      = -(majorana1 * parityOp) := by
    apply endAlgEquiv.injective
    rw [map_mul, map_neg, map_mul]
    have hm : endAlgEquiv parityOp = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) :=
      AlgEquiv.apply_symm_apply _ _
    have hH : endAlgEquiv majorana1 = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      have hsum : majorana1 = creator1 + annihil1 := rfl
      rw [hsum, map_add, endAlgEquiv_creator1, endAlgEquiv_annihil1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [creatorMat1, annihilMat1, Matrix.add_apply]
    rw [hm, hH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Module.End.mul_eq_comp] at h
  exact h

/-- Parity coordinate action (T1). -/
theorem parityOp_coord (x : Fock1) (k : Fin 2) :
    (parityOp x).ofLp k = if k = 0 then x.ofLp 0 else -(x.ofLp 1) := by
  have hp : parityOp = endAlgEquiv.symm !![1, 0; 0, -1] := rfl
  rw [hp, symm_coord]
  simp only [Fin.sum_univ_two]
  fin_cases k <;> simp

/-- Parity preserves norms (T1). -/
theorem parityOp_norm (x : Fock1) : ‖parityOp x‖ = ‖x‖ := by
  have h0 : (parityOp x).ofLp 0 = x.ofLp 0 := by
    rw [parityOp_coord x 0]
    simp
  have h1 : (parityOp x).ofLp 1 = -(x.ofLp 1) := by
    rw [parityOp_coord x 1]
    simp
  have h2 : ‖parityOp x‖ ^ 2 = ‖x‖ ^ 2 := by
    have e : ∀ (y : Fock1), ‖y‖ ^ 2 = ‖y.ofLp 0‖ ^ 2 + ‖y.ofLp 1‖ ^ 2 := by
      intro y
      have h := PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 2 => ℂ) y
      rw [Fin.sum_univ_two] at h
      simpa using h
    rw [e (parityOp x), e x, h0, h1, norm_neg]
  rw [sq_eq_sq_iff_abs_eq_abs] at h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

/-- Lift an endomorphism to the top submodule (for `D = ⊤` plumbing). -/
def liftTop {H : Type*} [AddCommGroup H] [Module ℂ H] (L : H →ₗ[ℂ] H) :
    (⊤ : Submodule ℂ H) →ₗ[ℂ] (⊤ : Submodule ℂ H) where
  toFun x := ⟨L (x : H), Submodule.mem_top⟩
  map_add' x y := Subtype.ext (map_add L (x : H) (y : H))
  map_smul' c x := Subtype.ext (map_smul L c (x : H))

theorem liftTop_comp {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H →ₗ[ℂ] H) :
    liftTop (A.comp B) = (liftTop A).comp (liftTop B) := by
  ext x
  rfl

theorem liftTop_smul {H : Type*} [AddCommGroup H] [Module ℂ H]
    (c : ℂ) (L : H →ₗ[ℂ] H) :
    liftTop (c • L) = c • liftTop L := by
  ext x
  rfl

theorem liftTop_one {H : Type*} [AddCommGroup H] [Module ℂ H] :
    liftTop (1 : H →ₗ[ℂ] H) = 1 := by
  ext x
  rfl

/-- Vacuum functional. -/
noncomputable def vacExp1 (X : Module.End ℂ Fock1) : ℂ := ⟪vac1, X vac1⟫_ℂ

theorem vacExp1_one : vacExp1 1 = 1 := by
  simp [vacExp1, inner_self_eq_norm_sq_to_K, norm_vac1]

#print axioms creator1_sq
#print axioms annihil1_sq
#print axioms creator_annihil_anticomm
#print axioms star_creator1
#print axioms creator1_adjoint
#print axioms majorana1_hermitian
#print axioms majorana1_sq
#print axioms creator1_vac
#print axioms creator1_e1
#print axioms majorana1_vac
#print axioms majorana1_e1
#print axioms vac1_ne_zero
#print axioms fieldMajorana_hermitian
#print axioms fieldMajorana_comp
#print axioms parityOp_anticomm_majorana
#print axioms parityOp_norm

end ThetLogos
