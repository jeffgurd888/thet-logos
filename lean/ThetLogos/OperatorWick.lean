import Mathlib.Analysis.InnerProductSpace.PiL2
import ThetLogos.ConcreteStar
import ThetLogos.WickSigns

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.OperatorWick — the 4-point operator Wick identity (Rung 7, Prong 2)

**Goal.** Prove the 4-point fermionic Wick identity as a T1 theorem in a
concrete 2-mode Fock model, discharging every hypothesis of the Part B
priced window (`WickSigns.lean`) as a proved fact rather than an assumption.

**The model.** The 2-mode fermionic Fock space `⋀(ℂ²) ≅ ℂ⁴` with basis
`|00⟩, |10⟩, |01⟩, |11⟩` (indices `0,1,2,3`). Creator/annihilator operators
for each mode are explicit `4×4` matrices with the Koszul sign
(`a₁†|01⟩ = −|11⟩`), transported to operators via `endAlgEquiv4` exactly as
in the `OneModeFermion.lean` template. The true adjoint star is transported
from matrix conjugate-transpose, so creator/annihilator adjoint relations
are T1.

**Fields and state.** Majorana fields `ψ₀ = a₁+a₁†`, `ψ₁ = i(a₁−a₁†)`,
`ψ₂ = a₂+a₂†`, `ψ₃ = i(a₂−a₂†)`; vacuum expectation
`ω(X) = ⟪vac, X vac⟫`; 2-point function `G i j = ω(ψᵢψⱼ)`.

**T1 proved here.**
- CAR for creators/annihilators (squares vanish, `{aᵢ,aᵢ†} = 1`,
  cross-mode anticommutators vanish);
- `star` swaps creator/annihilator per mode; Hilbert-adjoint relations;
- `ω` linear, `ω(1) = 1`, `ω(ψᵢ) = 0`, `ω(ψᵢψⱼ) = G i j`;
- Majorana CAR `{ψᵢ,ψⱼ} = 2δᵢⱼ` (`car_psi`);
- the quasi-free Wick move (`wick_move`);
- the 4-point operator Wick identity (`wick_four_point_operator`):
  `ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ − G₀₂G₁₃ + G₀₃G₁₂`,
  with the signs `+1,−1,+1` identified as the Koszul signs of the three
  4-point pairings (`wick_four_point_koszul`, via `koszulSign_four_point`).

**Correction to the Part B priced window.** The window hypothesized
`{ψᵢ,ψⱼ} = 2Gᵢⱼ` together with `ω(ψᵢψⱼ) = Gᵢⱼ`; jointly these force `G`
symmetric. In the Fock model they are jointly FALSE: `{ψᵢ,ψⱼ} = 2δᵢⱼ`
while `G₀₁ = i ≠ −i = G₁₀`. The Wick move contracts with the
anticommutator `δ`; the 4-point identity holds with the full (non-symmetric)
`G`. The window's hypotheses are repriced accordingly — this file proves
the corrected statements.

**Tier honesty.** Everything here is T1 (machine-checked, `#print axioms`
at the end). Zero sorrys. `satisfiesDestruction` untouched. The n-point
Wick expansion stays priced (needs the Wick recursion). No 4D interacting
QFT claimed; no mass gap claimed.
-/

-- ============================================================================
-- §1. Four-dimensional plumbing (mirrors ConcreteFiniteModel/ConcreteStar)
-- ============================================================================

/-- Two-mode Fock space `⋀(ℂ²) ≅ ℂ⁴`.
    Basis order: `0 = |00⟩` (vacuum), `1 = |10⟩`, `2 = |01⟩`, `3 = |11⟩`. -/
abbrev Fock2 := EuclideanSpace ℂ (Fin 4)

/-- Standard basis for the 2-mode model (T2 definition). -/
noncomputable def basis4 : Module.Basis (Fin 4) ℂ Fock2 :=
  (EuclideanSpace.basisFun (Fin 4) ℂ).toBasis

/-- Endomorphisms as `4×4` matrices (T2 definition): the algebra equivalence. -/
noncomputable def endAlgEquiv4 :
    Module.End ℂ Fock2 ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  LinearMap.toMatrixAlgEquiv basis4

/-- `toMatrix` inverts `endAlgEquiv4.symm` (T1). -/
theorem toMatrix4_symm (M : Matrix (Fin 4) (Fin 4) ℂ) :
    LinearMap.toMatrix basis4 basis4 (endAlgEquiv4.symm M) = M := by
  show endAlgEquiv4.toLinearEquiv (endAlgEquiv4.symm M) = M
  have hsym : ∀ x, endAlgEquiv4.symm x = endAlgEquiv4.toLinearEquiv.symm x := fun x => rfl
  rw [hsym]
  exact LinearEquiv.apply_symm_apply _ _

/-- `basis4.repr` is coordinate evaluation (T1). -/
theorem basis4_repr_apply (z : Fock2) (k : Fin 4) :
    basis4.repr z k = z.ofLp k := by
  show ((EuclideanSpace.basisFun (Fin 4) ℂ).toBasis.repr z) k = z.ofLp k
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- `endAlgEquiv4.symm M` acts by matrix-vector multiplication (T1). -/
theorem symmM4_repr (M : Matrix (Fin 4) (Fin 4) ℂ) (y : Fock2) :
    basis4.repr ((endAlgEquiv4.symm M) y) = Matrix.mulVec M (basis4.repr y) := by
  have h := LinearMap.toMatrix_mulVec_repr basis4 basis4 (endAlgEquiv4.symm M) y
  rwa [toMatrix4_symm M] at h

theorem symmM4_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (y : Fock2) (k : Fin 4) :
    ((endAlgEquiv4.symm M) y).ofLp k = (Matrix.mulVec M (basis4.repr y)) k := by
  rw [← basis4_repr_apply ((endAlgEquiv4.symm M) y) k, symmM4_repr]

/-- Coordinate action of an `endAlgEquiv4.symm` matrix (T1 helper). -/
theorem symm4_coord (M : Matrix (Fin 4) (Fin 4) ℂ) (y : Fock2) (k : Fin 4) :
    ((endAlgEquiv4.symm M) y).ofLp k = ∑ j : Fin 4, M k j * y.ofLp j := by
  rw [symmM4_apply]
  simp only [Matrix.mulVec, dotProduct, basis4_repr_apply]

/-- The TRUE adjoint star on 2-mode endomorphisms (T2 instance), transported
    from matrix conjugate-transpose along `endAlgEquiv4`. -/
noncomputable instance fock2StarInst : Star (Module.End ℂ Fock2) where
  star X := endAlgEquiv4.symm (star (endAlgEquiv4 X))

/-- The star unfolds as matrix conjugate-transpose (T1). -/
theorem fock2Star_apply (X : Module.End ℂ Fock2) :
    endAlgEquiv4 (star X) = star (endAlgEquiv4 X) :=
  AlgEquiv.apply_symm_apply _ _

/-- Involutive (T1): from `star_star` on matrices. -/
theorem fock2Star_involutive (X : Module.End ℂ Fock2) :
    star (star X) = X := by
  apply endAlgEquiv4.injective
  rw [fock2Star_apply, fock2Star_apply, star_star]

/-- Contravariant (T1): from `(MN)ᴴ = NᴴMᴴ` on matrices. -/
theorem fock2Star_mul (X Y : Module.End ℂ Fock2) :
    star (X * Y) = star Y * star X := by
  apply endAlgEquiv4.injective
  rw [fock2Star_apply, map_mul, map_mul, fock2Star_apply, fock2Star_apply,
    Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose]
  exact Matrix.conjTranspose_mul _ _

/-- `InvolutiveStar` (T2 instance). -/
noncomputable instance fock2InvolutiveStarInst :
    InvolutiveStar (Module.End ℂ Fock2) where
  star_involutive := fock2Star_involutive

/-- `StarMul` (T2 instance). -/
noncomputable instance fock2StarMulInst : StarMul (Module.End ℂ Fock2) where
  star_mul := fock2Star_mul

/-- Inner product in coordinates (T1). -/
theorem inner_coord4 (x y : Fock2) :
    ⟪x, y⟫_ℂ = ∑ i : Fin 4, star (x.ofLp i) * y.ofLp i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply', starRingEnd_apply]

/-- The transported star IS the Hilbert adjoint (T1):
    `⟪X x, y⟫ = ⟪x, X⋆ y⟫`. -/
theorem fock2Star_is_adjoint (X : Module.End ℂ Fock2) (x y : Fock2) :
    ⟪X x, y⟫_ℂ = ⟪x, star X y⟫_ℂ := by
  have hX : ∀ i : Fin 4, (X x).ofLp i
      = ∑ j : Fin 4, (endAlgEquiv4 X) i j * x.ofLp j := by
    intro i
    have hXeq : X = endAlgEquiv4.symm (endAlgEquiv4 X) :=
      (AlgEquiv.symm_apply_apply _ _).symm
    conv_lhs => rw [hXeq, symmM4_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [basis4_repr_apply]
  have hS : ∀ i : Fin 4, (star X y).ofLp i
      = ∑ j : Fin 4, star ((endAlgEquiv4 X) j i) * y.ofLp j := by
    intro i
    show ((endAlgEquiv4.symm (star (endAlgEquiv4 X))) y).ofLp i = _
    rw [symmM4_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [basis4_repr_apply, Matrix.star_apply]
  rw [inner_coord4, inner_coord4]
  simp only [hX, hS, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

-- ============================================================================
-- §2. The two-mode creator/annihilator operators
-- ============================================================================

/-- Creator / annihilator matrices for the two modes.
    Mode 1 creates `|10⟩` from `|00⟩` and `−|11⟩` from `|01⟩` (Koszul sign);
    mode 2 creates `|01⟩` from `|00⟩` and `+|11⟩` from `|10⟩`. -/
def creatorMat2m1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0]
def annihilMat2m1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0]
def creatorMat2m2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0]
def annihilMat2m2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The creators and annihilators as operators (T2 definitions). -/
noncomputable def creator2m1 : Module.End ℂ Fock2 := endAlgEquiv4.symm creatorMat2m1
noncomputable def annihil2m1 : Module.End ℂ Fock2 := endAlgEquiv4.symm annihilMat2m1
noncomputable def creator2m2 : Module.End ℂ Fock2 := endAlgEquiv4.symm creatorMat2m2
noncomputable def annihil2m2 : Module.End ℂ Fock2 := endAlgEquiv4.symm annihilMat2m2

theorem endAlgEquiv4_creator2m1 : endAlgEquiv4 creator2m1 = creatorMat2m1 :=
  AlgEquiv.apply_symm_apply _ _
theorem endAlgEquiv4_annihil2m1 : endAlgEquiv4 annihil2m1 = annihilMat2m1 :=
  AlgEquiv.apply_symm_apply _ _
theorem endAlgEquiv4_creator2m2 : endAlgEquiv4 creator2m2 = creatorMat2m2 :=
  AlgEquiv.apply_symm_apply _ _
theorem endAlgEquiv4_annihil2m2 : endAlgEquiv4 annihil2m2 = annihilMat2m2 :=
  AlgEquiv.apply_symm_apply _ _

/-- Pauli exclusion per mode: squares vanish (T1). -/
theorem creator2m1_sq : creator2m1 * creator2m1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_mul, endAlgEquiv4_creator2m1, map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m1, Matrix.mul_apply, Fin.sum_univ_four]

theorem annihil2m1_sq : annihil2m1 * annihil2m1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_mul, endAlgEquiv4_annihil2m1, map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [annihilMat2m1, Matrix.mul_apply, Fin.sum_univ_four]

theorem creator2m2_sq : creator2m2 * creator2m2 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_mul, endAlgEquiv4_creator2m2, map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m2, Matrix.mul_apply, Fin.sum_univ_four]

theorem annihil2m2_sq : annihil2m2 * annihil2m2 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_mul, endAlgEquiv4_annihil2m2, map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [annihilMat2m2, Matrix.mul_apply, Fin.sum_univ_four]

/-- `{cᵢ, aᵢ} = 1` per mode (T1). -/
theorem car2m1 : creator2m1 * annihil2m1 + annihil2m1 * creator2m1 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_creator2m1, endAlgEquiv4_annihil2m1,
    map_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m1, annihilMat2m1, Matrix.add_apply]

theorem car2m2 : creator2m2 * annihil2m2 + annihil2m2 * creator2m2 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_creator2m2, endAlgEquiv4_annihil2m2,
    map_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m2, annihilMat2m2, Matrix.add_apply]

/-- Distinct modes anticommute (T1): the Koszul sign at work. -/
theorem cross_cc : creator2m1 * creator2m2 + creator2m2 * creator2m1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_creator2m1, endAlgEquiv4_creator2m2,
    map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m1, creatorMat2m2, Matrix.add_apply]

theorem cross_aa : annihil2m1 * annihil2m2 + annihil2m2 * annihil2m1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_annihil2m1, endAlgEquiv4_annihil2m2,
    map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [annihilMat2m1, annihilMat2m2, Matrix.add_apply]

theorem cross_ca12 : creator2m1 * annihil2m2 + annihil2m2 * creator2m1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_creator2m1, endAlgEquiv4_annihil2m2,
    map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m1, annihilMat2m2, Matrix.add_apply]

theorem cross_ca21 : creator2m2 * annihil2m1 + annihil2m1 * creator2m2 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, endAlgEquiv4_creator2m2, endAlgEquiv4_annihil2m1,
    map_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m2, annihilMat2m1, Matrix.add_apply]

/-- `star` swaps creator and annihilator per mode (T1). -/
theorem star_creator2m1 : star creator2m1 = annihil2m1 := by
  apply endAlgEquiv4.injective
  rw [fock2Star_apply, endAlgEquiv4_creator2m1, endAlgEquiv4_annihil2m1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m1, annihilMat2m1, Matrix.star_apply]

theorem star_creator2m2 : star creator2m2 = annihil2m2 := by
  apply endAlgEquiv4.injective
  rw [fock2Star_apply, endAlgEquiv4_creator2m2, endAlgEquiv4_annihil2m2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [creatorMat2m2, annihilMat2m2, Matrix.star_apply]

theorem star_annihil2m1 : star annihil2m1 = creator2m1 := by
  have h : star (star creator2m1) = star annihil2m1 := congrArg star star_creator2m1
  rw [star_star] at h
  exact h.symm

theorem star_annihil2m2 : star annihil2m2 = creator2m2 := by
  have h : star (star creator2m2) = star annihil2m2 := congrArg star star_creator2m2
  rw [star_star] at h
  exact h.symm

/-- Hilbert-adjoint relations (T1): annihilators are adjoints of creators. -/
theorem creator2m1_adjoint (x y : Fock2) :
    ⟪creator2m1 x, y⟫_ℂ = ⟪x, annihil2m1 y⟫_ℂ := by
  rw [← star_creator2m1]
  exact fock2Star_is_adjoint creator2m1 x y

theorem annihil2m1_adjoint (x y : Fock2) :
    ⟪annihil2m1 x, y⟫_ℂ = ⟪x, creator2m1 y⟫_ℂ := by
  rw [← star_annihil2m1]
  exact fock2Star_is_adjoint annihil2m1 x y

theorem creator2m2_adjoint (x y : Fock2) :
    ⟪creator2m2 x, y⟫_ℂ = ⟪x, annihil2m2 y⟫_ℂ := by
  rw [← star_creator2m2]
  exact fock2Star_is_adjoint creator2m2 x y

theorem annihil2m2_adjoint (x y : Fock2) :
    ⟪annihil2m2 x, y⟫_ℂ = ⟪x, creator2m2 y⟫_ℂ := by
  rw [← star_annihil2m2]
  exact fock2Star_is_adjoint annihil2m2 x y

/-- Vacuum and basis states (T2 definitions). -/
def vac2 : Fock2 := WithLp.toLp 2 ![1, 0, 0, 0]
def e10 : Fock2 := WithLp.toLp 2 ![0, 1, 0, 0]
def e01 : Fock2 := WithLp.toLp 2 ![0, 0, 1, 0]
def e11 : Fock2 := WithLp.toLp 2 ![0, 0, 0, 1]

/-- Extensionality via coordinates (T1 helper). -/
theorem Fock2_ext {x y : Fock2} (h : ∀ k : Fin 4, x.ofLp k = y.ofLp k) : x = y := by
  have hfun : x.ofLp = y.ofLp := funext h
  have h2 := congrArg (WithLp.toLp 2) hfun
  rwa [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h2

theorem vac2_ofLp (k : Fin 4) : vac2.ofLp k = ![1, 0, 0, 0] k := by
  fin_cases k <;> rfl
theorem e10_ofLp (k : Fin 4) : e10.ofLp k = ![0, 1, 0, 0] k := by
  fin_cases k <;> rfl
theorem e01_ofLp (k : Fin 4) : e01.ofLp k = ![0, 0, 1, 0] k := by
  fin_cases k <;> rfl
theorem e11_ofLp (k : Fin 4) : e11.ofLp k = ![0, 0, 0, 1] k := by
  fin_cases k <;> rfl
theorem zero4_ofLp (k : Fin 4) : (0 : Fock2).ofLp k = 0 := rfl

/-- Creator/annihilator action on the vacuum (T1). -/
theorem creator2m1_vac : creator2m1 vac2 = e10 := by
  apply Fock2_ext
  intro k
  have hc : creator2m1 = endAlgEquiv4.symm creatorMat2m1 := rfl
  rw [hc, symm4_coord]
  simp only [Fin.sum_univ_four, vac2_ofLp, e10_ofLp]
  fin_cases k <;> simp [creatorMat2m1]

theorem annihil2m1_vac : annihil2m1 vac2 = 0 := by
  apply Fock2_ext
  intro k
  have ha : annihil2m1 = endAlgEquiv4.symm annihilMat2m1 := rfl
  rw [ha, symm4_coord]
  simp only [Fin.sum_univ_four, vac2_ofLp, zero4_ofLp]
  fin_cases k <;> simp [annihilMat2m1]

theorem creator2m2_vac : creator2m2 vac2 = e01 := by
  apply Fock2_ext
  intro k
  have hc : creator2m2 = endAlgEquiv4.symm creatorMat2m2 := rfl
  rw [hc, symm4_coord]
  simp only [Fin.sum_univ_four, vac2_ofLp, e01_ofLp]
  fin_cases k <;> simp [creatorMat2m2]

theorem annihil2m2_vac : annihil2m2 vac2 = 0 := by
  apply Fock2_ext
  intro k
  have ha : annihil2m2 = endAlgEquiv4.symm annihilMat2m2 := rfl
  rw [ha, symm4_coord]
  simp only [Fin.sum_univ_four, vac2_ofLp, zero4_ofLp]
  fin_cases k <;> simp [annihilMat2m2]

/-- Vacuum is a unit vector (T1). -/
theorem norm_vac2 : ‖vac2‖ = 1 := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_four]
  simp [vac2]

/-- The vacuum expectation functional (T2 definition). -/
noncomputable def vacExp2 (X : Module.End ℂ Fock2) : ℂ := ⟪vac2, X vac2⟫_ℂ

theorem vacExp2_add (X Y : Module.End ℂ Fock2) :
    vacExp2 (X + Y) = vacExp2 X + vacExp2 Y := by
  simp [vacExp2, LinearMap.add_apply, inner_add_right]

theorem vacExp2_smul (c : ℂ) (X : Module.End ℂ Fock2) :
    vacExp2 (c • X) = c * vacExp2 X := by
  simp [vacExp2, LinearMap.smul_apply, inner_smul_right]

theorem vacExp2_one : vacExp2 1 = 1 := by
  simp [vacExp2, inner_self_eq_norm_sq_to_K, norm_vac2]

/-- Vacuum expectation is the `(0,0)` matrix entry (T1): the workhorse that
    turns every `ω`-computation into explicit matrix arithmetic. -/
theorem vacExp2_entry (X : Module.End ℂ Fock2) :
    vacExp2 X = (endAlgEquiv4 X) 0 0 := by
  have hX : ∀ i : Fin 4, (X vac2).ofLp i
      = ∑ j : Fin 4, (endAlgEquiv4 X) i j * vac2.ofLp j := by
    intro i
    have hXeq : X = endAlgEquiv4.symm (endAlgEquiv4 X) :=
      (AlgEquiv.symm_apply_apply _ _).symm
    conv_lhs => rw [hXeq, symm4_coord]
  show ⟪vac2, X vac2⟫_ℂ = _
  rw [inner_coord4]
  simp only [hX, vac2_ofLp, Fin.sum_univ_four]
  simp

-- ============================================================================
-- §3. Majorana fields, the 2-point function, and the 4-point Wick identity
-- ============================================================================

/-- The four Majorana field operators (T2 definitions). -/
noncomputable def psi0 : Module.End ℂ Fock2 := creator2m1 + annihil2m1
noncomputable def psi1 : Module.End ℂ Fock2 := Complex.I • (creator2m1 - annihil2m1)
noncomputable def psi2 : Module.End ℂ Fock2 := creator2m2 + annihil2m2
noncomputable def psi3 : Module.End ℂ Fock2 := Complex.I • (creator2m2 - annihil2m2)

/-- The field family (T2 definition). -/
noncomputable def psi : Fin 4 → Module.End ℂ Fock2 := ![psi0, psi1, psi2, psi3]

/-- The 2-point function (T2 definition): `G i j = ω(ψᵢψⱼ)`. -/
noncomputable def twoPt : Fin 4 → Fin 4 → ℂ := fun i j => vacExp2 (psi i * psi j)

/-- Explicit Majorana matrices (for the entry computations). -/
def majoranaMat0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]
def majoranaMat1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, Complex.I; 0, 0, -Complex.I, 0]
def majoranaMat2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
def majoranaMat3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I; Complex.I, 0, 0, 0; 0, Complex.I, 0, 0]

theorem endAlgEquiv4_psi0 : endAlgEquiv4 psi0 = majoranaMat0 := by
  rw [psi0, map_add, endAlgEquiv4_creator2m1, endAlgEquiv4_annihil2m1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat0, creatorMat2m1, annihilMat2m1, Matrix.add_apply]

theorem endAlgEquiv4_psi1 : endAlgEquiv4 psi1 = majoranaMat1 := by
  rw [psi1, map_smul, map_sub, endAlgEquiv4_creator2m1, endAlgEquiv4_annihil2m1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat1, creatorMat2m1, annihilMat2m1, smul_eq_mul]

theorem endAlgEquiv4_psi2 : endAlgEquiv4 psi2 = majoranaMat2 := by
  rw [psi2, map_add, endAlgEquiv4_creator2m2, endAlgEquiv4_annihil2m2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat2, creatorMat2m2, annihilMat2m2, Matrix.add_apply]

theorem endAlgEquiv4_psi3 : endAlgEquiv4 psi3 = majoranaMat3 := by
  rw [psi3, map_smul, map_sub, endAlgEquiv4_creator2m2, endAlgEquiv4_annihil2m2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat3, creatorMat2m2, annihilMat2m2, smul_eq_mul]

/-- `ψᵢ² = 1` (T1): the diagonal Majorana CAR. -/
theorem psi0_sq : psi0 * psi0 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_mul, map_one, endAlgEquiv4_psi0]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat0, Matrix.mul_apply, Fin.sum_univ_four]

theorem psi1_sq : psi1 * psi1 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_mul, map_one, endAlgEquiv4_psi1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat1, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem psi2_sq : psi2 * psi2 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_mul, map_one, endAlgEquiv4_psi2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat2, Matrix.mul_apply, Fin.sum_univ_four]

theorem psi3_sq : psi3 * psi3 = 1 := by
  apply endAlgEquiv4.injective
  rw [map_mul, map_one, endAlgEquiv4_psi3]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem psi_sq (i : Fin 4) : psi i * psi i = 1 := by
  fin_cases i
  · show psi0 * psi0 = 1; exact psi0_sq
  · show psi1 * psi1 = 1; exact psi1_sq
  · show psi2 * psi2 = 1; exact psi2_sq
  · show psi3 * psi3 = 1; exact psi3_sq

/-- Off-diagonal Majorana anticommutators, pair by pair (T1). -/
theorem psi01_anticomm : psi0 * psi1 + psi1 * psi0 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi0, endAlgEquiv4_psi1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat0, majoranaMat1, Matrix.add_apply]

theorem psi02_anticomm : psi0 * psi2 + psi2 * psi0 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi0, endAlgEquiv4_psi2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat0, majoranaMat2, Matrix.add_apply]

theorem psi03_anticomm : psi0 * psi3 + psi3 * psi0 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi0, endAlgEquiv4_psi3]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat0, majoranaMat3, Matrix.add_apply]

theorem psi12_anticomm : psi1 * psi2 + psi2 * psi1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi1, endAlgEquiv4_psi2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat1, majoranaMat2, Matrix.add_apply]

theorem psi13_anticomm : psi1 * psi3 + psi3 * psi1 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi1, endAlgEquiv4_psi3]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat1, majoranaMat3, Matrix.add_apply]

theorem psi23_anticomm : psi2 * psi3 + psi3 * psi2 = 0 := by
  apply endAlgEquiv4.injective
  rw [map_add, map_mul, map_mul, map_zero, endAlgEquiv4_psi2, endAlgEquiv4_psi3]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majoranaMat2, majoranaMat3, Matrix.add_apply]

/-- Distinct Majorana fields anticommute (T1): the off-diagonal CAR. -/
theorem psi_anticomm {i j : Fin 4} (h : i ≠ j) :
    psi i * psi j + psi j * psi i = 0 := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · show psi0 * psi1 + psi1 * psi0 = 0; exact psi01_anticomm
  · show psi0 * psi2 + psi2 * psi0 = 0; exact psi02_anticomm
  · show psi0 * psi3 + psi3 * psi0 = 0; exact psi03_anticomm
  · show psi1 * psi0 + psi0 * psi1 = 0; rw [add_comm]; exact psi01_anticomm
  · exact (h rfl).elim
  · show psi1 * psi2 + psi2 * psi1 = 0; exact psi12_anticomm
  · show psi1 * psi3 + psi3 * psi1 = 0; exact psi13_anticomm
  · show psi2 * psi0 + psi0 * psi2 = 0; rw [add_comm]; exact psi02_anticomm
  · show psi2 * psi1 + psi1 * psi2 = 0; rw [add_comm]; exact psi12_anticomm
  · exact (h rfl).elim
  · show psi2 * psi3 + psi3 * psi2 = 0; exact psi23_anticomm
  · show psi3 * psi0 + psi0 * psi3 = 0; rw [add_comm]; exact psi03_anticomm
  · show psi3 * psi1 + psi1 * psi3 = 0; rw [add_comm]; exact psi13_anticomm
  · show psi3 * psi2 + psi2 * psi3 = 0; rw [add_comm]; exact psi23_anticomm
  · exact (h rfl).elim

/-- The Majorana CAR (T1): `{ψᵢ,ψⱼ} = 2δᵢⱼ`.
    NOTE: this is the CORRECTED form of the Part B window hypothesis —
    the anticommutator is `2δᵢⱼ`, not `2Gᵢⱼ`. -/
theorem car_psi (i j : Fin 4) :
    psi i * psi j + psi j * psi i
      = (if i = j then (2 : ℂ) else 0) • (1 : Module.End ℂ Fock2) := by
  by_cases hij : i = j
  · subst hij
    have hif : (if i = i then (2 : ℂ) else 0) = 2 := by simp
    rw [hif, psi_sq, two_smul]
  · have hif : (if i = j then (2 : ℂ) else 0) = 0 := by simp [hij]
    rw [hif, psi_anticomm hij, zero_smul]

/-- `ω(ψᵢ) = 0` (T1): the 1-point function vanishes. -/
theorem vacExp2_psi (i : Fin 4) : vacExp2 (psi i) = 0 := by
  fin_cases i
  · show vacExp2 psi0 = 0
    rw [vacExp2_entry, endAlgEquiv4_psi0]
    simp [majoranaMat0]
  · show vacExp2 psi1 = 0
    rw [vacExp2_entry, endAlgEquiv4_psi1]
    simp [majoranaMat1]
  · show vacExp2 psi2 = 0
    rw [vacExp2_entry, endAlgEquiv4_psi2]
    simp [majoranaMat2]
  · show vacExp2 psi3 = 0
    rw [vacExp2_entry, endAlgEquiv4_psi3]
    simp [majoranaMat3]

/-- `ω(ψᵢψⱼ) = G i j` (T1): holds by definition of the 2-point function. -/
theorem vacExp2_psi_psi (i j : Fin 4) : vacExp2 (psi i * psi j) = twoPt i j := rfl

/-- The quasi-free Wick move, corrected form (T1): the contraction is with
    the anticommutator `2δᵢⱼ`, from `car_psi` plus linearity of `ω`. -/
theorem wick_move (x y : Module.End ℂ Fock2) (i j : Fin 4) :
    vacExp2 (x * (psi i * psi j) * y) + vacExp2 (x * (psi j * psi i) * y)
      = 2 * (if i = j then (1 : ℂ) else 0) * vacExp2 (x * y) := by
  have hcar := car_psi i j
  have hexpand : x * (psi i * psi j) * y + x * (psi j * psi i) * y
      = x * (psi i * psi j + psi j * psi i) * y := by
    rw [mul_add, add_mul]
  have h : x * (psi i * psi j) * y + x * (psi j * psi i) * y
      = (if i = j then (2 : ℂ) else 0) • (x * y) := by
    rw [hexpand, hcar, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [← vacExp2_add, h, vacExp2_smul]
  by_cases hij : i = j <;> simp [hij]

/-- THE 4-POINT OPERATOR WICK IDENTITY (T1):
    `ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ − G₀₂G₁₃ + G₀₃G₁₂`.
    Proved by direct computation: `vacExp2_entry` turns each side into
    explicit `4×4` matrix arithmetic. -/
theorem wick_four_point_operator :
    vacExp2 (psi 0 * psi 1 * psi 2 * psi 3)
      = twoPt 0 1 * twoPt 2 3 - twoPt 0 2 * twoPt 1 3
        + twoPt 0 3 * twoPt 1 2 := by
  have e0 : psi 0 = psi0 := rfl
  have e1 : psi 1 = psi1 := rfl
  have e2 : psi 2 = psi2 := rfl
  have e3 : psi 3 = psi3 := rfl
  simp only [twoPt, vacExp2_entry, e0, e1, e2, e3, map_mul,
    endAlgEquiv4_psi0, endAlgEquiv4_psi1, endAlgEquiv4_psi2, endAlgEquiv4_psi3]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [majoranaMat0, majoranaMat1, majoranaMat2, majoranaMat3, Complex.I_mul_I]

/-- The signs are the Koszul signs (T1): `pairing4a = {{0,1},{2,3}}` signs
    `+1`, `pairing4b = {{0,2},{1,3}}` signs `−1`, `pairing4c = {{0,3},{1,2}}`
    signs `+1` (`koszulSign_four_point`). -/
theorem wick_signs_match :
    ((pairing4a.koszulSign.val : ℤ) : ℂ) = 1 ∧
    ((pairing4b.koszulSign.val : ℤ) : ℂ) = -1 ∧
    ((pairing4c.koszulSign.val : ℤ) : ℂ) = 1 := by
  obtain ⟨h4a, h4b, h4c⟩ := koszulSign_four_point
  rw [h4a, h4b, h4c]
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- The 4-point Wick identity in Koszul-sign form (T1). -/
theorem wick_four_point_koszul :
    vacExp2 (psi 0 * psi 1 * psi 2 * psi 3)
      = ((pairing4a.koszulSign.val : ℤ) : ℂ) * (twoPt 0 1 * twoPt 2 3)
      + ((pairing4b.koszulSign.val : ℤ) : ℂ) * (twoPt 0 2 * twoPt 1 3)
      + ((pairing4c.koszulSign.val : ℤ) : ℂ) * (twoPt 0 3 * twoPt 1 2) := by
  obtain ⟨h4a, h4b, h4c⟩ := wick_signs_match
  rw [h4a, h4b, h4c, wick_four_point_operator]
  ring

#print axioms creator2m1_sq
#print axioms annihil2m1_sq
#print axioms car2m1
#print axioms car2m2
#print axioms cross_cc
#print axioms cross_ca12
#print axioms star_creator2m1
#print axioms creator2m1_adjoint
#print axioms creator2m1_vac
#print axioms vacExp2_one
#print axioms vacExp2_entry
#print axioms psi_sq
#print axioms psi_anticomm
#print axioms car_psi
#print axioms vacExp2_psi
#print axioms wick_move
#print axioms wick_four_point_operator
#print axioms wick_signs_match
#print axioms wick_four_point_koszul

end ThetLogos
