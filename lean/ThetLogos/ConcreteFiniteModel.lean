import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import ThetLogos.ProductTriple
import ThetLogos.AnalyticTriple
import ThetLogos.FactorOrderOne

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.ConcreteFiniteModel — EVOLVE Track 1: the 2-dim Pauli model (2026-10-10)

EVOLVE phase, Track 1 (Jeff's "let's Evolve", 2026-10-10): a concrete
finite-dimensional model discharging the Rung 4 prep analytic debts (T1).

## The model
- `S := EuclideanSpace ℂ (Fin 2)`, `A := ℂ` (scalar algebra);
- `π c = c • 1` (scalar representation);
- `D` = Pauli X, `Γ` = Pauli Z (via the endomorphism/matrix algebra equivalence);
- `Janti` = coordinate-wise conjugation;
- `ηsym = 1`;
- `conjJ` = the real-structure shadow `X ↦ J (X*) J⁻¹`, which for coordinate
  conjugation `J` computes to matrix transpose (see `conjJ2` docstring);
- `ko = ⟨1, 1, 1⟩`;
- `sesq x y = ⟪x, y⟫` (Mathlib inner).

## HONESTY NOTE
The scalar algebra makes all commutators vanish (`[D, π f] = 0`). This model
discharges the ANALYTIC debts — positivity (`hiprod_pos` PROVED from
`⟪x,x⟫ = ‖x‖²`), definiteness, bounded commutators (`C = 0`), bounded
representation (`C = ‖a‖`), finite-dimensional compactness, completeness —
not interesting gauge content. It is "a concrete finite model", NOT the
32×32 SM triple (whose `TripleData` instantiation remains future work per
`ProductTriple.lean`). The `BoundedAnalyticTriple` INSTANCE is not formed:
`hcompactRes` is an opaque def and cannot be inhabited; `hbddComm`/`hbddRep`
are proved as standalone T1 theorems and the compactness content as
`end_compact`/`pauliD_compact`.

## Tier ledger
T2 (definitions): `pauliX`, `pauliZ`, `basis2`, `endAlgEquiv`, `pauliD`,
  `pauliGrading`, `repScal`, `conjJ2`, `Janti2`, `sesq2`, `ko2`, `tripleData`,
  `pauliAnalytic` (instance).
T1 (proved, zero sorrys): `pauliX_sq`, `pauliZ_sq`, `pauliX_pauliZ`,
  `transpose_pauliX`, `transpose_pauliZ`, `pauliX_real`, `pauliZ_real`,
  `toMatrix_symm`, `basis2_repr_apply`, `Janti2_apply`, `Janti2_repr`,
  `symmM_repr`, `symmM_apply`, `Janti2_comm_of_real`, `inner_conj_coord`,
  `pauliGrading_sq`, `pauliD_anticomm`, `repScal_smul_one`, `repScal_even`,
  `conjJ2_mul`, `conjJ2_inv`, `conjJ2_one`, `conjJ2_pauliD`, `conjJ2_pauliGrading`,
  `Janti2_sq`, `Janti2_pauliD`, `Janti2_pauliGrading`, `ηsym_sq'`, `ηsym_selfadj'`,
  `hsesq_symm'`, `hiprod_pos'`, `hiprod_def'`, `hJanti_iprod'`, `nrm_eq_norm`,
  `bddComm`, `bddRep`, `end_compact`, `pauliD_compact`, `hord0'`, `hord1'`.
PARTIAL (documented, not claimed): `BoundedAnalyticTriple` instance —
  `hcompactRes` is opaque (`HasCompactResolvent` cannot be inhabited); the
  mathematical content is `end_compact`.
-/

-- ============================================================================
-- §1. Pauli matrices, the basis, and the endomorphism algebra (T2 defs, T1 facts)
-- ============================================================================

/-- Pauli X (Tier T2 — definition). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli Z (Tier T2 — definition). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `X² = 1` (Tier T1 — proved, 2×2 computation). -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Z² = 1` (Tier T1 — proved, 2×2 computation). -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `XZ = -ZX` (Tier T1 — proved, 2×2 computation). -/
theorem pauliX_pauliZ : pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli X is symmetric (Tier T1 — proved). -/
theorem transpose_pauliX : Matrix.transpose pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.transpose_apply]

/-- Pauli Z is symmetric (Tier T1 — proved). -/
theorem transpose_pauliZ : Matrix.transpose pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.transpose_apply]

/-- Pauli X has real entries (Tier T1 — proved). -/
theorem pauliX_real : ∀ i j, star (pauliX i j) = pauliX i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

/-- Pauli Z has real entries (Tier T1 — proved). -/
theorem pauliZ_real : ∀ i j, star (pauliZ i j) = pauliZ i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

/-- The standard basis (Tier T2 — definition). -/
noncomputable def basis2 : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

/-- Endomorphisms as 2×2 matrices (Tier T2 — definition): the algebra equivalence. -/
noncomputable def endAlgEquiv :
    Module.End ℂ (EuclideanSpace ℂ (Fin 2)) ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toMatrixAlgEquiv basis2

/-- `toMatrix` inverts `endAlgEquiv.symm` (Tier T1 — proved). -/
theorem toMatrix_symm (M : Matrix (Fin 2) (Fin 2) ℂ) :
    LinearMap.toMatrix basis2 basis2 (endAlgEquiv.symm M) = M := by
  show endAlgEquiv.toLinearEquiv (endAlgEquiv.symm M) = M
  have hsym : ∀ x, endAlgEquiv.symm x = endAlgEquiv.toLinearEquiv.symm x := fun x => rfl
  rw [hsym]
  exact LinearEquiv.apply_symm_apply _ _

/-- `basis2.repr` is coordinate evaluation (Tier T1 — proved). -/
theorem basis2_repr_apply (z : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) :
    basis2.repr z k = z.ofLp k := by
  show ((EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.repr z) k = z.ofLp k
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

-- ============================================================================
-- §2. The operators (T2 definitions)
-- ============================================================================

/-- The Dirac: Pauli X (Tier T2 — definition). -/
noncomputable def pauliD : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  endAlgEquiv.symm pauliX

/-- The grading: Pauli Z (Tier T2 — definition). -/
noncomputable def pauliGrading : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  endAlgEquiv.symm pauliZ

/-- The scalar representation `c ↦ c • 1` (Tier T2 — definition). -/
def repScal : ℂ →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) where
  toFun c := c • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
  map_one' := one_smul _ _
  map_mul' := by
    intro c d
    show (c * d) • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
      = (c • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))) * (d • 1)
    rw [← Algebra.algebraMap_eq_smul_one (c * d), map_mul,
      Algebra.algebraMap_eq_smul_one c, Algebra.algebraMap_eq_smul_one d]
  map_zero' := zero_smul _ _
  map_add' := fun c d => add_smul c d _
  commutes' := by
    intro r
    show (algebraMap ℂ ℂ r) • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
      = algebraMap ℂ _ r
    rw [Algebra.algebraMap_eq_smul_one r]
    congr 1
    -- algebraMap ℂ ℂ r = r
    simp

/-- The real-structure shadow (Tier T2 — definition).

    `conjJ2 X = J (X*) J⁻¹`: J-conjugation of the matrix adjoint. For our
    `Janti2` (coordinate conjugation) this computes to plain matrix transpose:
    J-conjugation acts on matrices as entrywise `star`, and
    entrywise-`star` of the conjugate-transpose is the transpose.
    This is the LINEAR anti-automorphism the `TripleData` axioms demand:
    the bare adjoint is conjugate-linear (cannot inhabit the `→ₗ[ℂ]` field)
    and J-conjugation alone is covariant, not contravariant. -/
noncomputable def conjJ2 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) →ₗ[ℂ]
    Module.End ℂ (EuclideanSpace ℂ (Fin 2)) where
  toFun X := endAlgEquiv.symm (Matrix.transpose (endAlgEquiv X))
  map_add' X Y := by simp [map_add, Matrix.transpose_add]
  map_smul' c X := by simp [map_smul, Matrix.transpose_smul]

/-- Coordinate-wise conjugation (Tier T2 — definition): the antilinear real structure. -/
def Janti2 : EuclideanSpace ℂ (Fin 2) →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i => star (x i))
  map_add' x y := by ext i; simp [star_add]
  map_smul' c x := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul, mul_comm]

/-- Pointwise action of `Janti2` (Tier T1 — proved). -/
theorem Janti2_apply (z : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) :
    (Janti2 z).ofLp k = star (z.ofLp k) := by
  rfl

/-- `Janti2` conjugates `basis2`-coordinates (Tier T1 — proved). -/
theorem Janti2_repr (z : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) :
    basis2.repr (Janti2 z) k = star (basis2.repr z k) := by
  rw [basis2_repr_apply, basis2_repr_apply, Janti2_apply]

/-- `endAlgEquiv.symm M` acts by matrix-vector multiplication in coordinates
    (Tier T1 — proved). -/
theorem symmM_repr (M : Matrix (Fin 2) (Fin 2) ℂ) (y : EuclideanSpace ℂ (Fin 2)) :
    basis2.repr ((endAlgEquiv.symm M) y) = Matrix.mulVec M (basis2.repr y) := by
  have h := LinearMap.toMatrix_mulVec_repr basis2 basis2 (endAlgEquiv.symm M) y
  rwa [toMatrix_symm M] at h

/-- Pointwise form of `symmM_repr` (Tier T1 — proved). -/
theorem symmM_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (y : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) :
    ((endAlgEquiv.symm M) y).ofLp k = (Matrix.mulVec M (basis2.repr y)) k := by
  rw [← basis2_repr_apply ((endAlgEquiv.symm M) y) k, symmM_repr]

/-- `Janti2` commutes with real matrices (Tier T1 — proved). -/
theorem Janti2_comm_of_real (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ i j, star (M i j) = M i j) (x : EuclideanSpace ℂ (Fin 2)) :
    Janti2 ((endAlgEquiv.symm M) x) = (endAlgEquiv.symm M) (Janti2 x) := by
  have hJ : ∀ j, (⇑(basis2.repr (Janti2 x)) j) = star ((⇑(basis2.repr x)) j) := by
    intro j
    show (basis2.repr (Janti2 x)) j = star ((basis2.repr x) j)
    rw [basis2_repr_apply, basis2_repr_apply, Janti2_apply, ← basis2_repr_apply]
  ext k
  rw [Janti2_apply, symmM_apply, symmM_apply]
  simp only [Matrix.mulVec, dotProduct, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul, hM k j, hJ j, mul_comm]

/-- The sesquilinear form: Mathlib inner (Tier T2 — definition).
    `inner_smul_left` gives `⟪r • x, y⟫ = r† * ⟪x, y⟫`, i.e. `starRingEnd`-semilinear
    in the first argument — exactly the `sesq` signature. -/
noncomputable def sesq2 : EuclideanSpace ℂ (Fin 2) →ₛₗ[starRingEnd ℂ]
    (EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ) :=
  innerₛₗ ℂ

/-- KO signature `⟨1, 1, 1⟩` (Tier T2 — definition). -/
def ko2 : KOSignature := ⟨1, 1, 1⟩

/-- Antiunitarity on coordinates (Tier T1 — proved). -/
theorem inner_conj_coord (a b : ℂ) : ⟪star a, star b⟫_ℂ = star ⟪a, b⟫_ℂ := by
  rw [RCLike.inner_apply', RCLike.inner_apply']
  show star (star a) * star b = star (star a * b)
  rw [star_star, star_mul, star_star, mul_comm]

-- ============================================================================
-- §3. TripleData axioms verified (T1)
-- ============================================================================

/-- `Γ² = 1` (Tier T1 — proved). -/
theorem pauliGrading_sq : pauliGrading * pauliGrading = 1 := by
  show endAlgEquiv.symm pauliZ * endAlgEquiv.symm pauliZ = 1
  rw [← map_mul, pauliZ_sq, map_one]

/-- `DΓ = -ΓD` (Tier T1 — proved). -/
theorem pauliD_anticomm : pauliD * pauliGrading = -(pauliGrading * pauliD) := by
  show endAlgEquiv.symm pauliX * endAlgEquiv.symm pauliZ
    = -(endAlgEquiv.symm pauliZ * endAlgEquiv.symm pauliX)
  rw [← map_mul, ← map_mul, ← map_neg]
  congr 1
  exact pauliX_pauliZ

/-- `π f = f • 1` (Tier T1 — proved). -/
theorem repScal_smul_one (f : ℂ) :
    repScal f = f • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :=
  rfl

/-- `π` is even: `Γ` commutes with scalars (Tier T1 — proved). -/
theorem repScal_even (f : ℂ) :
    pauliGrading * repScal f = repScal f * pauliGrading := by
  rw [repScal_smul_one f]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]

/-- `conjJ2` is contravariant (Tier T1 — proved): from `(MN)ᵀ = NᵀMᵀ`. -/
theorem conjJ2_mul (X Y : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    conjJ2 (X * Y) = conjJ2 Y * conjJ2 X := by
  show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv (X * Y)))
    = endAlgEquiv.symm (Matrix.transpose (endAlgEquiv Y))
      * endAlgEquiv.symm (Matrix.transpose (endAlgEquiv X))
  rw [map_mul, Matrix.transpose_mul, map_mul]

/-- `conjJ2` is involutive (Tier T1 — proved). -/
theorem conjJ2_inv (X : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) :
    conjJ2 (conjJ2 X) = X := by
  have h : endAlgEquiv (conjJ2 X) = Matrix.transpose (endAlgEquiv X) := by
    show endAlgEquiv (endAlgEquiv.symm (Matrix.transpose (endAlgEquiv X))) = _
    rw [AlgEquiv.apply_symm_apply]
  show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv (conjJ2 X))) = X
  rw [h, Matrix.transpose_transpose, AlgEquiv.symm_apply_apply]

/-- `conjJ2 1 = 1` (Tier T1 — proved). -/
theorem conjJ2_one : conjJ2 1 = 1 := by
  show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv 1)) = 1
  rw [map_one, Matrix.transpose_one, map_one]

/-- `conjJ2 D = D` (`eps' = 1`, Pauli X symmetric) (Tier T1 — proved). -/
theorem conjJ2_pauliD : conjJ2 pauliD = ((ko2.eps' : ℤ) : ℂ) • pauliD := by
  have h2 : conjJ2 pauliD = pauliD := by
    show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv (endAlgEquiv.symm pauliX)))
      = endAlgEquiv.symm pauliX
    rw [AlgEquiv.apply_symm_apply, transpose_pauliX]
  rw [h2, show ko2.eps' = 1 from rfl, Int.cast_one, one_smul]

/-- `conjJ2 Γ = Γ` (`eps'' = 1`, Pauli Z symmetric) (Tier T1 — proved). -/
theorem conjJ2_pauliGrading : conjJ2 pauliGrading = ((ko2.eps'' : ℤ) : ℂ) • pauliGrading := by
  have h2 : conjJ2 pauliGrading = pauliGrading := by
    show endAlgEquiv.symm (Matrix.transpose (endAlgEquiv (endAlgEquiv.symm pauliZ)))
      = endAlgEquiv.symm pauliZ
    rw [AlgEquiv.apply_symm_apply, transpose_pauliZ]
  rw [h2, show ko2.eps'' = 1 from rfl, Int.cast_one, one_smul]

/-- `J² = id` (`eps = 1`) (Tier T1 — proved). -/
theorem Janti2_sq :
    Janti2.comp Janti2
      = ((ko2.eps : ℤ) : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  rw [show ((ko2.eps : ℤ) : ℂ) = 1 from by rw [show ko2.eps = 1 from rfl, Int.cast_one]]
  apply LinearMap.ext
  intro x
  ext k
  have h1 : ((Janti2.comp Janti2) x).ofLp k = star (star (x.ofLp k)) := by
    show (Janti2 (Janti2 x)).ofLp k = _
    rw [Janti2_apply, Janti2_apply]
  have h2 : ((((1 : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] _)) x)).ofLp k
      = x.ofLp k := by
    simp only [LinearMap.smul_apply, one_smul, LinearMap.id_apply]
  rw [h1, h2, star_star]

/-- `J(Dx) = D(Jx)` (`eps' = 1`, Pauli X real) (Tier T1 — proved). -/
theorem Janti2_pauliD :
    Janti2.comp pauliD = ((ko2.eps' : ℤ) : ℂ) • (pauliD.comp Janti2) := by
  rw [show ((ko2.eps' : ℤ) : ℂ) = 1 from by rw [show ko2.eps' = 1 from rfl, Int.cast_one],
    one_smul]
  apply LinearMap.ext
  intro x
  show Janti2 (pauliD x) = pauliD (Janti2 x)
  exact Janti2_comm_of_real pauliX pauliX_real x

/-- `J(Γx) = Γ(Jx)` (`eps'' = 1`, Pauli Z real) (Tier T1 — proved). -/
theorem Janti2_pauliGrading :
    Janti2.comp pauliGrading = ((ko2.eps'' : ℤ) : ℂ) • (pauliGrading.comp Janti2) := by
  rw [show ((ko2.eps'' : ℤ) : ℂ) = 1 from by rw [show ko2.eps'' = 1 from rfl, Int.cast_one],
    one_smul]
  apply LinearMap.ext
  intro x
  show Janti2 (pauliGrading x) = pauliGrading (Janti2 x)
  exact Janti2_comm_of_real pauliZ pauliZ_real x

/-- `η² = 1` (Tier T1 — proved). -/
theorem ηsym_sq' : (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) * 1 = 1 :=
  mul_one 1

/-- `η` is self-adjoint for the form (Tier T1 — proved; `η = 1`). -/
theorem ηsym_selfadj' (x y : EuclideanSpace ℂ (Fin 2)) :
    sesq2 ((1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) x) y
      = sesq2 x ((1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) y) := by
  simp only [Module.End.one_apply]

-- ============================================================================
-- §4. The TripleData (T2)
-- ============================================================================

/-- The Pauli triple data (Tier T2 — definition). -/
noncomputable def tripleData : TripleData where
  A := ℂ
  S := EuclideanSpace ℂ (Fin 2)
  π := repScal
  D := pauliD
  Γ := pauliGrading
  hΓsq := pauliGrading_sq
  hΓD := pauliD_anticomm
  hπeven := repScal_even
  conjJ := conjJ2
  hconjJ_mul := conjJ2_mul
  hconjJ_inv := conjJ2_inv
  hconjJ_one := conjJ2_one
  ko := ko2
  hkoD := conjJ2_pauliD
  hkoΓ := conjJ2_pauliGrading
  sesq := sesq2
  Janti := Janti2
  hJanti_sq := Janti2_sq
  hJanti_D := Janti2_pauliD
  hJanti_Γ := Janti2_pauliGrading
  ηsym := 1
  hηsym_sq := ηsym_sq'
  hηsym_selfadj := ηsym_selfadj'

/-- `iprod` on `tripleData` is the Mathlib inner product (Tier T1 — proved). -/
theorem iprod_eq_inner (x y : EuclideanSpace ℂ (Fin 2)) :
    @iprod tripleData x y = ⟪x, y⟫_ℂ :=
  rfl

-- ============================================================================
-- §5. The AnalyticTripleData instance — debt 1 discharged (T1)
-- ============================================================================

/-- Krein-form symmetry (Tier T1 — proved): from `inner_conj_symm`. -/
theorem hsesq_symm' (x y : EuclideanSpace ℂ (Fin 2)) :
    tripleData.sesq y x = star (tripleData.sesq x y) := by
  show ⟪y, x⟫_ℂ = star ⟪x, y⟫_ℂ
  exact (inner_conj_symm y x).symm

/-- Positivity — PROVED, not assumed (Tier T1):
    `iprod x x = ⟪x, x⟫ = ↑‖x‖² ≥ 0`. -/
theorem hiprod_pos' (x : EuclideanSpace ℂ (Fin 2)) :
    ∃ r : ℝ, 0 ≤ r ∧ @iprod tripleData x x = (r : ℂ) := by
  refine ⟨‖x‖ ^ 2, sq_nonneg _, ?_⟩
  simp [iprod_eq_inner, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]

/-- Definiteness (Tier T1 — proved): from `inner_self_eq_zero`. -/
theorem hiprod_def' (x : EuclideanSpace ℂ (Fin 2)) :
    @iprod tripleData x x = 0 → x = 0 := by
  rw [iprod_eq_inner]
  exact inner_self_eq_zero.mp

/-- Antiunitarity of `Janti2` (Tier T1 — proved by computation). -/
theorem hJanti_iprod' (x y : EuclideanSpace ℂ (Fin 2)) :
    @iprod tripleData (Janti2 x) (Janti2 y) = star (@iprod tripleData x y) := by
  rw [iprod_eq_inner, iprod_eq_inner, PiLp.inner_apply, PiLp.inner_apply, star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Janti2_apply, Janti2_apply]
  exact inner_conj_coord _ _

/-- The analytic triple instance (Tier T2 — instance): debt 1 discharged. -/
noncomputable instance pauliAnalytic : AnalyticTripleData where
  toTripleData := tripleData
  hsesq_symm := hsesq_symm'
  hiprod_pos := hiprod_pos'
  hiprod_def := hiprod_def'
  hJanti_iprod := hJanti_iprod'

/-- `nrm` is the norm (Tier T1 — proved): `nrm x = ‖x‖`. -/
theorem nrm_eq_norm (x : EuclideanSpace ℂ (Fin 2)) :
    @nrm pauliAnalytic x = ‖x‖ := by
  have h : @iprod pauliAnalytic.toTripleData x x = ⟪x, x⟫_ℂ := rfl
  show Real.sqrt (@iprod pauliAnalytic.toTripleData x x).re = ‖x‖
  rw [h]
  have h2 : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    have h4 : ⟪x, x⟫_ℂ = Complex.ofReal (‖x‖ ^ 2) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h4]
    rfl
  rw [h2, Real.sqrt_sq (norm_nonneg _)]

-- ============================================================================
-- §6. Boundedness — debt 2 (T1 theorems; instance partial — see HONESTY NOTE)
-- ============================================================================

/-- The commutator `[D, π f]` vanishes (Tier T1 — proved). -/
theorem comm_repScal_eq_zero (f : ℂ) :
    pauliD * repScal f - repScal f * pauliD
      = (0 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [repScal_smul_one f]
  apply LinearMap.ext
  intro y
  have e1 : (pauliD * (f • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))))) y
      = f • pauliD y := by
    rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  have e2 : ((f • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))) * pauliD) y
      = f • pauliD y := by
    rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  have e3 : ((0 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) y)
      = (0 : EuclideanSpace ℂ (Fin 2)) := rfl
  rw [LinearMap.sub_apply, e1, e2, sub_self, e3]

/-- Bounded commutators with `C = 0` (Tier T1 — proved):
    `[D, π f] = 0` since `π` is scalar. This is the proof of the `hbddComm`
    field; the `BoundedAnalyticTriple` instance itself is not formed because
    `hcompactRes` is opaque. -/
theorem bddComm (f : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℂ (Fin 2),
      @nrm pauliAnalytic ((pauliD * repScal f - repScal f * pauliD) x)
        ≤ C * @nrm pauliAnalytic x := by
  refine ⟨0, le_rfl, fun x => ?_⟩
  rw [comm_repScal_eq_zero f]
  have hz : ((0 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) x)
      = (0 : EuclideanSpace ℂ (Fin 2)) := rfl
  rw [hz, nrm_eq_norm, nrm_eq_norm, norm_zero, zero_mul]

/-- Bounded representation with `C = ‖a‖` (Tier T1 — proved).
    This is the proof of the `hbddRep` field. -/
theorem bddRep (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℂ (Fin 2),
      @nrm pauliAnalytic ((repScal a) x) ≤ C * @nrm pauliAnalytic x := by
  refine ⟨‖a‖, norm_nonneg _, fun x => ?_⟩
  have hπx : (repScal a) x = a • x := by
    rw [repScal_smul_one a, LinearMap.smul_apply, Module.End.one_apply]
  rw [hπx, nrm_eq_norm, nrm_eq_norm, norm_smul]

/-- Every continuous-linear endomorphism of `S` is a compact operator
    (Tier T1 — proved). Finite-dimensionality is the whole proof. -/
theorem end_compact (T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    IsCompactOperator (⇑T) :=
  isCompactOperator_of_locallyCompactSpace_dom T

/-- Applied to `D` (Tier T1 — proved): `D`, as a continuous-linear map, is a
    compact operator. This is the real mathematical content of `hcompactRes`
    for this model. `HasCompactResolvent` itself is an opaque def and cannot
    be inhabited — so no `BoundedAnalyticTriple` instance is formed (the honest
    PARTIAL verdict on debt 2). -/
theorem pauliD_compact :
    IsCompactOperator (⇑(Module.End.toContinuousLinearMap _ pauliD)) :=
  end_compact _

-- ============================================================================
-- §7. Completeness — debt 3 (verified instance)
-- ============================================================================

-- Debt 3: `CompleteSpace (EuclideanSpace ℂ (Fin 2))` is already an instance
-- (verified 2026-10-10 by `inferInstance`).
example : CompleteSpace (EuclideanSpace ℂ (Fin 2)) := inferInstance

-- ============================================================================
-- §8. FactorOrderZeroOne — debt 4 discharged (T1)
-- ============================================================================

/-- Order-zero (Tier T1 — proved): scalars commute with their shadows. -/
theorem hord0' (f g : ℂ) :
    tripleData.π f * tripleData.conjJ (tripleData.π g)
      = tripleData.conjJ (tripleData.π g) * tripleData.π f := by
  have hmul : ∀ a b : ℂ, (a • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))) * (b • 1)
      = (a * b) • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
    intro a b
    rw [← Algebra.algebraMap_eq_smul_one a, ← Algebra.algebraMap_eq_smul_one b,
      ← map_mul, Algebra.algebraMap_eq_smul_one (a * b)]
  have e1 : tripleData.π f * tripleData.conjJ (tripleData.π g)
      = (f * g) • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
    show repScal f * conjJ2 (repScal g) = _
    rw [repScal_smul_one f]
    have hcg : conjJ2 (repScal g) = g • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
      rw [repScal_smul_one g, map_smul, conjJ2_one]
    rw [hcg, hmul]
  have e2 : tripleData.conjJ (tripleData.π g) * tripleData.π f
      = (g * f) • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
    show conjJ2 (repScal g) * repScal f = _
    rw [repScal_smul_one f]
    have hcg : conjJ2 (repScal g) = g • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2))) := by
      rw [repScal_smul_one g, map_smul, conjJ2_one]
    rw [hcg, hmul]
  rw [e1, e2, mul_comm f g]

/-- Order-one (Tier T1 — proved): `[D, π f] = 0`, so both sides vanish. -/
theorem hord1' (f g : ℂ) :
    (tripleData.D * tripleData.π f - tripleData.π f * tripleData.D)
        * tripleData.conjJ (tripleData.π g)
      = tripleData.conjJ (tripleData.π g)
        * (tripleData.D * tripleData.π f - tripleData.π f * tripleData.D) := by
  show (pauliD * repScal f - repScal f * pauliD) * conjJ2 (repScal g)
    = conjJ2 (repScal g) * (pauliD * repScal f - repScal f * pauliD)
  rw [comm_repScal_eq_zero f, zero_mul, mul_zero]

/-- `FactorOrderZeroOne` for the Pauli triple (Tier T1 — instance): debt 4 discharged. -/
instance pauliOrderZeroOne : FactorOrderZeroOne tripleData where
  hord0 := hord0'
  hord1 := hord1'

-- ============================================================================
-- §9. Tier ledger check
-- ============================================================================

#print axioms pauliGrading_sq
#print axioms pauliD_anticomm
#print axioms repScal_even
#print axioms conjJ2_mul
#print axioms conjJ2_inv
#print axioms conjJ2_one
#print axioms conjJ2_pauliD
#print axioms conjJ2_pauliGrading
#print axioms Janti2_sq
#print axioms Janti2_pauliD
#print axioms Janti2_pauliGrading
#print axioms hsesq_symm'
#print axioms hiprod_pos'
#print axioms hiprod_def'
#print axioms hJanti_iprod'
#print axioms nrm_eq_norm
#print axioms bddComm
#print axioms bddRep
#print axioms end_compact
#print axioms pauliD_compact
#print axioms hord0'
#print axioms hord1'

end ThetLogos
