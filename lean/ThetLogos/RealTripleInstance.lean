/-
# ThetLogos.RealTripleInstance — ROPE BRIDGE (B): the ℂ³² seat carries a
  `RealFiniteFactor` (content module behind `RealTripleDataPin`)

The instance half of Rope Bridge (B), behind the frozen interface of
`ThetLogos.RealTripleDataPin`. Design of record:
`your_files/rope-bridge-b-design-scope-2026-11-08.md` (verdict BUILD
WITH CHANGES, band M, 22–32 strict). The §0 adoption is recorded on
the pin's face; it is not re-argued here.

## What this module proves, and what it does not

It proves: the concrete seat — `A := SMAlgebra`,
`S := EuclideanSpace ℂ I32`, `π := endAlgEquiv32.symm ∘ pi1`, at the
stop pin's frozen Yukawa parameters — carries a `RealFiniteFactor`
whose operator data is exactly the stop pin's §1 packaging
(`realFiniteFactorSM`, `realSmInstanceTarget_holds`). The two
frameworks — the generic triple framework and the concrete ℂ³² seat —
are thereby joined at the algebra seam by a real-species class with a
landed instance, and the corpus's structural sentence ("the seat's
representations are *-representations of a real *-algebra") is a class
the tree carries, not a stop record's prose.

It does NOT prove: anything about `TripleData` itself (untouched);
any new relation at the seat (every field discharges from a landed
citation or from one of the two named new proofs below); any dial.

## The two genuinely new proofs (design §2.2)

* `sesq32_end_adjoint` — the Euclidean adjoint identity under
  `endAlgEquiv32`: the bridge that turns `pi1`'s matrix-level star law
  (DialOneBase clause 3) into the class's form-level `hπ_star`.
* `pi1End_smul_real` — the ℝ-scalar law for `pi1`, by the entry
  argument over `pi1`'s table: every leaf is ℂ-linear or star-twisted
  in a single component, and star-twisted leaves scale by
  `star (r : ℂ) = (r : ℂ)` for real `r`. This is the exact analogue of
  `AlgHom.commutes'`, FALSE over ℂ at this seat (the FiniteTripleInstance
  stop, reason (3)) and TRUE over ℝ — the mathematical heart of the
  class.

Everything else is the algebra bundle of design §2.1 (the af-operations
installed as the operations of record, componentwise) and the stop
pin's frozen §3 discharge map, transported through `endAlgEquiv32`.

**Global side effect, stated at full rank** (design §2.1): §1 installs
instances on `SMAlgebra` tree-wide (any future `a * b` on `AF` resolves
to `afMul`, etc.). Existing statements keep their meaning because the
operations ARE the af-operations; a surprise diamond in any consumer
is K-ROPE-BUNDLE's blast radius, and the integration root build is
its check.

## Kills

K-ROPE-BUNDLE and K-ROPE-SPECIES armed (watch-list: `pi1End_smul_real`,
`sesq32_end_adjoint`, the `hπeven` transport); neither fired.
K-MIR-FIAT / K-MIR-PROXY / K-MIR-DUP do not fire by construction:
nothing is postulated, π is the seat's own `pi1`, the packaging is
imported from the stop pin, not re-declared.

## Faces

NO CLAIM. Dials 0/4; Dial 1 = 0. Pre-registered DIAL-INELIGIBLE.
Tier map: T1 assembly over T1 citations plus the two T1 proof
obligations above; the class it instantiates is T2 design. Working
label only — the public name is Zero's hand.

**As built** (counted at the lane): 61 theorems — 25 in §1 (the 21
component simp lemmas of the af-operations, the installed unit and
zero, and `afNeg`'s components; `ofNat_succ_cast`; the
characterizations `afAlgebraMap_apply`, `af_smul_apply`; and
`star_ofReal`), 13 in §2, 22 in §3, and the target discharge — plus
6 instances and 3 definitions (`afNeg`, `pi1End`,
`realFiniteFactorSM`). The design priced 19–23 theorems + ~22
defs/instances for the whole build; the excess over the band is §1
component infrastructure and §2's coordinate lemmas
(`basis32_repr_apply`, `toMatrix32_symm`, `endAlgEquiv32_symm_repr`,
`sesq32_apply`), stated here at full rank.
-/

import ThetLogos.RealTripleDataPin
import ThetLogos.Track1RouteB
import ThetLogos.DialOneSeatTiePin
import ThetLogos.DialOneGammaTraceChecks

namespace ThetLogos.RealTripleInstance

open ThetLogos.FiniteTripleInstancePin
open ThetLogos.RealTripleDataPin
open ThetLogos.PreOptionARepresentation
open scoped Matrix

/-! ## §1. The algebra bundle on `SMAlgebra`

The af-operations installed as the operations of record, so that every
landed law stated against `afMul` / `afAdd` / `afStar` / `afOne` /
`afZero` transfers to the instance operations definitionally. Only
the ℝ species is installed (design §6, change 1): no `Algebra ℂ AF`,
no `StarModule ℂ AF` — the false species' furniture is not built.
All instances carry explicit names. -/

/-- The negation on `AF`, componentwise (NEW definition — no `afNeg`
    exists in-tree). -/
def afNeg (a : AF) : AF := ⟨-a.u1, -a.q, -a.color⟩

@[simp] theorem afNeg_u1 (a : AF) : (afNeg a).u1 = -a.u1 := rfl
@[simp] theorem afNeg_q (a : AF) : (afNeg a).q = -a.q := rfl
@[simp] theorem afNeg_color (a : AF) : (afNeg a).color = -a.color := rfl

/-- The successor cast in `ℤ`, in the form the `zsmul` axioms take
    (`Int.ofNat_succ` does not exist in this pin). -/
theorem ofNat_succ_cast (n : ℕ) :
    Int.ofNat (n + 1) = Int.ofNat n + 1 :=
  rfl

/-- The additive commutative group on `AF`: operations are `afAdd`,
    `afZero`, `afNeg`; every law is componentwise through
    `PreOptionARepresentation.ext_iff`. -/
instance instAddCommGroupAF : AddCommGroup AF where
  add := afAdd
  zero := afZero
  neg := afNeg
  sub := fun a b => afAdd a (afNeg b)
  add_assoc a b c := by
    show afAdd (afAdd a b) c = afAdd a (afAdd b c)
    exact ext_iff.mpr ⟨add_assoc _ _ _, add_assoc _ _ _, add_assoc _ _ _⟩
  zero_add a := by
    show afAdd afZero a = a
    exact ext_iff.mpr ⟨zero_add _, zero_add _, zero_add _⟩
  add_zero a := by
    show afAdd a afZero = a
    exact ext_iff.mpr ⟨add_zero _, add_zero _, add_zero _⟩
  nsmul := fun n a => ⟨n • a.u1, n • a.q, n • a.color⟩
  nsmul_zero a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℕ) • a.u1 = 0
      exact zero_nsmul _
    · show (0 : ℕ) • a.q = 0
      exact zero_nsmul _
    · show (0 : ℕ) • a.color = 0
      exact zero_nsmul _
  nsmul_succ n a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (n + 1) • a.u1 = n • a.u1 + a.u1
      exact succ_nsmul _ _
    · show (n + 1) • a.q = n • a.q + a.q
      exact succ_nsmul _ _
    · show (n + 1) • a.color = n • a.color + a.color
      exact succ_nsmul _ _
  sub_eq_add_neg a b := rfl
  zsmul := fun z a => ⟨z • a.u1, z • a.q, z • a.color⟩
  zsmul_zero' a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℤ) • a.u1 = 0
      exact zero_zsmul _
    · show (0 : ℤ) • a.q = 0
      exact zero_zsmul _
    · show (0 : ℤ) • a.color = 0
      exact zero_zsmul _
  zsmul_succ' n a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (Int.ofNat (n + 1)) • a.u1 = (Int.ofNat n) • a.u1 + a.u1
      rw [ofNat_succ_cast]
      exact add_one_zsmul _ _
    · show (Int.ofNat (n + 1)) • a.q = (Int.ofNat n) • a.q + a.q
      rw [ofNat_succ_cast]
      exact add_one_zsmul _ _
    · show (Int.ofNat (n + 1)) • a.color = (Int.ofNat n) • a.color + a.color
      rw [ofNat_succ_cast]
      exact add_one_zsmul _ _
  zsmul_neg' n a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (Int.negSucc n) • a.u1 = -((Int.ofNat (n + 1)) • a.u1)
      rw [Int.negSucc_eq, neg_zsmul, ofNat_succ_cast]
      rfl
    · show (Int.negSucc n) • a.q = -((Int.ofNat (n + 1)) • a.q)
      rw [Int.negSucc_eq, neg_zsmul, ofNat_succ_cast]
      rfl
    · show (Int.negSucc n) • a.color = -((Int.ofNat (n + 1)) • a.color)
      rw [Int.negSucc_eq, neg_zsmul, ofNat_succ_cast]
      rfl
  neg_add_cancel a := by
    show afAdd (afNeg a) a = afZero
    exact ext_iff.mpr ⟨neg_add_cancel _, neg_add_cancel _, neg_add_cancel _⟩
  add_comm a b := by
    show afAdd a b = afAdd b a
    exact ext_iff.mpr ⟨add_comm _ _, add_comm _ _, add_comm _ _⟩

/-- The semiring on `AF`: multiplication is `afMul`, unit is `afOne`;
    laws componentwise. -/
instance instSemiringAF : Semiring AF where
  add := afAdd
  zero := afZero
  nsmul := fun n a => ⟨n • a.u1, n • a.q, n • a.color⟩
  nsmul_zero a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℕ) • a.u1 = 0
      exact zero_nsmul _
    · show (0 : ℕ) • a.q = 0
      exact zero_nsmul _
    · show (0 : ℕ) • a.color = 0
      exact zero_nsmul _
  nsmul_succ n a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (n + 1) • a.u1 = n • a.u1 + a.u1
      exact succ_nsmul _ _
    · show (n + 1) • a.q = n • a.q + a.q
      exact succ_nsmul _ _
    · show (n + 1) • a.color = n • a.color + a.color
      exact succ_nsmul _ _
  mul := afMul
  one := afOne
  add_assoc a b c := by
    show afAdd (afAdd a b) c = afAdd a (afAdd b c)
    exact ext_iff.mpr ⟨add_assoc _ _ _, add_assoc _ _ _, add_assoc _ _ _⟩
  zero_add a := by
    show afAdd afZero a = a
    exact ext_iff.mpr ⟨zero_add _, zero_add _, zero_add _⟩
  add_zero a := by
    show afAdd a afZero = a
    exact ext_iff.mpr ⟨add_zero _, add_zero _, add_zero _⟩
  add_comm a b := by
    show afAdd a b = afAdd b a
    exact ext_iff.mpr ⟨add_comm _ _, add_comm _ _, add_comm _ _⟩
  mul_assoc a b c := by
    show afMul (afMul a b) c = afMul a (afMul b c)
    exact ext_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _, mul_assoc _ _ _⟩
  one_mul a := by
    show afMul afOne a = a
    exact ext_iff.mpr ⟨one_mul _, one_mul _, one_mul _⟩
  mul_one a := by
    show afMul a afOne = a
    exact ext_iff.mpr ⟨mul_one _, mul_one _, mul_one _⟩
  left_distrib a b c := by
    show afMul a (afAdd b c) = afAdd (afMul a b) (afMul a c)
    exact ext_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _, left_distrib _ _ _⟩
  right_distrib a b c := by
    show afMul (afAdd a b) c = afAdd (afMul a c) (afMul b c)
    exact ext_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _, right_distrib _ _ _⟩
  zero_mul a := by
    show afMul afZero a = afZero
    exact ext_iff.mpr ⟨zero_mul _, zero_mul _, zero_mul _⟩
  mul_zero a := by
    show afMul a afZero = afZero
    exact ext_iff.mpr ⟨mul_zero _, mul_zero _, mul_zero _⟩

/-- The ring on `AF`, assembled from the semiring and the additive
    group (their operations are the same af-operations, so the merge
    is definitional). -/
instance instRingAF : Ring AF :=
  { instSemiringAF, instAddCommGroupAF with }

/-- The star ring on `AF`: the star is `afStar`; involutivity,
    anti-multiplicativity and additivity are componentwise (`star` on
    ℂ; `Matrix.conjTranspose` on the matrix components). -/
instance instStarRingAF : StarRing AF where
  star := afStar
  star_involutive a := by
    show afStar (afStar a) = a
    exact ext_iff.mpr ⟨star_star _, Matrix.conjTranspose_conjTranspose _,
      Matrix.conjTranspose_conjTranspose _⟩
  star_mul a b := by
    show afStar (afMul a b) = afMul (afStar b) (afStar a)
    exact ext_iff.mpr ⟨star_mul _ _, Matrix.conjTranspose_mul _ _,
      Matrix.conjTranspose_mul _ _⟩
  star_add a b := by
    show afStar (afAdd a b) = afAdd (afStar a) (afStar b)
    exact ext_iff.mpr ⟨star_add _ _, Matrix.conjTranspose_add _ _,
      Matrix.conjTranspose_add _ _⟩

/-- Component projections of the installed operations, for rewriting
    in the rest of the module (each is `rfl`: the operations ARE the
    af-operations). -/
@[simp] theorem mul_u1 (a b : AF) : (a * b).u1 = a.u1 * b.u1 := rfl
@[simp] theorem mul_q (a b : AF) : (a * b).q = a.q * b.q := rfl
@[simp] theorem mul_color (a b : AF) : (a * b).color = a.color * b.color := rfl
@[simp] theorem add_u1 (a b : AF) : (a + b).u1 = a.u1 + b.u1 := rfl
@[simp] theorem add_q (a b : AF) : (a + b).q = a.q + b.q := rfl
@[simp] theorem add_color (a b : AF) : (a + b).color = a.color + b.color := rfl
@[simp] theorem star_u1 (a : AF) : (star a).u1 = star a.u1 := rfl
@[simp] theorem star_q (a : AF) : (star a).q = a.qᴴ := rfl
@[simp] theorem star_color (a : AF) : (star a).color = a.colorᴴ := rfl
@[simp] theorem neg_u1 (a : AF) : (-a).u1 = -a.u1 := rfl
@[simp] theorem neg_q (a : AF) : (-a).q = -a.q := rfl
@[simp] theorem neg_color (a : AF) : (-a).color = -a.color := rfl
@[simp] theorem one_u1 : (1 : AF).u1 = 1 := rfl
@[simp] theorem one_q : (1 : AF).q = 1 := rfl
@[simp] theorem one_color : (1 : AF).color = 1 := rfl
@[simp] theorem zero_u1 : (0 : AF).u1 = 0 := rfl
@[simp] theorem zero_q : (0 : AF).q = 0 := rfl
@[simp] theorem zero_color : (0 : AF).color = 0 := rfl

/-- The ℝ-algebra on `AF`: the algebra map sends `r` to the diagonal
    real element `⟨(r : ℂ), (r : ℂ) • 1, (r : ℂ) • 1⟩`, and the scalar
    action is componentwise (characterized in `af_smul_apply`). -/
instance instAlgebraRealAF : Algebra ℝ AF where
  algebraMap :=
    { toFun := fun r => ⟨(r : ℂ), (r : ℂ) • 1, (r : ℂ) • 1⟩
      map_one' := by
        apply ext_iff.mpr
        refine ⟨?_, ?_, ?_⟩ <;> simp
      map_mul' := by
        intro r s
        apply ext_iff.mpr
        refine ⟨?_, ?_, ?_⟩
        · simp
        · show ((r * s : ℝ) : ℂ) • (1 : Matrix I2 I2 ℂ)
            = (r : ℂ) • (1 : Matrix I2 I2 ℂ) * ((s : ℂ) • 1)
          rw [Complex.ofReal_mul, Matrix.smul_mul, Matrix.one_mul,
            smul_smul]
        · show ((r * s : ℝ) : ℂ) • (1 : Matrix I3 I3 ℂ)
            = (r : ℂ) • (1 : Matrix I3 I3 ℂ) * ((s : ℂ) • 1)
          rw [Complex.ofReal_mul, Matrix.smul_mul, Matrix.one_mul,
            smul_smul]
      map_add' := by
        intro r s
        apply ext_iff.mpr
        refine ⟨?_, ?_, ?_⟩ <;> simp [add_smul]
      map_zero' := by
        apply ext_iff.mpr
        refine ⟨?_, ?_, ?_⟩ <;> simp }
  commutes' r a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (r : ℂ) * a.u1 = a.u1 * (r : ℂ)
      exact mul_comm _ _
    · show (r : ℂ) • (1 : Matrix I2 I2 ℂ) * a.q = a.q * ((r : ℂ) • 1)
      simp [Matrix.smul_mul, Matrix.mul_smul]
    · show (r : ℂ) • (1 : Matrix I3 I3 ℂ) * a.color = a.color * ((r : ℂ) • 1)
      simp [Matrix.smul_mul, Matrix.mul_smul]
  smul_def' r a := by
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (r : ℂ) * a.u1 = (r : ℂ) * a.u1
      rfl
    · show (r : ℂ) • a.q = (r : ℂ) • (1 : Matrix I2 I2 ℂ) * a.q
      simp [Matrix.smul_mul]
    · show (r : ℂ) • a.color = (r : ℂ) • (1 : Matrix I3 I3 ℂ) * a.color
      simp [Matrix.smul_mul]
  toSMul :=
    ⟨fun r a => ⟨(r : ℂ) * a.u1, (r : ℂ) • a.q, (r : ℂ) • a.color⟩⟩

/-- The algebra map of the ℝ-algebra, as a term (the §1
    characterization the rest of the module rewrites by). -/
theorem afAlgebraMap_apply (r : ℝ) :
    algebraMap ℝ AF r = ⟨(r : ℂ), (r : ℂ) • 1, (r : ℂ) • 1⟩ := rfl

/-- The scalar action of the ℝ-algebra, as a term. -/
theorem af_smul_apply (r : ℝ) (a : AF) :
    r • a = ⟨(r : ℂ) * a.u1, (r : ℂ) • a.q, (r : ℂ) • a.color⟩ := by
  rw [Algebra.smul_def, afAlgebraMap_apply]
  apply ext_iff.mpr
  refine ⟨rfl, ?_, ?_⟩ <;> simp [Matrix.smul_mul]

/-- Stars fix real scalars in `ℂ`. -/
theorem star_ofReal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simp

/-- The star module over ℝ: `star (r • a) = r • star a`,
    componentwise — the ℂ component is star-of-real-cast, the matrix
    components are conjugate-transpose of a real-cast scalar
    multiple. -/
instance instStarModuleRealAF : StarModule ℝ AF where
  star_smul r a := by
    rw [af_smul_apply, af_smul_apply]
    apply ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · show star ((r : ℂ) * a.u1) = (r : ℂ) * star a.u1
      rw [star_mul, star_ofReal, mul_comm]
    · show ((r : ℂ) • a.q)ᴴ = (r : ℂ) • a.qᴴ
      rw [Matrix.conjTranspose_smul, star_ofReal]
    · show ((r : ℂ) • a.color)ᴴ = (r : ℂ) • a.colorᴴ
      rw [Matrix.conjTranspose_smul, star_ofReal]

/-! ## §2. The representation, transported

`pi1End a := endAlgEquiv32.symm (pi1 a)`. The one/mul/add/even laws
are Dial-One citations transported through the algebra equivalence;
the star law goes through the new sesquilinear bridge; the ℝ-scalar
law is the new entry proof. -/

/-- The transported representation: `pi1` moved from matrices to
    endomorphisms of `EuclideanSpace ℂ I32` along the stop pin's
    `endAlgEquiv32`. -/
noncomputable def pi1End (a : AF) : Module.End ℂ (EuclideanSpace ℂ I32) :=
  endAlgEquiv32.symm (Track1RouteB.pi1 a)

/-- Transported unitality (DialOneBase clause 4, `pi1_one`). -/
theorem pi1End_one : pi1End 1 = 1 := by
  show endAlgEquiv32.symm (Track1RouteB.pi1 afOne) = 1
  rw [Track1RouteB.pi1_one]
  exact map_one _

/-- Transported multiplicativity (DialOneBase clause 1, `pi1_afMul`;
    the `*` on `AF` is `afMul` by §1's construction). -/
theorem pi1End_mul (a b : AF) : pi1End (a * b) = pi1End a * pi1End b := by
  show endAlgEquiv32.symm (Track1RouteB.pi1 (afMul a b)) = _
  rw [Track1RouteB.pi1_afMul]
  exact map_mul _ _ _

/-- Transported additivity (DialOneBase clause 2, `pi1_afAdd`). -/
theorem pi1End_add (a b : AF) : pi1End (a + b) = pi1End a + pi1End b := by
  show endAlgEquiv32.symm (Track1RouteB.pi1 (afAdd a b)) = _
  rw [Track1RouteB.pi1_afAdd]
  exact map_add _ _ _

/-- `basis32.repr` is coordinate evaluation (the corpus idiom of
    `ConcreteFiniteModel.basis2_repr_apply`). -/
theorem basis32_repr_apply (z : EuclideanSpace ℂ I32) (k : I32) :
    basis32.repr z k = z.ofLp k := by
  show ((EuclideanSpace.basisFun I32 ℂ).toBasis.repr z) k = z.ofLp k
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- The matrix of a transported matrix is itself (the corpus idiom
    of `ConcreteFiniteModel.toMatrix_symm`). -/
theorem toMatrix32_symm (M : Matrix I32 I32 ℂ) :
    LinearMap.toMatrix basis32 basis32 (endAlgEquiv32.symm M) = M := by
  show endAlgEquiv32.toLinearEquiv (endAlgEquiv32.symm M) = M
  have hsym : ∀ x, endAlgEquiv32.symm x
      = endAlgEquiv32.toLinearEquiv.symm x := fun x => rfl
  rw [hsym]
  exact LinearEquiv.apply_symm_apply _ _

/-- A transported matrix acts by matrix-vector multiplication in
    coordinates (the corpus idiom of `ConcreteFiniteModel.symmM_repr`). -/
theorem endAlgEquiv32_symm_repr (M : Matrix I32 I32 ℂ)
    (u : EuclideanSpace ℂ I32) :
    basis32.repr (endAlgEquiv32.symm M u)
      = Matrix.mulVec M (basis32.repr u) := by
  have h := LinearMap.toMatrix_mulVec_repr basis32 basis32
    (endAlgEquiv32.symm M) u
  rwa [toMatrix32_symm M] at h

/-- The action of a transported matrix on coordinates:
    `(endAlgEquiv32.symm N) u` is the matrix action `N *ᵥ u`. -/
theorem endAlgEquiv32_symm_apply (N : Matrix I32 I32 ℂ)
    (u : EuclideanSpace ℂ I32) (k : I32) :
    (endAlgEquiv32.symm N u) k = ∑ j, N k j * u j := by
  have h1 : (endAlgEquiv32.symm N u) k
      = (Matrix.mulVec N (basis32.repr u)) k := by
    rw [← basis32_repr_apply ((endAlgEquiv32.symm N) u) k,
      endAlgEquiv32_symm_repr]
  rw [h1]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [basis32_repr_apply]

/-- `sesq32` in coordinates: the ℓ² inner product (the corpus idiom
    of `ConcreteStar.inner_coord`). -/
theorem sesq32_apply (u v : EuclideanSpace ℂ I32) :
    sesq32 u v = ∑ i, star (u i) * v i := by
  show innerₛₗ ℂ u v = _
  rw [innerₛₗ_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply', starRingEnd_apply]

/-- **NEW PROOF (bridge).** The Euclidean adjoint identity under
    `endAlgEquiv32`: the sesquilinear form `sesq32` (the ℓ² inner
    product) pairs `M` against `Mᴴ`. This is what turns `pi1`'s
    matrix-level star law into the class's form-level star law. -/
theorem sesq32_end_adjoint (M : Matrix I32 I32 ℂ)
    (x y : EuclideanSpace ℂ I32) :
    sesq32 (endAlgEquiv32.symm M x) y
      = sesq32 x (endAlgEquiv32.symm Mᴴ y) := by
  rw [sesq32_apply, sesq32_apply]
  simp only [endAlgEquiv32_symm_apply, star_sum, star_mul,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The form-level star law for `pi1End` (DialOneBase clause 3,
    `pi1_afStar`, at matrix level, transported through
    `sesq32_end_adjoint`). -/
theorem pi1End_star_sesq (a : AF) (x y : EuclideanSpace ℂ I32) :
    sesq32 (pi1End (star a) x) y = sesq32 x (pi1End a y) := by
  have h : pi1End (star a) = endAlgEquiv32.symm (Track1RouteB.pi1 a)ᴴ := by
    show endAlgEquiv32.symm (Track1RouteB.pi1 (afStar a)) = _
    rw [Track1RouteB.pi1_afStar]
  rw [h, sesq32_end_adjoint, Matrix.conjTranspose_conjTranspose]
  rfl

/-- **NEW PROOF (the scalar law at matrix level).** `pi1` scales by
    `(r : ℂ)` under the componentwise real scaling of its argument:
    every leaf of `pi1`'s table is ℂ-linear in a single component
    (`a.q` entries, `a.u1`) or star-twisted in a single component
    (`star a.u1`, `star (a.color …)`), and star-twisted leaves scale
    by `star (r : ℂ) = (r : ℂ)` because `r` is real. The proof is the
    entry argument: unfold the table, split its branches (the branch
    conditions depend only on the indices), and close each leaf. -/
theorem pi1_smul_real (r : ℝ) (a : AF) :
    Track1RouteB.pi1 ⟨(r : ℂ) * a.u1, (r : ℂ) • a.q, (r : ℂ) • a.color⟩
      = (r : ℂ) • Track1RouteB.pi1 a := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold Track1RouteB.pi1
  dsimp only
  split_ifs <;>
    simp [Matrix.smul_apply, smul_eq_mul, star_mul, mul_comm, mul_left_comm]

/-- The ℝ-scalar law for `pi1End` — the class's `hπ_smul`. The exact
    analogue of `AlgHom.commutes'`, false over ℂ at this seat and
    true over ℝ. -/
theorem pi1End_smul_real (r : ℝ) (a : AF) :
    pi1End (r • a) = (r : ℂ) • pi1End a := by
  rw [af_smul_apply]
  show endAlgEquiv32.symm
      (Track1RouteB.pi1 ⟨(r : ℂ) * a.u1, (r : ℂ) • a.q, (r : ℂ) • a.color⟩)
    = (r : ℂ) • pi1End a
  rw [pi1_smul_real]
  exact map_smul _ _ _

/-- Transported grading-evenness (DialOneBase clause 7,
    `pi1_grading_even`). -/
theorem pi1End_even (a : AF) :
    smGrading * pi1End a = pi1End a * smGrading := by
  show endAlgEquiv32.symm gammaF * endAlgEquiv32.symm (Track1RouteB.pi1 a)
    = endAlgEquiv32.symm (Track1RouteB.pi1 a) * endAlgEquiv32.symm gammaF
  rw [← map_mul, ← map_mul, Track1RouteB.pi1_grading_even]

/-! ## §3. The operator relations and the assembly

Every relation is the stop pin's frozen §3 discharge map, transported
through `endAlgEquiv32`. The computation lemmas first: the equiv
applied to the pin's packaging returns the matrices (the coordinate
action itself is §2's `endAlgEquiv32_symm_apply`). -/

/-- Computation: the equiv returns `smGrading`'s matrix. -/
theorem endAlgEquiv32_smGrading : endAlgEquiv32 smGrading = gammaF :=
  AlgEquiv.apply_symm_apply _ _

/-- Computation: the equiv returns `smDiracOp`'s matrix. -/
theorem endAlgEquiv32_smDiracOp (yNu yE yU yD yR : ℂ) :
    endAlgEquiv32 (smDiracOp yNu yE yU yD yR)
      = smDirac yNu yE yU yD yR :=
  AlgEquiv.apply_symm_apply _ _

/-- The grading acts diagonally on coordinates. -/
theorem smGrading_apply (u : EuclideanSpace ℂ I32) (k : I32) :
    smGrading u k = gammaF k k * u k := by
  show (endAlgEquiv32.symm gammaF u) k = _
  rw [endAlgEquiv32_symm_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rw [gammaF_apply_ne (fun h => hjk h.symm), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The Dirac operator acts as its matrix on coordinates. -/
theorem smDiracOp_apply (yNu yE yU yD yR : ℂ)
    (u : EuclideanSpace ℂ I32) (k : I32) :
    smDiracOp yNu yE yU yD yR u k
      = ∑ j, smDirac yNu yE yU yD yR k j * u j :=
  endAlgEquiv32_symm_apply _ _ _

/-- Computation: the equiv applied to `conjJ32 X` is the `UJ`-sandwich
    of the transpose (the pin's definition, unwound). -/
theorem endAlgEquiv32_conjJ32 (X : Module.End ℂ (EuclideanSpace ℂ I32)) :
    endAlgEquiv32 (conjJ32 X) = UJ * (endAlgEquiv32 X)ᵀ * UJ := by
  show endAlgEquiv32 (endAlgEquiv32.symm
    (UJ * (endAlgEquiv32 X).transpose * UJ)) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The `UJ`-sandwich multiplies: `(UJ A UJ)(UJ B UJ) = UJ (A B) UJ`,
    from `UJ * UJ = 1`. -/
theorem UJ_sandwich_mul (A B : Matrix I32 I32 ℂ) :
    (UJ * A * UJ) * (UJ * B * UJ) = UJ * (A * B) * UJ := by
  calc (UJ * A * UJ) * (UJ * B * UJ)
      = UJ * (A * ((UJ * UJ) * B)) * UJ := by
        simp only [Matrix.mul_assoc]
    _ = UJ * (A * B) * UJ := by
        rw [UJ_mul_self, Matrix.one_mul]

/-- `conjJ32` is anti-multiplicative (transpose laws + `UJ_mul_self`,
    via the sandwich). -/
theorem conjJ32_mul (X Y : Module.End ℂ (EuclideanSpace ℂ I32)) :
    conjJ32 (X * Y) = conjJ32 Y * conjJ32 X := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  simp only [endAlgEquiv32_conjJ32, map_mul, Matrix.transpose_mul,
    UJ_sandwich_mul]

/-- `conjJ32` is involutive (entry form, via `UJ_conj_apply` and
    `partner_involutive`). -/
theorem conjJ32_inv (X : Module.End ℂ (EuclideanSpace ℂ I32)) :
    conjJ32 (conjJ32 X) = X := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  rw [endAlgEquiv32_conjJ32, endAlgEquiv32_conjJ32]
  ext i j
  simp only [UJ_conj_apply, Matrix.transpose_apply, partner_involutive]

/-- `conjJ32` fixes the identity. -/
theorem conjJ32_one : conjJ32 1 = 1 := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  rw [endAlgEquiv32_conjJ32, map_one, Matrix.transpose_one,
    Matrix.mul_one, UJ_mul_self]

/-- The bridge behind `hkoD`: self-adjointness of the Dirac operator
    makes its plain transpose equal its entrywise star. -/
theorem dirac_transpose_eq_map_star (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR)ᵀ
      = (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) := by
  ext i j
  have hsa := smDirac_self_adjoint yNu yE yU yD yR
  have h2 : star (smDirac yNu yE yU yD yR j i)
      = smDirac yNu yE yU yD yR i j := by
    have h3 := congrFun (congrFun hsa i) j
    simpa [Matrix.conjTranspose_apply] using h3
  rw [Matrix.transpose_apply, Matrix.map_apply, ← h2, star_star]

/-- `conjJ32` fixes the Dirac operator (KO sign ε′ = +1):
    `smDirac_J_compat` through the transpose bridge. -/
theorem conjJ32_D (yNu yE yU yD yR : ℂ) :
    conjJ32 (smDiracOp yNu yE yU yD yR) = smDiracOp yNu yE yU yD yR := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  rw [endAlgEquiv32_conjJ32, endAlgEquiv32_smDiracOp,
    dirac_transpose_eq_map_star]
  calc UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ
      = (smDirac yNu yE yU yD yR * UJ) * UJ := by
        rw [smDirac_J_compat]
    _ = smDirac yNu yE yU yD yR := by
        rw [Matrix.mul_assoc, UJ_mul_self, Matrix.mul_one]

/-- `gammaF` is symmetric (it is diagonal). -/
theorem gammaF_transpose : gammaFᵀ = gammaF := by
  ext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · rw [h]
  · rw [gammaF_apply_ne h, gammaF_apply_ne (fun hh => h hh.symm)]

/-- `conjJ32` negates the grading (KO sign ε″ = −1):
    `UJ_gammaF_anticommute` through `gammaFᵀ = gammaF`. -/
theorem conjJ32_Γ : conjJ32 smGrading = -smGrading := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  rw [endAlgEquiv32_conjJ32, endAlgEquiv32_smGrading, gammaF_transpose,
    map_neg, endAlgEquiv32_smGrading]
  calc UJ * gammaF * UJ = (UJ * gammaF) * UJ := rfl
    _ = (-gammaF * UJ) * UJ := by rw [UJ_gammaF_anticommute]
    _ = -gammaF := by
        rw [Matrix.mul_assoc, UJ_mul_self, Matrix.mul_one]

/-- The grading squares to one (transported `gammaF_involutive`). -/
theorem smGrading_sq : smGrading * smGrading = 1 := by
  show endAlgEquiv32.symm gammaF * endAlgEquiv32.symm gammaF = 1
  rw [← map_mul, gammaF_involutive]
  exact map_one _

/-- The Dirac operator is grading-odd at end level (transported
    `smDirac_grading_odd`, rearranged). -/
theorem smGrading_D_odd (yNu yE yU yD yR : ℂ) :
    smDiracOp yNu yE yU yD yR * smGrading
      = -(smGrading * smDiracOp yNu yE yU yD yR) := by
  apply (EquivLike.apply_eq_iff_eq endAlgEquiv32).mp
  simp only [endAlgEquiv32_smGrading, endAlgEquiv32_smDiracOp,
    map_mul, map_neg]
  have h := smDirac_grading_odd yNu yE yU yD yR
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

/-- `Janti32` on coordinates (its definition, unwound). -/
theorem Janti32_apply (x : EuclideanSpace ℂ I32) (i : I32) :
    Janti32 x i = star (x (partner i)) := rfl

/-- `Janti32` squares to the identity (KO sign ε = +1):
    `partner_involutive` and `star_star` on coordinates. -/
theorem Janti32_sq :
    Janti32.comp Janti32 = (1 : ℂ) • LinearMap.id := by
  ext x i
  simp [LinearMap.comp_apply, Janti32_apply, partner_involutive]

/-- Diagonal entries of `gammaF` are real. -/
theorem star_gammaF_diag (i : I32) : star (gammaF i i) = gammaF i i := by
  have h := congrFun (congrFun gammaF_self_adjoint i) i
  simpa [Matrix.conjTranspose_apply] using h

/-- The grading flips sign across the partner involution (its
    diagonal is `+1` on sectors 0, 3 and `−1` on sectors 1, 2, and
    `partner` swaps 0 ↔ 2, 1 ↔ 3). -/
theorem gammaF_partner_diag (i : I32) :
    gammaF (partner i) (partner i) = -gammaF i i := by
  have hv : i.val < 32 := i.isLt
  simp only [gammaF, partner_val_eq]
  split_ifs <;> norm_num <;> omega

/-- `Janti32` commutes with the Dirac operator (KO sign ε′ = +1),
    mulVec form of `smDirac_J_compat`: on coordinates the key entry
    identity is `star (D (partner i) j) = D i (partner j)`, the
    `UJ_conj_apply` form of J-compatibility; the sums then agree by
    reindexing along `partner`. -/
theorem Janti32_D (yNu yE yU yD yR : ℂ) :
    Janti32.comp (smDiracOp yNu yE yU yD yR)
      = (1 : ℂ) • ((smDiracOp yNu yE yU yD yR).comp Janti32) := by
  have hDstar : ∀ i j : I32,
      star (smDirac yNu yE yU yD yR (partner i) j)
        = smDirac yNu yE yU yD yR i (partner j) := by
    intro i j
    have h2 : UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ
        = smDirac yNu yE yU yD yR := by
      calc UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ
          = (smDirac yNu yE yU yD yR * UJ) * UJ := by
            rw [smDirac_J_compat]
        _ = smDirac yNu yE yU yD yR := by
            rw [Matrix.mul_assoc, UJ_mul_self, Matrix.mul_one]
    have h3 := congrFun (congrFun h2 i) (partner j)
    rwa [UJ_conj_apply, Matrix.map_apply, partner_involutive] at h3
  ext x i
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, one_mul, smDiracOp_apply, Janti32_apply, star_sum,
    star_mul, hDstar]
  rw [← Equiv.sum_comp
    (⟨partner, partner, fun i => partner_involutive i,
      fun i => partner_involutive i⟩ : I32 ≃ I32)
    (fun j => star (x j) * smDirac yNu yE yU yD yR i (partner j))]
  simp only [Equiv.coe_fn_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partner_involutive, mul_comm]

/-- `Janti32` anticommutes with the grading (KO sign ε″ = −1), on
    coordinates: the diagonal sign flips across `partner`. -/
theorem Janti32_Γ :
    Janti32.comp smGrading
      = (-1 : ℂ) • (smGrading.comp Janti32) := by
  ext x i
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, smGrading_apply, Janti32_apply, star_mul,
    gammaF_partner_diag, star_neg, star_gammaF_diag]
  ring

/-- The grading is self-adjoint for `sesq32` (its diagonal entries
    are real). -/
theorem smGrading_sesq_selfadj (x y : EuclideanSpace ℂ I32) :
    sesq32 (smGrading x) y = sesq32 x (smGrading y) := by
  rw [sesq32_apply, sesq32_apply]
  simp only [smGrading_apply, star_mul, star_gammaF_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## The assembly -/

/-- **The real finite factor at the concrete seat**: `SMAlgebra` acting
    on `EuclideanSpace ℂ I32` through `pi1`, with the stop pin's
    operator packaging. The instance fields of the class are the
    §1 bundle (for `SMAlgebra`) and the ambient instances (for the
    Euclidean space); every law field is a §2/§3 discharge above. -/
@[instance_reducible]
noncomputable def realFiniteFactorSM (yNu yE yU yD yR : ℂ) :
    RealFiniteFactor where
  toRealTripleData :=
    { A := SMAlgebra
      S := EuclideanSpace ℂ I32
      sesq := sesq32
      π := pi1End
      hπ_one := pi1End_one
      hπ_mul := pi1End_mul
      hπ_add := pi1End_add
      hπ_star := pi1End_star_sesq
      hπ_smul := pi1End_smul_real
      D := smDiracOp yNu yE yU yD yR
      Γ := smGrading
      hΓsq := smGrading_sq
      hΓD := smGrading_D_odd yNu yE yU yD yR
      hπeven := pi1End_even
      conjJ := conjJ32
      hconjJ_mul := conjJ32_mul
      hconjJ_inv := conjJ32_inv
      hconjJ_one := conjJ32_one
      ko := ko6sig
      hkoD := by
        have hc : (ko6sig.eps' : ℂ) = 1 := by norm_num [ko6sig]
        rw [hc, one_smul]
        exact conjJ32_D yNu yE yU yD yR
      hkoΓ := by
        have hc : (ko6sig.eps'' : ℂ) = -1 := by norm_num [ko6sig]
        rw [hc, neg_one_smul]
        exact conjJ32_Γ
      Janti := Janti32
      hJanti_sq := by
        have hc : (ko6sig.eps : ℂ) = 1 := by norm_num [ko6sig]
        rw [hc]
        exact Janti32_sq
      hJanti_D := by
        have hc : (ko6sig.eps' : ℂ) = 1 := by norm_num [ko6sig]
        rw [hc]
        exact Janti32_D yNu yE yU yD yR
      hJanti_Γ := by
        have hc : (ko6sig.eps'' : ℂ) = -1 := by norm_num [ko6sig]
        rw [hc]
        exact Janti32_Γ
      ηsym := smGrading
      hηsym_sq := smGrading_sq
      hηsym_selfadj := smGrading_sesq_selfadj }
  ko6 := rfl

/-- **The frozen target of the pin, discharged**: a `RealFiniteFactor`
    whose algebra, spinor module, and operator data are exactly the
    stop pin's packaging of the concrete seat. -/
theorem realSmInstanceTarget_holds (yNu yE yU yD yR : ℂ) :
    realSmInstanceTarget yNu yE yU yD yR :=
  ⟨realFiniteFactorSM yNu yE yU yD yR, rfl, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, rfl⟩

end ThetLogos.RealTripleInstance
