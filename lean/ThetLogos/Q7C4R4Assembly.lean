import Mathlib.Tactic
import ThetLogos.Q7C4R4Realify

/-!
# ThetLogos.Q7C4R4Assembly — the general product-Dirac assembly over ℝ (Q7CR-1b)

**Status: T1 construction brick (general, over factor operators).
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing scoping: `scoping-q7c4r4-gauntlet-2026-10-30.md` §§2, 3
(Q7CR-1), 5. Gates: Q7CR-0 (`ThetLogos.Q7C4R4Post`, the registered
composite `q7c4r4Composite = ((Fin 7 → ℂ) ⊗[ℝ] (Fin 4 → ℂ)) ⊗[ℝ]
Minkowski` with its three registered real pairings) and Q7CR-1a
(`ThetLogos.Q7C4R4Realify`: the `FactorOp n` package for the two
realified complex factors, its transport kit, and the registered
real pairing `factorPair n`).

## What this brick is

The general product-Dirac assembly in Jeff's filed shape, with the
signs explicit:

`D = D₇ ⊗ 1 ⊗ 1 + γ₇ ⊗ D₄ ⊗ 1 + γ₇ ⊗ γ₄ ⊗ D_R`

on the registered composite, parameterized over factor packages:
`F₇ : FactorOp 7` and `F₄ : FactorOp 4` (Q7CR-1a's packages) and
`F_R : FactorOpR`, the native real package for the Minkowski factor
defined in §1 below (operator + grading on `Fin 4 → ℝ`, grading an
involution, both self-adjoint for `minkowskiInner` in form sense,
grading anticommuting with the operator — the same field shape as
Q7CR-1a's). Tensor products of operators are `TensorProduct.map`,
associated as in Q7CR-0's composite: `((— ⊗ —) ⊗ —)`.

**Headline 1 — the D² identity** (§4): `D²` is the Kronecker sum of
the factor squares,
`D² = D₇² ⊗ 1 ⊗ 1 + 1 ⊗ D₄² ⊗ 1 + 1 ⊗ 1 ⊗ D_R²`. This is the
anchor the spectral-action line gates on. Cross-term cancellation
is exactly Q7CR-1a's transported kit: factor anticommutation kills
the mixed terms; `γ₇² = γ₄² = 1` collapses the squares.

**Headline 2 — self-adjointness** (§5): `D` is self-adjoint, in
form sense, with respect to Q7CR-0's registered composite pairing.
Landed form: the LIFTED form — the composite pairing is built as a
genuine bilinear form on the whole tensor space (§3, the factorwise
product of the three registered pairings, built by the corpus's own
lift-and-map pattern from `ThetLogos.ProductTriple`), its value on
pure tensors is the product of the factor pairings, and `D`'s
self-adjointness is stated and proved against that lifted form for
all composite vectors, not only pure tensors.

## Fences, on the face

- **Bounded-commutator vacuity caveat (verbatim-tier).** In finite
  dimension bounded commutators are vacuous; the testable content
  here is the D² identity and self-adjointness (and, later,
  spectrum) — never bounded commutators. Nothing in this module
  states or implies a bounded-commutator fact.
- **General over choices.** The assembly and both headlines are
  parameterized over the factor packages: no factor operator is
  chosen anywhere in this module. Specific factor operators are
  Q7CR-2's labeled choices.
- **Kill K-Q7CR-1 (armed at scoping, watched here).** If either
  headline were false as stated — a sign that provably cannot
  cancel, a counterexample at the package level — the filed
  product-Dirac shape dies at full rank; the shape is not weakened
  and no hypothesis is added to save it. Status at landing: the
  kill does NOT fire — both headlines hold in the stated shape,
  over the stated packages, with no strengthened hypothesis.
- NO CLAIM; dials 0/4; no measured number is claimed by this line.
-/

namespace ThetLogos

open TensorProduct

/-! ## §1. The native real factor package for the Minkowski factor -/

/-- **Self-adjointness for the Minkowski form**: an operator `A` on
`Minkowski` is self-adjoint when `minkowskiInner (A x) y =
minkowskiInner x (A y)` for all `x y` (form seat, as everywhere in
this line). -/
def MinkSelfAdjoint (A : Minkowski →ₗ[ℝ] Minkowski) : Prop :=
  ∀ x y, minkowskiInner (A x) y = minkowskiInner x (A y)

/-- **A native real factor package for the R factor** (the Minkowski
seat): an ℝ-linear operator and grading on `Fin 4 → ℝ`, the grading
an involution, both self-adjoint with respect to `minkowskiInner`
in form sense, the grading anticommuting with the operator — the
same field shape as Q7CR-1a's `FactorOp`. -/
structure FactorOpR where
  /-- The factor operator (a choice, in every instantiation). -/
  D : Minkowski →ₗ[ℝ] Minkowski
  /-- The factor grading. -/
  γ : Minkowski →ₗ[ℝ] Minkowski
  γ_invol : γ ∘ₗ γ = 1
  γ_selfadj : MinkSelfAdjoint γ
  D_selfadj : MinkSelfAdjoint D
  anticomm : γ ∘ₗ D + D ∘ₗ γ = 0

/-! ## §2. The triple operator tensor and its algebra kit

Operators on the composite are iterated `TensorProduct.map`s,
associated as in Q7CR-0's composite. The kit is the binary
`TensorProduct.map` algebra (multiplication, one, addition, zero),
iterated once. -/

/-- The tensor product of three operators, associated as in the
registered composite: `X ⊗ₜ Y ⊗ₜ Z = (X ⊗ₜ Y) ⊗ₜ Z` via
`TensorProduct.map`. -/
noncomputable def opTensor3 {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Y : Module.End ℝ B) (Z : Module.End ℝ C) :
    Module.End ℝ ((A ⊗[ℝ] B) ⊗[ℝ] C) :=
  TensorProduct.map (TensorProduct.map X Y) Z

/-- Mixed-product law for the triple tensor. -/
theorem opTensor3_mul {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X₁ X₂ : Module.End ℝ A) (Y₁ Y₂ : Module.End ℝ B)
    (Z₁ Z₂ : Module.End ℝ C) :
    opTensor3 (X₁ * X₂) (Y₁ * Y₂) (Z₁ * Z₂)
      = opTensor3 X₁ Y₁ Z₁ * opTensor3 X₂ Y₂ Z₂ := by
  unfold opTensor3
  rw [TensorProduct.map_mul, TensorProduct.map_mul]

/-- `1 ⊗ₜ 1 ⊗ₜ 1 = 1`. -/
theorem opTensor3_one {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C] :
    opTensor3 (1 : Module.End ℝ A) (1 : Module.End ℝ B)
        (1 : Module.End ℝ C) = 1 := by
  unfold opTensor3
  rw [TensorProduct.map_one, TensorProduct.map_one]

/-- Additivity in the left factor. -/
theorem opTensor3_add_left {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X₁ X₂ : Module.End ℝ A) (Y : Module.End ℝ B) (Z : Module.End ℝ C) :
    opTensor3 (X₁ + X₂) Y Z = opTensor3 X₁ Y Z + opTensor3 X₂ Y Z := by
  unfold opTensor3
  rw [TensorProduct.map_add_left, TensorProduct.map_add_left]

/-- Additivity in the middle factor. -/
theorem opTensor3_add_mid {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Y₁ Y₂ : Module.End ℝ B) (Z : Module.End ℝ C) :
    opTensor3 X (Y₁ + Y₂) Z = opTensor3 X Y₁ Z + opTensor3 X Y₂ Z := by
  unfold opTensor3
  rw [TensorProduct.map_add_right, TensorProduct.map_add_left]

/-- Additivity in the right factor. -/
theorem opTensor3_add_right {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Y : Module.End ℝ B) (Z₁ Z₂ : Module.End ℝ C) :
    opTensor3 X Y (Z₁ + Z₂) = opTensor3 X Y Z₁ + opTensor3 X Y Z₂ := by
  unfold opTensor3
  rw [TensorProduct.map_add_right]

/-- `0 ⊗ₜ Y ⊗ₜ Z = 0`. -/
theorem opTensor3_zero_left {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (Y : Module.End ℝ B) (Z : Module.End ℝ C) :
    opTensor3 (0 : Module.End ℝ A) Y Z = 0 := by
  unfold opTensor3
  rw [TensorProduct.map_zero_left, TensorProduct.map_zero_left]

/-- `X ⊗ₜ 0 ⊗ₜ Z = 0`. -/
theorem opTensor3_zero_mid {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Z : Module.End ℝ C) :
    opTensor3 X (0 : Module.End ℝ B) Z = 0 := by
  unfold opTensor3
  rw [TensorProduct.map_zero_right, TensorProduct.map_zero_left]

/-- `X ⊗ₜ Y ⊗ₜ 0 = 0`. -/
theorem opTensor3_zero_right {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Y : Module.End ℝ B) :
    opTensor3 X Y (0 : Module.End ℝ C) = 0 := by
  unfold opTensor3
  rw [TensorProduct.map_zero_right]

/-- The triple tensor on pure tensors. -/
theorem opTensor3_tmul {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    (X : Module.End ℝ A) (Y : Module.End ℝ B) (Z : Module.End ℝ C)
    (a : A) (b : B) (c : C) :
    opTensor3 X Y Z ((a ⊗ₜ[ℝ] b) ⊗ₜ[ℝ] c)
      = (X a ⊗ₜ[ℝ] Y b) ⊗ₜ[ℝ] Z c := by
  unfold opTensor3
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul]

/-! ## §3 (assembly). The product Dirac, in Jeff's filed shape -/

/-- The triple operator tensor at the registered factors (the
specialization of `opTensor3` to the composite's three seats; its
explicit argument types pin every identity operator in the
assembly's formulas). -/
noncomputable def opTensorQ (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    Module.End ℝ q7c4r4Composite :=
  opTensor3 X Y Z

/-- Mixed-product law at the registered factors. -/
theorem opTensorQ_mul (X₁ X₂ : Module.End ℝ (Fin 7 → ℂ))
    (Y₁ Y₂ : Module.End ℝ (Fin 4 → ℂ))
    (Z₁ Z₂ : Module.End ℝ Minkowski) :
    opTensorQ (X₁ * X₂) (Y₁ * Y₂) (Z₁ * Z₂)
      = opTensorQ X₁ Y₁ Z₁ * opTensorQ X₂ Y₂ Z₂ :=
  opTensor3_mul X₁ X₂ Y₁ Y₂ Z₁ Z₂

/-- Additivity in the left factor, at the registered factors. -/
theorem opTensorQ_add_left (X₁ X₂ : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    opTensorQ (X₁ + X₂) Y Z = opTensorQ X₁ Y Z + opTensorQ X₂ Y Z :=
  opTensor3_add_left X₁ X₂ Y Z

/-- Additivity in the middle factor, at the registered factors. -/
theorem opTensorQ_add_mid (X : Module.End ℝ (Fin 7 → ℂ))
    (Y₁ Y₂ : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    opTensorQ X (Y₁ + Y₂) Z = opTensorQ X Y₁ Z + opTensorQ X Y₂ Z :=
  opTensor3_add_mid X Y₁ Y₂ Z

/-- `0 ⊗ₜ Y ⊗ₜ Z = 0` at the registered factors. -/
theorem opTensorQ_zero_left (Y : Module.End ℝ (Fin 4 → ℂ))
    (Z : Module.End ℝ Minkowski) :
    opTensorQ (0 : Module.End ℝ (Fin 7 → ℂ)) Y Z = 0 :=
  opTensor3_zero_left Y Z

/-- `X ⊗ₜ 0 ⊗ₜ Z = 0` at the registered factors. -/
theorem opTensorQ_zero_mid (X : Module.End ℝ (Fin 7 → ℂ))
    (Z : Module.End ℝ Minkowski) :
    opTensorQ X (0 : Module.End ℝ (Fin 4 → ℂ)) Z = 0 :=
  opTensor3_zero_mid X Z

/-- The triple tensor on pure tensors, at the registered factors. -/
theorem opTensorQ_tmul (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    opTensorQ X Y Z ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = (X x ⊗ₜ[ℝ] Y y) ⊗ₜ[ℝ] Z z :=
  opTensor3_tmul X Y Z x y z

/-- **The Q⁷C⁴R⁴ product Dirac-type operator** (Jeff's filed shape,
signs explicit), parameterized over the factor packages:
`D = D₇ ⊗ 1 ⊗ 1 + γ₇ ⊗ D₄ ⊗ 1 + γ₇ ⊗ γ₄ ⊗ D_R` on the registered
composite. No factor operator is chosen. -/
noncomputable def diracQ7C4R4 (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) : Module.End ℝ q7c4r4Composite :=
  opTensorQ F₇.D 1 1 + opTensorQ F₇.γ F₄.D 1
    + opTensorQ F₇.γ F₄.γ F_R.D

/-- The product Dirac on pure tensors. -/
theorem diracQ7C4R4_tmul (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    diracQ7C4R4 F₇ F₄ F_R ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = ((F₇.D x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
        + ((F₇.γ x ⊗ₜ[ℝ] F₄.D y) ⊗ₜ[ℝ] z)
        + ((F₇.γ x ⊗ₜ[ℝ] F₄.γ y) ⊗ₜ[ℝ] F_R.D z) := by
  unfold diracQ7C4R4
  rw [LinearMap.add_apply, LinearMap.add_apply, opTensorQ_tmul,
    opTensorQ_tmul, opTensorQ_tmul]
  simp [Module.End.one_apply]

/-! ## §4. Headline 1 — the D² identity

The package laws of Q7CR-1a / §1 are carried in composition form
(`∘ₗ`); the D² computation runs in the multiplication of
`Module.End`. The conversions are one-line rewrites by
`LinearMap.mul_eq_comp`. -/

/-- A complex factor package's grading squares to `1`, in
multiplication form (multiplication on `Module.End` is composition,
by definition). -/
theorem FactorOp.gamma_mul_self {n : ℕ} (F : FactorOp n) :
    F.γ * F.γ = 1 :=
  F.γ_invol

/-- A complex factor package's anticommutation, in multiplication
form (operator-first order). -/
theorem FactorOp.anticomm_mul {n : ℕ} (F : FactorOp n) :
    F.D * F.γ + F.γ * F.D = 0 := by
  rw [add_comm]
  exact F.anticomm

/-- The R package's grading squares to `1`, in multiplication
form. -/
theorem FactorOpR.gamma_mul_self (F : FactorOpR) :
    F.γ * F.γ = 1 :=
  F.γ_invol

/-- **HEADLINE 1 — the D² identity.** The square of the assembled
product Dirac is the Kronecker sum of the factor squares:
`D² = D₇² ⊗ 1 ⊗ 1 + 1 ⊗ D₄² ⊗ 1 + 1 ⊗ 1 ⊗ D_R²`, for arbitrary
factor packages. The mixed products cancel in pairs by the factor
anticommutation laws; the diagonal products collapse by the
grading involutions `γ₇² = γ₄² = 1`. -/
theorem diracQ7C4R4_sq (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) :
    (diracQ7C4R4 F₇ F₄ F_R) ^ 2
      = opTensorQ (F₇.D ^ 2) 1 1 + opTensorQ 1 (F₄.D ^ 2) 1
        + opTensorQ 1 1 (F_R.D ^ 2) := by
  have hAA : opTensorQ F₇.D 1 1 * opTensorQ F₇.D 1 1
      = opTensorQ (F₇.D ^ 2) 1 1 := by
    rw [← opTensorQ_mul]
    simp [pow_two]
  have hBB : opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.γ F₄.D 1
      = opTensorQ 1 (F₄.D ^ 2) 1 := by
    rw [← opTensorQ_mul, F₇.gamma_mul_self]
    simp [pow_two]
  have hCC : opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.γ F₄.γ F_R.D
      = opTensorQ 1 1 (F_R.D ^ 2) := by
    rw [← opTensorQ_mul, F₇.gamma_mul_self, F₄.gamma_mul_self]
    simp [pow_two]
  have hAB : opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.D 1
      = opTensorQ (F₇.D * F₇.γ) F₄.D 1 := by
    rw [← opTensorQ_mul]
    simp
  have hBA : opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.D 1 1
      = opTensorQ (F₇.γ * F₇.D) F₄.D 1 := by
    rw [← opTensorQ_mul]
    simp
  have hAC : opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.γ F_R.D
      = opTensorQ (F₇.D * F₇.γ) F₄.γ F_R.D := by
    rw [← opTensorQ_mul]
    simp
  have hCA : opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.D 1 1
      = opTensorQ (F₇.γ * F₇.D) F₄.γ F_R.D := by
    rw [← opTensorQ_mul]
    simp
  have hBC : opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.γ F₄.γ F_R.D
      = opTensorQ 1 (F₄.D * F₄.γ) F_R.D := by
    rw [← opTensorQ_mul, F₇.gamma_mul_self]
    simp
  have hCB : opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.γ F₄.D 1
      = opTensorQ 1 (F₄.γ * F₄.D) F_R.D := by
    rw [← opTensorQ_mul, F₇.gamma_mul_self]
    simp
  have hcross₇ : opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.D 1
      + opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.D 1 1 = 0 := by
    rw [hAB, hBA, ← opTensorQ_add_left, F₇.anticomm_mul,
      opTensorQ_zero_left]
  have hcross₇' : opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.γ F_R.D
      + opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.D 1 1 = 0 := by
    rw [hAC, hCA, ← opTensorQ_add_left, F₇.anticomm_mul,
      opTensorQ_zero_left]
  have hcross₄ : opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.γ F₄.γ F_R.D
      + opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.γ F₄.D 1 = 0 := by
    rw [hBC, hCB, ← opTensorQ_add_mid, F₄.anticomm_mul,
      opTensorQ_zero_mid]
  calc (diracQ7C4R4 F₇ F₄ F_R) ^ 2
      = (opTensorQ F₇.D 1 1 + opTensorQ F₇.γ F₄.D 1
          + opTensorQ F₇.γ F₄.γ F_R.D)
        * (opTensorQ F₇.D 1 1 + opTensorQ F₇.γ F₄.D 1
          + opTensorQ F₇.γ F₄.γ F_R.D) := by
        rw [pow_two]; rfl
    _ = opTensorQ F₇.D 1 1 * opTensorQ F₇.D 1 1
          + opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.γ F₄.D 1
          + opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.γ F₄.γ F_R.D
          + (opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.D 1
            + opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.D 1 1)
          + (opTensorQ F₇.D 1 1 * opTensorQ F₇.γ F₄.γ F_R.D
            + opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.D 1 1)
          + (opTensorQ F₇.γ F₄.D 1 * opTensorQ F₇.γ F₄.γ F_R.D
            + opTensorQ F₇.γ F₄.γ F_R.D * opTensorQ F₇.γ F₄.D 1) := by
        noncomm_ring
    _ = opTensorQ (F₇.D ^ 2) 1 1 + opTensorQ 1 (F₄.D ^ 2) 1
          + opTensorQ 1 1 (F_R.D ^ 2) := by
        rw [hAA, hBB, hCC, hcross₇, hcross₇', hcross₄]
        simp

/-! ## §5. Headline 2 — self-adjointness for the registered
composite pairing (lifted form)

The composite pairing is built as a genuine bilinear form on the
whole tensor space: each factor pairing is packaged as a bilinear
form, and the product form is assembled by the corpus's own
lift-and-map pattern (`ThetLogos.ProductTriple`'s `sesqProd`):
tensor the curried factor forms, then apply the lifted evaluation
pairing. Its value on pure tensors is the product of the three
registered factor pairings. -/

/-- The registered real pairing is homogeneous in its first
argument (real scalars). -/
theorem factorPair_smul_left (n : ℕ) (r : ℝ) (x y : Fin n → ℂ) :
    factorPair n (r • x) y = r • factorPair n x y := by
  have h : cplxPair n (r • x) y = (r : ℂ) * cplxPair n x y := by
    unfold cplxPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    show (r • x) k * star (y k) = (r : ℂ) * (x k * star (y k))
    rw [Pi.smul_apply, Complex.real_smul]
    ring
  show (cplxPair n (r • x) y).re = r • (cplxPair n x y).re
  rw [h, smul_eq_mul]
  simp [Complex.mul_re]

/-- **The factor pairing as a bilinear form**: Q7CR-0's registered
real pairing on the factor `Fin n → ℂ`, packaged as a genuine
ℝ-bilinear form (additivity in the second argument and homogeneity
in the second argument are the symmetry transports of the first
argument's laws, via `factorPair_symm`). -/
noncomputable def factorBilin (n : ℕ) :
    LinearMap.BilinForm ℝ (Fin n → ℂ) :=
  LinearMap.mk₂ ℝ (factorPair n)
    (factorPair_add_left n)
    (factorPair_smul_left n)
    (fun x y y' => by
      rw [factorPair_symm n x (y + y'), factorPair_add_left n y y' x,
        factorPair_symm n y x, factorPair_symm n y' x])
    (fun r x y => by
      rw [factorPair_symm n x (r • y), factorPair_smul_left n r y x,
        factorPair_symm n y x])

/-- The factor bilinear form evaluates as the registered pairing. -/
theorem factorBilin_apply (n : ℕ) (x y : Fin n → ℂ) :
    factorBilin n x y = factorPair n x y :=
  rfl

/-- **The Minkowski pairing as a bilinear form**: Q7CR-0's
registered R⁴ pairing `minkowskiInner`, packaged as a genuine
ℝ-bilinear form. -/
noncomputable def minkBilin : LinearMap.BilinForm ℝ Minkowski :=
  LinearMap.mk₂ ℝ minkowskiInner
    (fun x x' y => by
      unfold minkowskiInner
      simp only [Pi.add_apply]
      ring)
    (fun r x y => by
      unfold minkowskiInner
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (fun x y y' => by
      unfold minkowskiInner
      simp only [Pi.add_apply]
      ring)
    (fun r x y => by
      unfold minkowskiInner
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)

/-- The Minkowski bilinear form evaluates as `minkowskiInner`. -/
theorem minkBilin_apply (x y : Minkowski) :
    minkBilin x y = minkowskiInner x y :=
  rfl

/-- The evaluation pairing of dual vectors, as a bilinear map into
linear functionals on the tensor product (the ℝ-form of
`ProductTriple.sesqProdBil`). -/
noncomputable def pairEvalBil {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] :
    (A →ₗ[ℝ] ℝ) →ₗ[ℝ] (B →ₗ[ℝ] ℝ) →ₗ[ℝ] ((A ⊗[ℝ] B) →ₗ[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ
    (fun f g => (TensorProduct.lid ℝ ℝ).comp (TensorProduct.map f g))
    (fun f₁ f₂ g => by rw [TensorProduct.map_add_left, LinearMap.comp_add])
    (fun c f g => by rw [TensorProduct.map_smul_left, LinearMap.comp_smul])
    (fun f g₁ g₂ => by rw [TensorProduct.map_add_right, LinearMap.comp_add])
    (fun c f g => by rw [TensorProduct.map_smul_right, LinearMap.comp_smul])

/-- **The product of two bilinear forms**: the factorwise product
pairing on a tensor product, as a genuine bilinear form on the
whole tensor space (lifted form). -/
noncomputable def bilinTensor {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (p : LinearMap.BilinForm ℝ A) (q : LinearMap.BilinForm ℝ B) :
    LinearMap.BilinForm ℝ (A ⊗[ℝ] B) :=
  (TensorProduct.lift pairEvalBil).comp (TensorProduct.map p q)

/-- The product pairing on pure tensors is the product of the
factor pairings. -/
theorem bilinTensor_tmul {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (p : LinearMap.BilinForm ℝ A) (q : LinearMap.BilinForm ℝ B)
    (a a' : A) (b b' : B) :
    bilinTensor p q (a ⊗ₜ[ℝ] b) (a' ⊗ₜ[ℝ] b') = p a a' * q b b' := by
  show ((TensorProduct.lift pairEvalBil).comp
      (TensorProduct.map p q)) (a ⊗ₜ[ℝ] b) (a' ⊗ₜ[ℝ] b') = _
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul]
  show ((TensorProduct.lid ℝ ℝ).comp
    (TensorProduct.map (p a) (q b))) (a' ⊗ₜ[ℝ] b') = _
  rw [LinearMap.comp_apply, TensorProduct.map_tmul]
  show (TensorProduct.lid ℝ ℝ) ((p a a') ⊗ₜ[ℝ] (q b b')) = _
  rw [TensorProduct.lid_tmul, smul_eq_mul]

/-- **The registered composite pairing, lifted**: the factorwise
product of Q7CR-0's three registered real pairings — the real part
of the Hermitian form on Q⁷, the same on C⁴, and the η-pairing on
R⁴ — as a genuine bilinear form on the whole composite tensor
space. This is the DQ2 linker form of Q7CR-0 / Q7CR-1a, lifted. -/
noncomputable def compositePair :
    LinearMap.BilinForm ℝ q7c4r4Composite :=
  bilinTensor (bilinTensor (factorBilin 7) (factorBilin 4)) minkBilin

/-- The composite pairing on pure tensors is the product of the
three registered factor pairings. -/
theorem compositePair_tmul (x x' : Fin 7 → ℂ) (y y' : Fin 4 → ℂ)
    (z z' : Minkowski) :
    compositePair ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z) ((x' ⊗ₜ[ℝ] y') ⊗ₜ[ℝ] z')
      = factorPair 7 x x' * factorPair 4 y y' * minkowskiInner z z' := by
  unfold compositePair
  rw [bilinTensor_tmul, bilinTensor_tmul, factorBilin_apply,
    factorBilin_apply, minkBilin_apply]

/-- **HEADLINE 2 — self-adjointness for the registered composite
pairing (lifted form).** The assembled product Dirac is
self-adjoint, in form sense, with respect to the lifted composite
pairing of Q7CR-0's registered factor pairings, for arbitrary
factor packages and arbitrary composite vectors: each of the three
summands of `D` is a tensor product of form-self-adjoint factor
operators (`D` and `γ` on every factor), and the product pairing
evaluates factorwise. -/
theorem diracQ7C4R4_selfAdjoint (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (s t : q7c4r4Composite) :
    compositePair (diracQ7C4R4 F₇ F₄ F_R s) t
      = compositePair s (diracQ7C4R4 F₇ F₄ F_R t) := by
  induction s using TensorProduct.inductionOn with
  | tmul s₇₄ z =>
    induction s₇₄ using TensorProduct.inductionOn with
    | tmul x y =>
      induction t using TensorProduct.inductionOn with
      | tmul t₇₄ w =>
        induction t₇₄ using TensorProduct.inductionOn with
        | tmul u v =>
          rw [diracQ7C4R4_tmul, diracQ7C4R4_tmul]
          simp only [map_add, LinearMap.add_apply, compositePair_tmul]
          rw [F₇.D_selfadj x u, F₇.γ_selfadj x u, F₄.D_selfadj y v,
            F₄.γ_selfadj y v, F_R.D_selfadj z w]
        | add a b ha hb =>
          simp only [TensorProduct.add_tmul, map_add, ha, hb]
      | add a b ha hb =>
        simp only [map_add, ha, hb]
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

end ThetLogos
