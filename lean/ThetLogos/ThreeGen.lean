import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.Scaffold32
import ThetLogos.FiniteSpectralTriple
import ThetLogos.MartinettiRep
import ThetLogos.InnerFluctuations

/-!
# ThetLogos.ThreeGen — three-generation triplication (T2/T3/T4)

Imposed triplication of the one-generation finite geometry from `ThetLogos.MartinettiRep`
to ℂ⁹⁶ = ℂ³² ⊗ ℂ³.

**Honesty boundary (read first).**
* Triplication is IMPOSED, not derived: nothing selects three generations from thet
  primitives. The representation π₃(a) = π(a) ⊗ I₃ and the Dirac ansatz below are
  conventional choices.
* Flavour structure (CKM/PMNS, mass hierarchies) is INPUT via the Yukawa matrices,
  not output. Order-one does not select them.
* Tier T2 (definitions, this file): `gamma3`, `UJ3`, `smGen3`, `smGenOp3`,
  `smDirac3diag` (flavour-diagonal triplication D₃ = D₁ ⊗ I₃).
* Tier T3 (proven, this file): blockwise action of Γ₃ (`gamma3_mul_apply`,
  `mul_gamma3_apply`); Kronecker bridge (`smDirac3diag_eq_kronecker`,
  `gamma3_eq_kronecker`, `UJ3_eq_kronecker`, `smGen3_eq_kronecker`,
  `smGenOp3_eq_kronecker`); inheritance of self-adjointness, grading-oddness,
  J-compatibility, order-zero, and order-one under flavour-diagonal
  triplication (`smDirac3diag_self_adjoint`, `smDirac3diag_grading_odd`,
  `smDirac3diag_J_compat`, `smGen3_order_zero`, `smDirac3diag_order_one`),
  instantiated for the SM ansatz (`smDirac3diag_smDirac_*`).
* Tier T4 (numerical only, NOT proven here): all axioms including order-one
  for arbitrary 3×3 Yukawa matrices. Verified 2026-09-27 in
  `attack4_corrected/attack4_3gen.py`: 3 random trials, exact zeros for
  grading-oddness, self-adjointness, J-compatibility (symmetric MR), and
  order-one (144+144 pairs); total order-one nullity 402 = 3×46 + 3×88.

Index convention: `I96 := I32 × Fin 3`; the pair `(i, g)` is the 32-index `i`
in generation `g`. This matches the Python 96-index `n = i.val * 3 + g.val`.
-/

open Matrix
open scoped Kronecker

namespace ThetLogos

/-- 96-dim index: 32-dim flavour-colour index × 3 generations. -/
abbrev I96 := I32 × Fin 3

/-- Triplicated grading: Γ₃ = Γ ⊗ I₃ (block-diagonal in generation). -/
def gamma3 : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => gammaF i j * if g = gp then (1 : ℂ) else 0

/-- Triplicated real structure: UJ₃ = UJ ⊗ I₃. -/
def UJ3 : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => UJ i j * if g = gp then (1 : ℂ) else 0

/-- Triplicated SM generators: π₃(a) = π(a) ⊗ I₃. -/
noncomputable def smGen3 (g : Fin 12) : Matrix I96 I96 ℂ :=
  fun (i, a) (j, b) => smGen g i j * if a = b then (1 : ℂ) else 0

/-- Triplicated opposite generators: π₃°(b) = π°(b) ⊗ I₃. -/
noncomputable def smGenOp3 (g : Fin 12) : Matrix I96 I96 ℂ :=
  fun (i, a) (j, b) => smGenOp g i j * if a = b then (1 : ℂ) else 0

/-- Flavour-diagonal three-generation Dirac: D₃ = D₁ ⊗ I₃.
    Takes the one-generation Dirac operator D₁ and triplicates it diagonally
    in generation space. The T3-proven case; arbitrary 3×3 Yukawa matrices
    are T4 (numerical) only. -/
def smDirac3diag (D1 : Matrix I32 I32 ℂ) : Matrix I96 I96 ℂ :=
  fun (i, g) (j, gp) => D1 i j * if g = gp then (1 : ℂ) else 0

/-! ## Blockwise action of the triplicated grading (T3) -/

/-- Γ₃ applied to indices. -/
theorem gamma3_apply (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    gamma3 (i, g) (j, gp) = gammaF i j * if g = gp then (1 : ℂ) else 0 := rfl

/-- Γ₃ is the 1-gen grading on the diagonal. -/
theorem gamma3_diag (i : I32) (g : Fin 3) : gamma3 (i, g) (i, g) = gammaF i i := by
  rw [gamma3_apply, if_pos rfl, mul_one]

/-- Γ₃ acts by left multiplication as the 1-gen grading on each block (T3). -/
theorem gamma3_mul_apply (M : Matrix I96 I96 ℂ) (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    (gamma3 * M) (i, g) (j, gp) = gammaF i i * M (i, g) (j, gp) := by
  have hsum : ∑ k : I96, gamma3 (i, g) k * M k (j, gp)
      = gamma3 (i, g) (i, g) * M (i, g) (j, gp) := by
    apply Finset.sum_eq_single (i, g)
    · intro b _ hb
      obtain ⟨k, c⟩ := b
      simp only [gamma3_apply]
      by_cases hcc : g = c
      · have hik : i ≠ k := by
          intro heq; apply hb; simp [heq, hcc]
        simp [ite_eq_left hcc, gammaF_apply_ne hik]
      · simp [ite_eq_right hcc]
    · intro hcon
      exact absurd (Finset.mem_univ (i, g)) hcon
  rw [Matrix.mul_apply, hsum, gamma3_diag]

/-- Γ₃ acts by right multiplication as the 1-gen grading on each block (T3). -/
theorem mul_gamma3_apply (M : Matrix I96 I96 ℂ) (i : I32) (g : Fin 3) (j : I32) (gp : Fin 3) :
    (M * gamma3) (i, g) (j, gp) = M (i, g) (j, gp) * gammaF j j := by
  have hsum : ∑ k : I96, M (i, g) k * gamma3 k (j, gp)
      = M (i, g) (j, gp) * gamma3 (j, gp) (j, gp) := by
    apply Finset.sum_eq_single (j, gp)
    · intro b _ hb
      obtain ⟨k, c⟩ := b
      simp only [gamma3_apply]
      by_cases hcc : c = gp
      · have hkj : k ≠ j := by
          intro heq; apply hb; simp [heq, hcc]
        simp [ite_eq_left hcc, gammaF_apply_ne hkj]
      · simp [ite_eq_right hcc]
    · intro hcon
      exact absurd (Finset.mem_univ (j, gp)) hcon
  rw [Matrix.mul_apply, hsum, gamma3_diag]

end ThetLogos

/-!
## Kronecker bridge and inheritance theorems (T3)

Triplication `D₃ = D₁ ⊗ I₃` is block-diagonal in generation space, which is
exactly the Kronecker product with the 3×3 identity. All five one-generation
properties (self-adjointness, grading-oddness, J-compatibility, order-zero,
order-one) pass through `⊗ₖ` by Mathlib's Kronecker algebra plus two small
local distribution lemmas (`transpose_kronecker_aux`, `sub_kronecker_aux`).
-/

namespace ThetLogos

/-- Triplication of the Dirac operator is the Kronecker product with I₃. -/
theorem smDirac3diag_eq_kronecker (D1 : Matrix I32 I32 ℂ) :
    smDirac3diag D1 = D1 ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  unfold smDirac3diag
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Triplication of the grading is the Kronecker product with I₃. -/
theorem gamma3_eq_kronecker :
    gamma3 = gammaF ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  unfold gamma3
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Triplication of the real structure is the Kronecker product with I₃. -/
theorem UJ3_eq_kronecker :
    UJ3 = UJ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  unfold UJ3
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Triplication of the SM generators is the Kronecker product with I₃. -/
theorem smGen3_eq_kronecker (g : Fin 12) :
    smGen3 g = smGen g ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  unfold smGen3
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Triplication of the opposite generators is the Kronecker product with I₃. -/
theorem smGenOp3_eq_kronecker (g : Fin 12) :
    smGenOp3 g = smGenOp g ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  unfold smGenOp3
  rw [Matrix.kronecker_apply, Matrix.one_apply]

/-- Transpose distributes over `⊗ₖ` (not stated in Mathlib). Tier T3 (proved). -/
theorem transpose_kronecker_aux (A : Matrix I32 I32 ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (A ⊗ₖ B).transpose = A.transpose ⊗ₖ B.transpose := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kronecker_apply, Matrix.transpose_apply]

/-- Subtraction distributes over the left `⊗ₖ` leg (not stated in Mathlib).
    Tier T3 (proved). -/
theorem sub_kronecker_aux (A1 A2 : Matrix I32 I32 ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (A1 - A2) ⊗ₖ B = A1 ⊗ₖ B - A2 ⊗ₖ B := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kronecker_apply, Matrix.sub_apply, sub_mul]

/-- Self-adjointness inherits under flavour-diagonal triplication.
    Tier T3 (proved). -/
theorem smDirac3diag_self_adjoint (D1 : Matrix I32 I32 ℂ) (hD : D1.conjTranspose = D1) :
    (smDirac3diag D1).conjTranspose = smDirac3diag D1 := by
  rw [smDirac3diag_eq_kronecker, Matrix.conjTranspose_kronecker, hD,
    Matrix.conjTranspose_one, ← smDirac3diag_eq_kronecker]

/-- Grading-oddness inherits: {Γ₃, D₃} = 0. Tier T3 (proved). -/
theorem smDirac3diag_grading_odd (D1 : Matrix I32 I32 ℂ)
    (hD : gammaF * D1 + D1 * gammaF = 0) :
    gamma3 * smDirac3diag D1 + smDirac3diag D1 * gamma3 = 0 := by
  have h11 : (1 : Matrix (Fin 3) (Fin 3) ℂ) * 1 = 1 := mul_one 1
  rw [gamma3_eq_kronecker, smDirac3diag_eq_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, h11, ← Matrix.add_kronecker, hD, Matrix.zero_kronecker]

/-- J-compatibility inherits: UJ₃ · D₃ᵀ · UJ₃ = D₃. Tier T3 (proved). -/
theorem smDirac3diag_J_compat (D1 : Matrix I32 I32 ℂ)
    (hD : UJ * D1.transpose * UJ = D1) :
    UJ3 * (smDirac3diag D1).transpose * UJ3 = smDirac3diag D1 := by
  have h11 : (1 : Matrix (Fin 3) (Fin 3) ℂ) * 1 * 1 = 1 := by simp
  rw [UJ3_eq_kronecker, smDirac3diag_eq_kronecker, transpose_kronecker_aux,
    Matrix.transpose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    h11, hD, ← smDirac3diag_eq_kronecker]

/-- Order-zero inherits: [π₃(g1), π₃°(g2)] = 0. Tier T3 (proved). -/
theorem smGen3_order_zero (g1 g2 : Fin 12) :
    smGen3 g1 * smGenOp3 g2 - smGenOp3 g2 * smGen3 g1 = 0 := by
  have h11 : (1 : Matrix (Fin 3) (Fin 3) ℂ) * 1 = 1 := mul_one 1
  rw [smGen3_eq_kronecker, smGenOp3_eq_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, h11, ← sub_kronecker_aux, smGen_order_zero,
    Matrix.zero_kronecker]

/-- Order-one inherits under triplication from any one-generation order-one Dirac.
    Tier T3 (proved). -/
theorem smDirac3diag_order_one (D1 : Matrix I32 I32 ℂ)
    (hD : ∀ g1 g2 : Fin 12,
      (D1 * smGen g1 - smGen g1 * D1) * smGenOp g2
        - smGenOp g2 * (D1 * smGen g1 - smGen g1 * D1) = 0) :
    ∀ g1 g2 : Fin 12,
      (smDirac3diag D1 * smGen3 g1 - smGen3 g1 * smDirac3diag D1) * smGenOp3 g2
        - smGenOp3 g2 * (smDirac3diag D1 * smGen3 g1 - smGen3 g1 * smDirac3diag D1)
        = 0 := by
  intro g1 g2
  have h11 : (1 : Matrix (Fin 3) (Fin 3) ℂ) * 1 = 1 := mul_one 1
  rw [smDirac3diag_eq_kronecker, smGen3_eq_kronecker, smGenOp3_eq_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h11, ← sub_kronecker_aux,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h11, ← sub_kronecker_aux,
    hD g1 g2, Matrix.zero_kronecker]

/-! ## Instantiation for the one-generation SM ansatz (T3) -/

/-- The flavour-diagonal SM three-generation Dirac is self-adjoint.
    Tier T3 (proved), from `smDirac_self_adjoint`. -/
theorem smDirac3diag_smDirac_self_adjoint (yNu yE yU yD yR : ℂ) :
    (smDirac3diag (smDirac yNu yE yU yD yR)).conjTranspose
      = smDirac3diag (smDirac yNu yE yU yD yR) :=
  smDirac3diag_self_adjoint _ (smDirac_self_adjoint yNu yE yU yD yR)

/-- The flavour-diagonal SM three-generation Dirac is grading-odd: {Γ₃, D₃} = 0.
    Tier T3 (proved), from `smDirac_grading_odd`. -/
theorem smDirac3diag_smDirac_grading_odd (yNu yE yU yD yR : ℂ) :
    gamma3 * smDirac3diag (smDirac yNu yE yU yD yR)
      + smDirac3diag (smDirac yNu yE yU yD yR) * gamma3 = 0 :=
  smDirac3diag_grading_odd _ (smDirac_grading_odd yNu yE yU yD yR)

/-- The flavour-diagonal SM three-generation Dirac is J-compatible:
    UJ₃ · D₃ᵀ · UJ₃ = D₃. Tier T3 (proved), from `smDirac_IsJCompatible`. -/
theorem smDirac3diag_smDirac_J_compat (yNu yE yU yD yR : ℂ) :
    UJ3 * (smDirac3diag (smDirac yNu yE yU yD yR)).transpose * UJ3
      = smDirac3diag (smDirac yNu yE yU yD yR) := by
  have hJ := smDirac_IsJCompatible yNu yE yU yD yR
  unfold IsJCompatible at hJ
  exact smDirac3diag_J_compat _ hJ

/-- The flavour-diagonal SM three-generation Dirac satisfies order-one:
    all 144 double commutators `[[D₃, π₃(g1)], π₃°(g2)]` vanish.
    Tier T3 (proved), from `smDirac_order_one`. -/
theorem smDirac3diag_smDirac_order_one (yNu yE yU yD yR : ℂ) :
    ∀ g1 g2 : Fin 12,
      (smDirac3diag (smDirac yNu yE yU yD yR) * smGen3 g1
        - smGen3 g1 * smDirac3diag (smDirac yNu yE yU yD yR)) * smGenOp3 g2
        - smGenOp3 g2 * (smDirac3diag (smDirac yNu yE yU yD yR) * smGen3 g1
          - smGen3 g1 * smDirac3diag (smDirac yNu yE yU yD yR)) = 0 :=
  smDirac3diag_order_one _ (fun g1 g2 => smDirac_order_one yNu yE yU yD yR g1 g2)

end ThetLogos
