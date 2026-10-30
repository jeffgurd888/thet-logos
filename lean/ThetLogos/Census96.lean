import ThetLogos.ThreeGen
import ThetLogos.OrderOne
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# ThetLogos.Census96 — the Census-96 INTERFACE pin (T2, definitions only)

This module is the frozen interface for the Census-96 line (scoping memo
`scoping-census96-2026-10-30.md` §§1.B–1.D, §3 row C96-0, §4 kills; pack
`pack-c96-0.md`). It contains DEFINITIONS AND STATEMENT PINS ONLY: no
census number is proved here, and no proof is attempted. Later bricks
(C96-1 decoupling, C96-2 the 46 theorem, C96-3 the 88 theorem, C96-4
assembly) build against exactly these names.

## Parameterization source (extracted, Python governs)

The admissible parameterization was extracted from the Python census
source `attack4_corrected/attack4_3gen.py` (commit `90a80e7`; the file
was later purged from the working tree by `457d150` and was read from
git history — it is NOT reconstructed from prose), together with its
one-generation base `attack4_corrected/attack4_corrected.py`.

What the Python actually imposes:

* One generation (`attack4_corrected.py`, `step2`): the admissible
  space is the real span of HERMITIAN 32×32 matrices subject to exactly
  two further constraints — grading-oddness `{H, gammaF} = 0` and
  J-compatibility `UJ * conj(H) = H * UJ`. Real dimension 272. The
  `build_dirac(A, B, C, E)` block ansatz is used in the Python ONLY to
  generate the SM directions; it is NOT a constraint on the admissible
  space. This pin follows the Python: `IsAdm32` below has the three
  conditions (self-adjoint, γ_F-odd, J-compatible) and no block ansatz.
* Three generations (`attack4_3gen.py`, Step 2): `D₃` ranges over all
  96×96 matrices whose nine generation blocks `D_{gg'}` (each a 32×32
  block over `I96 = I32 × Fin 3`) satisfy: `D₃` self-adjoint (so
  `D_{g'g} = D_{gg'}†` and each diagonal block is hermitian),
  `γ₃`-oddness (`γ₃ = γ_F ⊗ I₃`, so each block is `γ_F`-odd), and
  `J₃`-compatibility (`UJ₃ = UJ ⊗ I₃`; in the Python's entrywise-conj
  form `UJ₃ * conj(D₃) = D₃ * UJ₃`, which couples each block to itself:
  every block is individually J-compatible in that form). Diagonal
  blocks: the 272-dimensional one-generation space. Off-diagonal
  blocks: a 512-real-dimensional space of complex `γ_F`-odd
  J-compatible blocks, decomposed in the Python as 272 (hermitian
  J-compatible) + 240 (`Complex.I` times hermitian J-ANTI-compatible
  `γ_F`-odd blocks). Equivalently, at the level of the SM ansatz: four
  arbitrary complex 3×3 Yukawa matrices and a complex SYMMETRIC 3×3
  Majorana matrix (the Python checks: self-adjointness needs no
  symmetry of `MR`; J-compatibility does — non-symmetric `MR` breaks
  `UJ₃ * conj(D₃) = D₃ * UJ₃` while leaving `D₃† = D₃`).
* Admissible dimension at 96 (Python, T4): `2352 = 3 * 272 + 3 * 512`.

Presentation note (not a divergence): the Python writes
J-compatibility with entrywise conjugation, the corpus's owned Lean
form (`IsJCompatible`, `smDirac3diag_J_compat`) writes it with the
transpose, `UJ * Dᵀ * UJ = D`. Under self-adjointness the two forms
coincide (`conj(D) = Dᵀ` when `D† = D`, and `UJ² = 1`), globally and
blockwise; this pin uses the owned Lean transpose form for `Adm96`
and records the Python conj form in `IsAdmBlock` for the blocks.

## The pinned statements (all UNPROVED here)

* `Census96`: `finrank ℝ {D ∈ Adm96 | OrderOneHolds₃ D} = 402`, with
  the decomposition on its face: **402 = 3·46 + 3·88**, and
  **402 ≠ 9·46 = 414** (the mixing pair contributes 88, not 92 — the
  self-adjoint/J pairing constrains the pair below two independent
  blocks). No later text may drift to 414.
* `Census96Diag`: the flavour-diagonal nullity is 46 — pinned
  SEPARATELY (see its docstring). It is a corollary-shaped statement
  of the one-generation 46 over the `smDirac3diag` image; it is NOT
  evidence for the 402, and reporting it as the census is a K-C96-2
  event.
* `Adm96Dim`: `finrank ℝ Adm96 = 2352` — the pin's self-check,
  registered as a statement; its proof is the interface's first
  discharge (a later brick). **If the pinned space's dimension is
  not 2352, the pin is wrong before any census question is asked.**

## Fences (binding on the whole line)

* Generations are IMPOSED; CKM/PMNS are input-only. The census counts
  slots/directions and derives NO flavour quantity. Dial 1 unmoved.
* Posted question Q3 (generations) stays OPEN under any outcome.
* The old 46→10 classification (`cf_kernel_classification_46_10`) is
  UNSOUND AS STATED and is NOT revived here; the standing corrected
  cut is 46→22 (`CFKernel22`).
* NO CLAIM. The target number 402 is a T4 note's content being pinned
  for proof or kill (K-C96-1 armed over the whole line). The pins in
  this module are T2.
-/

open Matrix

namespace ThetLogos

/-! ## §1. The extracted admissible predicates -/

/-- One-generation admissibility, exactly as parameterized by
    `attack4_corrected.py` (`step2`): self-adjoint, `γ_F`-odd, and
    J-compatible (owned Lean form `IsJCompatible`). No `buildDirac`
    block ansatz is imposed — in the Python that ansatz generates the
    SM directions only. Tier T2. -/
def IsAdm32 (D : Matrix I32 I32 ℂ) : Prop :=
  D.conjTranspose = D ∧
  gammaF * D + D * gammaF = 0 ∧
  IsJCompatible D

/-- Entrywise conjugation of a 32×32 complex matrix (the Python
    census's `conj(M)`, without transpose). Tier T2. -/
def entrywiseConj (M : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  fun i j => star (M i j)

/-- Block admissibility for a single generation block, in the Python
    census's own form (`attack4_3gen.py`, Step 2): `γ_F`-odd and
    J-compatible in the entrywise-conj form `UJ * conj(M) = M * UJ`.
    Every one of the nine blocks of an admissible `D₃` satisfies this;
    a diagonal block additionally satisfies `IsAdm32` (hermitian),
    and an off-diagonal block's partner is its conjugate-transpose
    (self-adjointness of the whole). Tier T2. -/
def IsAdmBlock (M : Matrix I32 I32 ℂ) : Prop :=
  gammaF * M + M * gammaF = 0 ∧
  UJ * entrywiseConj M = M * UJ

/-- Three-generation admissibility: `D ∈ M₉₆(ℂ)` self-adjoint,
    `γ₃`-odd, and `J₃`-compatible in the owned Lean transpose form
    (the form of `smDirac3diag_J_compat`). Under self-adjointness
    this is the Python's `UJ₃ * conj(D₃) = D₃ * UJ₃`. Tier T2. -/
def IsAdm96 (D : Matrix I96 I96 ℂ) : Prop :=
  D.conjTranspose = D ∧
  gamma3 * D + D * gamma3 = 0 ∧
  UJ3 * D.transpose * UJ3 = D

/-! ## §2. Generation-block projections -/

/-- The `(g, g')` generation block of `D : M₉₆(ℂ)`: the 32×32 matrix
    `fun i j => D (i, g) (j, g')` over `I96 = I32 × Fin 3`. These are
    the nine `buildDirac`-sized blocks of the Python parameterization
    (there, `D₃ = ∑_{g,g'} D^{(g,g')} ⊗ E³_{gg'}`). Tier T2. -/
def genBlock (D : Matrix I96 I96 ℂ) (g gp : Fin 3) : Matrix I32 I32 ℂ :=
  fun i j => D (i, g) (j, gp)

end ThetLogos

namespace ThetLogos

/-! ## §3. `Adm96` as a real submodule -/

/-- Real scalars commute with `star` on `ℂ` (interface closure fact,
    needed for the real submodule structures below). -/
theorem census96_star_real_smul (c : ℝ) (z : ℂ) : star (c • z) = c • star z := by
  have h : ∀ w : ℂ, (c : ℝ) • w = (c : ℂ) * w := fun w => by simp
  rw [h, h, star_mul]
  simp
  ring

/-- **The admissible space `𝒜₃`** (Python: real dimension 2352, T4):
    the ℝ-submodule of `M₉₆(ℂ)` cut out by `IsAdm96` — self-adjoint,
    `γ₃`-odd, `J₃`-compatible. The three conditions are ℝ-linear
    (conjugation is ℝ-linear on `ℂ`), so this is a real submodule over
    the realification, as the census's real `finrank` requires.
    Tier T2. -/
def Adm96 : Submodule ℝ (Matrix I96 I96 ℂ) where
  carrier := {D | IsAdm96 D}
  add_mem' := by
    intro D1 D2 h1 h2
    obtain ⟨s1, g1, j1⟩ := h1
    obtain ⟨s2, g2, j2⟩ := h2
    refine ⟨?_, ?_, ?_⟩
    · show (D1 + D2).conjTranspose = D1 + D2
      rw [Matrix.conjTranspose_add, s1, s2]
    · show gamma3 * (D1 + D2) + (D1 + D2) * gamma3 = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gamma3 * D1 + gamma3 * D2) + (D1 * gamma3 + D2 * gamma3)
          = (gamma3 * D1 + D1 * gamma3) + (gamma3 * D2 + D2 * gamma3) := by
        ac_rfl
      rw [h3, g1, g2, add_zero]
    · show UJ3 * (D1 + D2).transpose * UJ3 = D1 + D2
      rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, j1, j2]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Matrix I96 I96 ℂ).conjTranspose = 0
      simp
    · show gamma3 * (0 : Matrix I96 I96 ℂ) + (0 : Matrix I96 I96 ℂ) * gamma3 = 0
      simp
    · show UJ3 * (0 : Matrix I96 I96 ℂ).transpose * UJ3 = 0
      simp
  smul_mem' := by
    intro c D hD
    obtain ⟨s, g, j⟩ := hD
    refine ⟨?_, ?_, ?_⟩
    · have hS : (c • D).conjTranspose = c • D.conjTranspose := by
        ext i j
        have e1 : ((c • D) j i) = c • (D j i) := rfl
        have e2 : ((c • D.conjTranspose) i j) = c • (D.conjTranspose i j) := rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • D).conjTranspose = c • D
      rw [hS, s]
    · have hG : gamma3 * (c • D) + (c • D) * gamma3
          = c • (gamma3 * D + D * gamma3) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gamma3 * (c • D) + (c • D) * gamma3 = 0
      rw [hG, g, smul_zero]
    · have hJ : UJ3 * (c • D).transpose * UJ3 = c • (UJ3 * D.transpose * UJ3) := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      show UJ3 * (c • D).transpose * UJ3 = c • D
      rw [hJ, j]

/-! ## §4. The order-one predicate at 96 -/

/-- **Order-one at three generations**: all 144 double commutators
    `[[D, π₃(g₁)], π₃°(g₂)]` over the owned triplicated generators
    `smGen3` / `smGenOp3` vanish. The exact analogue of the
    one-generation predicate `OrderOneHolds`, with the same repaired
    12-generator family. Tier T2. -/
def OrderOneHolds₃ (D : Matrix I96 I96 ℂ) : Prop :=
  ∀ g1 g2 : Fin 12,
    (D * smGen3 g1 - smGen3 g1 * D) * smGenOp3 g2
      - smGenOp3 g2 * (D * smGen3 g1 - smGen3 g1 * D) = 0

end ThetLogos

namespace ThetLogos

/-! ## §5. The census solution space and the pinned census statements -/

/-- The order-one solution space inside `Adm96`:
    `{D ∈ Adm96 | OrderOneHolds₃ D}` as a real submodule of `M₉₆(ℂ)`.
    Order-one is ℝ-linear in `D`, so the restriction is a submodule.
    Tier T2. -/
def Census96Sol : Submodule ℝ (Matrix I96 I96 ℂ) where
  carrier := {D | IsAdm96 D ∧ OrderOneHolds₃ D}
  add_mem' := by
    intro D1 D2 h1 h2
    refine ⟨Adm96.add_mem h1.1 h2.1, ?_⟩
    intro a b
    have e1 := h1.2 a b
    have e2 := h2.2 a b
    have hX : (D1 + D2) * smGen3 a - smGen3 a * (D1 + D2)
        = (D1 * smGen3 a - smGen3 a * D1) + (D2 * smGen3 a - smGen3 a * D2) := by
      simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, neg_add]
      ac_rfl
    rw [hX, Matrix.add_mul, Matrix.mul_add]
    have h3 : ((D1 * smGen3 a - smGen3 a * D1) * smGenOp3 b
        + (D2 * smGen3 a - smGen3 a * D2) * smGenOp3 b)
        - (smGenOp3 b * (D1 * smGen3 a - smGen3 a * D1)
        + smGenOp3 b * (D2 * smGen3 a - smGen3 a * D2))
        = ((D1 * smGen3 a - smGen3 a * D1) * smGenOp3 b
        - smGenOp3 b * (D1 * smGen3 a - smGen3 a * D1))
        + ((D2 * smGen3 a - smGen3 a * D2) * smGenOp3 b
        - smGenOp3 b * (D2 * smGen3 a - smGen3 a * D2)) := by
      simp only [sub_eq_add_neg, neg_add]
      ac_rfl
    rw [h3, e1, e2, add_zero]
  zero_mem' := ⟨Adm96.zero_mem, by intro a b; simp⟩
  smul_mem' := by
    intro c D hD
    refine ⟨Adm96.smul_mem c hD.1, ?_⟩
    intro a b
    have e := hD.2 a b
    have hX : (c • D) * smGen3 a - smGen3 a * (c • D)
        = c • (D * smGen3 a - smGen3 a * D) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
    show ((c • D) * smGen3 a - smGen3 a * (c • D)) * smGenOp3 b
      - smGenOp3 b * ((c • D) * smGen3 a - smGen3 a * (c • D)) = 0
    rw [hX, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, e, smul_zero]

/-- **CENSUS-96 (pinned statement, UNPROVED).** The real dimension of
    the order-one solution space in `𝒜₃` is 402:
    `finrank ℝ {D ∈ Adm96 | OrderOneHolds₃ D} = 402`, with the
    decomposition **402 = 3·46 + 3·88** (three diagonal blocks at the
    one-generation 46, three mixing pairs at 88) and
    **402 ≠ 9·46 = 414**. The number is the T4 Python census's content
    (`attack4_3gen.py`: per-diagonal nullity 46, per-mixing-pair
    nullity 88), pinned here for proof or kill — K-C96-1 is armed.
    Tier T2 (the pin); the number itself is T4 until discharged. -/
def Census96 : Prop :=
  Module.finrank ℝ Census96Sol = 402

/-- **Self-check (pinned statement, UNPROVED).** The admissible space
    itself has real dimension `2352 = 3·272 + 3·512`. Registered as
    part of the pin; its proof is the interface's first discharge.
    If the pinned space's dimension is not 2352, the pin is wrong
    before any census question is asked. Tier T2 (the pin); the
    number is T4 (Python, `attack4_3gen.py` Step 2). -/
def Adm96Dim : Prop :=
  Module.finrank ℝ Adm96 = 2352

end ThetLogos

namespace ThetLogos

/-! ## §6. The flavour-diagonal pin (separate; NOT the census) -/

/-- The one-generation census solution space:
    `{D ∈ M₃₂(ℂ) | IsAdm32 D ∧ OrderOneHolds D}` as a real submodule.
    Its `finrank` is the one-generation 46 (T4 today; the theorem is
    owed by C96-2). Tier T2. -/
def Sol32 : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {D | IsAdm32 D ∧ OrderOneHolds D}
  add_mem' := by
    intro D1 D2 h1 h2
    obtain ⟨⟨s1, g1, j1⟩, o1⟩ := h1
    obtain ⟨⟨s2, g2, j2⟩, o2⟩ := h2
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show (D1 + D2).conjTranspose = D1 + D2
      rw [Matrix.conjTranspose_add, s1, s2]
    · show gammaF * (D1 + D2) + (D1 + D2) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * D1 + gammaF * D2) + (D1 * gammaF + D2 * gammaF)
          = (gammaF * D1 + D1 * gammaF) + (gammaF * D2 + D2 * gammaF) := by
        ac_rfl
      rw [h3, g1, g2, add_zero]
    · show UJ * (D1 + D2).transpose * UJ = D1 + D2
      rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, j1, j2]
    · intro a b
      have e1 := o1 a b
      have e2 := o2 a b
      have hX : (D1 + D2) * smGen a - smGen a * (D1 + D2)
          = (D1 * smGen a - smGen a * D1) + (D2 * smGen a - smGen a * D2) := by
        simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, neg_add]
        ac_rfl
      rw [hX, Matrix.add_mul, Matrix.mul_add]
      have h3 : ((D1 * smGen a - smGen a * D1) * smGenOp b
          + (D2 * smGen a - smGen a * D2) * smGenOp b)
          - (smGenOp b * (D1 * smGen a - smGen a * D1)
          + smGenOp b * (D2 * smGen a - smGen a * D2))
          = ((D1 * smGen a - smGen a * D1) * smGenOp b
          - smGenOp b * (D1 * smGen a - smGen a * D1))
          + ((D2 * smGen a - smGen a * D2) * smGenOp b
          - smGenOp b * (D2 * smGen a - smGen a * D2)) := by
        simp only [sub_eq_add_neg, neg_add]
        ac_rfl
      rw [h3, e1, e2, add_zero]
  zero_mem' := by
    refine ⟨⟨?_, ?_, ?_⟩, by intro a b; simp⟩
    · show (0 : Matrix I32 I32 ℂ).conjTranspose = 0
      simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ) * gammaF = 0
      simp
    · show UJ * (0 : Matrix I32 I32 ℂ).transpose * UJ = 0
      simp
  smul_mem' := by
    intro c D hD
    obtain ⟨⟨s, g, j⟩, o⟩ := hD
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · have hS : (c • D).conjTranspose = c • D.conjTranspose := by
        ext i j
        have e1 : ((c • D) j i) = c • (D j i) := rfl
        have e2 : ((c • D.conjTranspose) i j) = c • (D.conjTranspose i j) := rfl
        rw [Matrix.conjTranspose_apply, e1, census96_star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • D).conjTranspose = c • D
      rw [hS, s]
    · have hG : gammaF * (c • D) + (c • D) * gammaF
          = c • (gammaF * D + D * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • D) + (c • D) * gammaF = 0
      rw [hG, g, smul_zero]
    · have hJ : UJ * (c • D).transpose * UJ = c • (UJ * D.transpose * UJ) := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      show UJ * (c • D).transpose * UJ = c • D
      rw [hJ, j]
    · intro a b
      have e := o a b
      have hX : (c • D) * smGen a - smGen a * (c • D)
          = c • (D * smGen a - smGen a * D) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      show ((c • D) * smGen a - smGen a * (c • D)) * smGenOp b
        - smGenOp b * ((c • D) * smGen a - smGen a * (c • D)) = 0
      rw [hX, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, e, smul_zero]

/-- Flavour-diagonal triplication `D₁ ↦ D₁ ⊗ I₃` (owned `smDirac3diag`)
    as a real-linear map. Tier T2. -/
noncomputable def smDirac3diagLM : (Matrix I32 I32 ℂ) →ₗ[ℝ] (Matrix I96 I96 ℂ) where
  toFun := smDirac3diag
  map_add' := by
    intro D1 D2
    ext ⟨i, g⟩ ⟨j, gp⟩
    by_cases h : g = gp <;> simp [smDirac3diag, h]
  map_smul' := by
    intro c D
    ext ⟨i, g⟩ ⟨j, gp⟩
    by_cases h : g = gp <;> simp [smDirac3diag, h, smul_eq_mul]

/-- The flavour-diagonal solution space at 96: the `smDirac3diag`
    image of the one-generation solution space `Sol32`. Tier T2. -/
noncomputable def Diag96Sol : Submodule ℝ (Matrix I96 I96 ℂ) :=
  Submodule.map smDirac3diagLM Sol32

/-- **CENSUS-96-DIAG (pinned statement, UNPROVED — fenced).** The
    flavour-diagonal nullity is 46: the `smDirac3diag` image of the
    one-generation order-one solution space has real dimension 46.
    This is a corollary-shaped statement of the one-generation 46.
    It is NOT the census, NOT evidence for the 402, and reporting it
    as the census is a K-C96-2 event. Tier T2 (the pin); the number
    is T4 until C96-2/C96-4 discharge it. -/
def Census96Diag : Prop :=
  Module.finrank ℝ Diag96Sol = 46

end ThetLogos
