import ThetLogos.RepOrthogonality

/-
# PW-3: the `ρ ⊗ ρ` twirl — the Frobenius–Schur side

Brick PW-3 of the projector scoping
(`scoping-pw3-fs-2026-10-27.md` §1). PW-1 evaluated the mixed pair
`(ρ, ρ̄)`: the `(1, 1)` site integrals. This module evaluates the
same-orientation pairs `(2, 0)` and `(0, 2)`: the entries of
`∫ ρ(g) ⊗ ρ(g) dg` and of its conjugate. The owned object is again
a `haarTwirl`, here at `(repMatrix ρ, repMatrix ρ)`; what is new
is its evaluation, which is the Frobenius–Schur alternative: for
irreducible `ρ` the invariant bilinear forms form a space of
dimension at most one, and the twirl is `(d : ℂ)⁻¹` times the
canonical J-tensor when a nonzero invariant form exists, and zero
when none does. The decision datum is the indicator

  `fsIndicator ρ μG = ∫ g, charFn ρ (g * g) ∂μG ∈ {0, 1, -1}`.

The headline (index placement recorded before proving, per the
PW-2 precedent): with `J = canonicalForm ρ` the normalized
invariant form of §5,

  `∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else (d : ℂ)⁻¹ * (star (J i k) * J j l)`.

The conjugated factor carries the row pair `(i, k)` — the twirl's
row index is the pair of first indices — and the plain factor the
column pair `(j, l)`. (Conjugation is spelled `star` throughout,
as in PW-1; on `ℂ` that is the conjugation operation.)
Trace consistency: `tr 𝒥 = (d:ℂ)⁻¹ * ∑ i k, star (J i k) * J i k
= 1`, matching `haarTwirl_trace` and the rank-one projector. The
indicator is a different trace: `ν = ∑ i k, 𝒥 (i,k) (k,i)`, the
flip trace of §4.

HONESTY LEDGER — read this before citing anything from this file.

**(i) NO CLAIM; dials 0/4.** Parts of the official Clay
Yang–Mills statement closed by this module: **0**. Finite-volume /
compact-group representation algebra only; no limit is taken or
asserted.

**(ii) Scope flag (K-PW-1b, extended verbatim; K-PW-3c).** Every
statement here is for **irreducible** `ρ` only. No vanishing or
J-form statement is made at reducible `ρ`; any consumer must carry
`RepIrreducible ρ` as a hypothesis.

**(iii) Seat checks first (K-PW-3a).** Before the general proof,
the headline and the indicator were checked by exact arithmetic
at the two probed seats (`seat-check-pw3.py`, sympy over ℚ(√3)):
(C₃, faithful χ) has `ν = (1/3)(1 + ζ² + ζ) = 0`, every `(2, 0)`
entry zero, and no nonzero invariant form; (S₃, std) has
`ν = +1`, the `(2, 0)` twirl equal to `(1/2) δ_{i,k} δ_{j,l}` on
all 16 tuples — the headline with canonical form `J = I` (the
seat matrices are real orthogonal) — and the flip trace
`tr (𝒥 ∘ flip) = ν` at both seats. Had a seat disagreed, this
file would instead be a defect report.

**(iv) Method.** The evaluation does not leave owned vocabulary:
pair-invariance under `(ρ, ρ)` is intertwining
`ρ(g) * W = W * ρ̄(g)`; the Hermitian square `star W * W` and the
square `W * star W` both land in a commutant (of `ρ̄`, of `ρ`),
both have the same trace `∑ ‖W i j‖²`, and PW-1's hand-rolled
Schur makes them the same nonzero scalar — so every nonzero
pair-invariant matrix is invertible and the invariant submodule
is a line (the second Schur use). The twirl on a line is then
factored entrywise (columns in the span, self-adjointness, the
twirl fixes the spanning vector), and the flip on the line is
the sign.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix

section Setup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §1. Definitions -/

/-- The **Frobenius–Schur indicator** of the corpus representation:
`∫ g, charFn ρ (g * g) ∂μG`. (Defined with explicit binders, in the
order the scoping memo names it; every piece is owned.) -/
noncomputable def fsIndicator {G : Type*} [Group G] [MeasurableSpace G] {d : ℕ}
    (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (μG : Measure G) : ℂ :=
  ∫ g, charFn ρ (g * g) ∂μG

/-- The **invariant-bilinear-form predicate**: `J` is invariant when
every `repMatrix ρ g` preserves the form, `(repMatrix ρ g)ᵀ * J *
repMatrix ρ g = J`. -/
def InvariantBilinearForm (J : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g, (repMatrix ρ g)ᵀ * J * repMatrix ρ g = J

/-- The vector form of a matrix on the pair index:
`vecOf W (a, b) = W a b`. -/
def vecOf (W : Matrix (Fin d) (Fin d) ℂ) : (Fin d × Fin d) → ℂ :=
  fun p => W p.1 p.2

theorem vecOf_apply (W : Matrix (Fin d) (Fin d) ℂ) (p : Fin d × Fin d) :
    vecOf W p = W p.1 p.2 := rfl

/-- The **J-vector** of a matrix `J`: the pair-index vector
`p ↦ star (J p.1 p.2)` — the entrywise conjugate, read as a vector.
For an invariant form `J` this is the canonical invariant vector
of the pair action `(ρ, ρ)` (§5). -/
def jVec (J : Matrix (Fin d) (Fin d) ℂ) : (Fin d × Fin d) → ℂ :=
  fun p => star (J p.1 p.2)

theorem jVec_apply (J : Matrix (Fin d) (Fin d) ℂ) (p : Fin d × Fin d) :
    jVec J p = star (J p.1 p.2) := rfl

/-- The **flip** on pair-index vectors: `flipVec w (a, b) = w (b, a)`
— transposition, read as a vector map. It preserves the pair
invariant submodule (§4), where it acts as the symmetry sign. -/
def flipVec (w : (Fin d × Fin d) → ℂ) : (Fin d × Fin d) → ℂ :=
  fun p => w (p.2, p.1)

theorem flipVec_apply (w : (Fin d × Fin d) → ℂ) (p : Fin d × Fin d) :
    flipVec w p = w (p.2, p.1) := rfl

theorem flipVec_flipVec (w : (Fin d × Fin d) → ℂ) :
    flipVec (flipVec w) = w := by
  funext ⟨a, b⟩
  rfl

theorem flipVec_smul (c : ℂ) (w : (Fin d × Fin d) → ℂ) :
    flipVec (c • w) = c • flipVec w := by
  funext ⟨a, b⟩
  show (c • w) (b, a) = c * w (b, a)
  rw [Pi.smul_apply, smul_eq_mul]

/-! ## §2. The conjugation dictionary

Transpose and conjugation of `repMatrix`, and the commutant of the
conjugate orientation. The bridge used throughout: on `ℂ`,
entrywise conjugation is spelled `starRingEnd ℂ` inside
`orientConj` and `star` at entries; the two agree. -/

theorem starRingEnd_eq_star (z : ℂ) : (starRingEnd ℂ) z = star z := rfl

/-- Transpose of the representation is the conjugate orientation
at the inverse: `(repMatrix ρ g)ᵀ = orientConj (repMatrix ρ) g⁻¹`. -/
theorem repMatrix_transpose (g : G) :
    (repMatrix ρ g)ᵀ = orientConj (repMatrix ρ) g⁻¹ := by
  ext i j
  show repMatrix ρ g j i = star (repMatrix ρ g⁻¹ i j)
  rw [repMatrix_inv, Matrix.star_apply, star_star]

/-- Transpose of the conjugate orientation is the representation
at the inverse: `(orientConj (repMatrix ρ) g)ᵀ = repMatrix ρ g⁻¹`. -/
theorem orientConj_transpose (g : G) :
    (orientConj (repMatrix ρ) g)ᵀ = repMatrix ρ g⁻¹ := by
  ext i j
  show star (repMatrix ρ g j i) = repMatrix ρ g⁻¹ i j
  rw [repMatrix_inv, Matrix.star_apply]

/-- Entrywise conjugation of a product of matrices is the product
of the entrywise conjugates. -/
theorem map_conj_mul (X Y : Matrix (Fin d) (Fin d) ℂ) :
    (X * Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) * Y.map (starRingEnd ℂ) :=
  Matrix.map_mul

/-- Entrywise conjugation is an involution on matrices. -/
theorem map_conj_map_conj (X : Matrix (Fin d) (Fin d) ℂ) :
    (X.map (starRingEnd ℂ)).map (starRingEnd ℂ) = X := by
  ext i j
  show (starRingEnd ℂ) ((starRingEnd ℂ) (X i j)) = X i j
  rw [starRingEnd_eq_star, starRingEnd_eq_star, star_star]

/-- The conjugate orientation, conjugated back, is the
representation: `(orientConj (repMatrix ρ) g).map (starRingEnd ℂ)
= repMatrix ρ g`. -/
theorem map_conj_orientConj (g : G) :
    (orientConj (repMatrix ρ) g).map (starRingEnd ℂ) = repMatrix ρ g := by
  show ((repMatrix ρ g).map (starRingEnd ℂ)).map (starRingEnd ℂ) = repMatrix ρ g
  exact map_conj_map_conj _

/-- The transpose–conjugate unit identity:
`(repMatrix ρ g)ᵀ * orientConj (repMatrix ρ) g = 1` — the transpose
is the conjugate orientation at the inverse, and the conjugate
orientation is multiplicative. -/
theorem transpose_mul_orientConj (g : G) :
    (repMatrix ρ g)ᵀ * orientConj (repMatrix ρ) g = 1 := by
  rw [repMatrix_transpose, ← orientConj_mul _ (fun a b => repMatrix_mul ρ a b),
    inv_mul_cancel, orientConj_one _ (repMatrix_one ρ)]

/-- The conjugate–transpose unit identity:
`orientConj (repMatrix ρ) g * (repMatrix ρ g)ᵀ = 1`. -/
theorem orientConj_mul_transpose (g : G) :
    orientConj (repMatrix ρ) g * (repMatrix ρ g)ᵀ = 1 := by
  rw [repMatrix_transpose, ← orientConj_mul _ (fun a b => repMatrix_mul ρ a b),
    mul_inv_cancel, orientConj_one _ (repMatrix_one ρ)]

/-- **The commutant of the conjugate orientation is scalar.**
If `A` commutes with every `orientConj (repMatrix ρ) h`, then `A`
is a scalar multiple of the identity: conjugate `A` entrywise and
apply PW-1's commutant theorem for `ρ` itself. -/
theorem commutant_orientConj_eq_smul (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ h : G, orientConj (repMatrix ρ) h * A = A * orientConj (repMatrix ρ) h) :
    ∃ c : ℂ, A = c • 1 := by
  have hB : ∀ h : G, repMatrix ρ h * A.map (starRingEnd ℂ)
      = A.map (starRingEnd ℂ) * repMatrix ρ h := by
    intro h
    have h1 : (orientConj (repMatrix ρ) h * A).map (starRingEnd ℂ)
        = (A * orientConj (repMatrix ρ) h).map (starRingEnd ℂ) := by rw [hA h]
    simp only [map_conj_mul, map_conj_orientConj] at h1
    exact h1
  obtain ⟨c, hc⟩ := commutant_eq_smul_of_repIrreducible ρ hd hρirr
    (A.map (starRingEnd ℂ)) hB
  refine ⟨star c, ?_⟩
  have h2 : A = (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) :=
    (map_conj_map_conj _).symm
  rw [h2, hc]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.map_apply, Matrix.smul_apply]
  · simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, h]

/-! ## §3. Pair-invariance is intertwining; the invariant submodule is a line

The bridge: for a vector `w`, invariance under the pair action
`(ρ, ρ)` is the matrix identity `R * W * Rᵀ = W` for the matrix
`W` it spells out. Since `(Rᵀ)⁻¹ = ρ̄` (the unit identities of
§2), that identity is the intertwining relation
`W * ρ̄(g) = ρ(g) * W`. Two squares land in commutants:
`W * star W` in the commutant of `ρ`, `star W * W` in the
commutant of `ρ̄`; both have trace `∑ ‖W i j‖²`, so by Schur both
are the same nonzero scalar when `W ≠ 0` — every nonzero
pair-invariant matrix is invertible, and the invariant submodule
is the span of any one of them. This is the second Schur use,
mirroring PW-1 §5. -/

/-- The entry identity behind the bridge: the pair action of
`(ρ, ρ)` on a vector agrees entrywise with the matrix product
against the transpose. -/
theorem pairMat_mulVec_repMatrix_self_apply (w : (Fin d × Fin d) → ℂ) (g : G)
    (a b : Fin d) :
    (pairMat (repMatrix ρ g) (repMatrix ρ g) *ᵥ w) (a, b)
      = (repMatrix ρ g * Matrix.of (fun a b => w (a, b)) * (repMatrix ρ g)ᵀ) a b := by
  calc (pairMat (repMatrix ρ g) (repMatrix ρ g) *ᵥ w) (a, b)
      = ∑ c, ∑ e, repMatrix ρ g a c * repMatrix ρ g b e * w (c, e) := by
        rw [pairMat_mulVec_apply, Fintype.sum_prod_type]
    _ = ∑ e, (∑ c, repMatrix ρ g a c * w (c, e)) * repMatrix ρ g b e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = (repMatrix ρ g * Matrix.of (fun a b => w (a, b)) * (repMatrix ρ g)ᵀ) a b := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

/-- **The bridge**: `w` is invariant under the pair action
`(ρ, ρ)` iff its matrix satisfies `R * W * Rᵀ = W` at every `h`. -/
theorem mem_pairInvariantSubmodule_repMatrix_self_iff {w : (Fin d × Fin d) → ℂ} :
    w ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) ↔
      ∀ h : G, repMatrix ρ h * Matrix.of (fun a b => w (a, b)) * (repMatrix ρ h)ᵀ
        = Matrix.of (fun a b => w (a, b)) := by
  rw [mem_pairInvariantSubmodule]
  constructor
  · intro hw h
    ext a b
    have hentry := congrFun (hw h) (a, b)
    rwa [pairMat_mulVec_repMatrix_self_apply] at hentry
  · intro hw h
    funext ⟨a, b⟩
    have hentry := congrFun (congrArg (fun M : Matrix (Fin d) (Fin d) ℂ =>
      fun p : Fin d × Fin d => M p.1 p.2) (hw h)) (a, b)
    rw [pairMat_mulVec_repMatrix_self_apply]
    exact hentry

theorem matrix_of_vecOf (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.of (fun a b => vecOf W (a, b)) = W := by
  ext a b
  rfl

/-- The bridge, matrix form. -/
theorem pairInvariant_mat {W : Matrix (Fin d) (Fin d) ℂ} :
    vecOf W ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) ↔
      ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W := by
  rw [mem_pairInvariantSubmodule_repMatrix_self_iff, matrix_of_vecOf]

/-- **Intertwining from pair-invariance**: if `R * W * Rᵀ = W`
throughout, then `W * ρ̄(h) = ρ(h) * W` — multiply on the right by
`(Rᵀ)⁻¹ = ρ̄` (the unit identity of §2). -/
theorem intertwine_of_pairInvariant {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W) (h : G) :
    W * orientConj (repMatrix ρ) h = repMatrix ρ h * W := by
  calc W * orientConj (repMatrix ρ) h
      = (repMatrix ρ h * W * (repMatrix ρ h)ᵀ) * orientConj (repMatrix ρ) h := by
        rw [hW h]
    _ = repMatrix ρ h * W * ((repMatrix ρ h)ᵀ * orientConj (repMatrix ρ) h) := by
        simp only [mul_assoc]
    _ = repMatrix ρ h * W := by rw [transpose_mul_orientConj, mul_one]

/-- The transposed intertwining relation, from §2's transpose
dictionary applied to `intertwine_of_pairInvariant`. -/
theorem intertwine_transpose_of_pairInvariant {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W) (h : G) :
    Wᵀ * orientConj (repMatrix ρ) h = repMatrix ρ h * Wᵀ := by
  have hstep : ∀ g : G, Wᵀ * orientConj (repMatrix ρ) g⁻¹
      = repMatrix ρ g⁻¹ * Wᵀ := by
    intro g
    have hT := congrArg Matrix.transpose (intertwine_of_pairInvariant ρ hW g)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, repMatrix_transpose,
      orientConj_transpose] at hT
    exact hT.symm
  have hfin := hstep h⁻¹
  rwa [inv_inv] at hfin

/-- The starred intertwining relation: conjugating the transposed
relation entrywise. -/
theorem intertwine_star_of_pairInvariant {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W) (h : G) :
    star W * repMatrix ρ h = orientConj (repMatrix ρ) h * star W := by
  have hT := intertwine_transpose_of_pairInvariant ρ hW h
  have hC : (Wᵀ * orientConj (repMatrix ρ) h).map (starRingEnd ℂ)
      = (repMatrix ρ h * Wᵀ).map (starRingEnd ℂ) := by rw [hT]
  rw [map_conj_mul, map_conj_mul, map_conj_orientConj] at hC
  have e1 : (Wᵀ).map (starRingEnd ℂ) = star W := by
    ext i j
    show (starRingEnd ℂ) (Wᵀ i j) = star W i j
    rw [starRingEnd_eq_star, Matrix.transpose_apply, Matrix.star_apply]
  have e2 : (repMatrix ρ h).map (starRingEnd ℂ) = orientConj (repMatrix ρ) h := rfl
  rw [e1, e2] at hC
  exact hC

/-- The square `W * star W` lies in the commutant of `ρ`. -/
theorem mul_star_mem_commutant {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W) (h : G) :
    repMatrix ρ h * (W * star W) = (W * star W) * repMatrix ρ h := by
  calc repMatrix ρ h * (W * star W)
      = (repMatrix ρ h * W) * star W := by rw [mul_assoc]
    _ = (W * orientConj (repMatrix ρ) h) * star W := by
        rw [intertwine_of_pairInvariant ρ hW h]
    _ = W * (orientConj (repMatrix ρ) h * star W) := by rw [mul_assoc]
    _ = W * (star W * repMatrix ρ h) := by
        rw [intertwine_star_of_pairInvariant ρ hW h]
    _ = (W * star W) * repMatrix ρ h := by rw [← mul_assoc]

/-- The Hermitian square `star W * W` lies in the commutant of
the conjugate orientation `ρ̄`. -/
theorem star_mul_mem_commutant_orientConj {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : ∀ h : G, repMatrix ρ h * W * (repMatrix ρ h)ᵀ = W) (h : G) :
    orientConj (repMatrix ρ) h * (star W * W) = (star W * W) * orientConj (repMatrix ρ) h := by
  calc orientConj (repMatrix ρ) h * (star W * W)
      = (orientConj (repMatrix ρ) h * star W) * W := by rw [mul_assoc]
    _ = (star W * repMatrix ρ h) * W := by
        rw [← intertwine_star_of_pairInvariant ρ hW h]
    _ = star W * (repMatrix ρ h * W) := by rw [mul_assoc]
    _ = star W * (W * orientConj (repMatrix ρ) h) := by
        rw [← intertwine_of_pairInvariant ρ hW h]
    _ = (star W * W) * orientConj (repMatrix ρ) h := by rw [← mul_assoc]

theorem sum_normSq_transpose (W : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ j, ‖W j i‖ ^ 2) = ∑ i, ∑ j, ‖W i j‖ ^ 2 :=
  Finset.sum_comm

/-- Trace of the Hermitian square is the sum of the squared
norms of the entries. -/
theorem trace_star_mul_self (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (star W * W) = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ i j : Fin d, star (W j i) * W j i = ((‖W j i‖ : ℂ)) ^ 2 := by
    intro i j
    have h := Complex.conj_mul' (W j i)
    rwa [starRingEnd_eq_star] at h
  calc Matrix.trace (star W * W)
      = ∑ i, ∑ j, star (W j i) * W j i := by
        show (∑ i, (star W * W) i i) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [Matrix.star_apply]
    _ = ∑ i, ∑ j, ((‖W j i‖ : ℂ)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ((∑ i, ∑ j, ‖W j i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]
    _ = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by rw [sum_normSq_transpose]

/-- Trace of the other square is the same sum. -/
theorem trace_mul_star_self (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (W * star W) = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ i j : Fin d, W i j * star (W i j) = ((‖W i j‖ : ℂ)) ^ 2 := by
    intro i j
    rw [mul_comm]
    have h := Complex.conj_mul' (W i j)
    rwa [starRingEnd_eq_star] at h
  calc Matrix.trace (W * star W)
      = ∑ i, ∑ j, W i j * star (W i j) := by
        show (∑ i, (W * star W) i i) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [Matrix.star_apply]
    _ = ∑ i, ∑ j, ((‖W i j‖ : ℂ)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]

theorem sum_normSq_pos {W : Matrix (Fin d) (Fin d) ℂ} (hW : W ≠ 0) :
    0 < ∑ i, ∑ j, ‖W i j‖ ^ 2 := by
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, W i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hW (Matrix.ext fun i j => hcon i j)
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2)
    ⟨i₀, Finset.mem_univ i₀, Finset.sum_pos'
      (fun j _ => pow_nonneg (norm_nonneg _) 2)
      ⟨j₀, Finset.mem_univ j₀, pow_pos (norm_pos_iff.mpr hij) 2⟩⟩

/-- **The invariant submodule of `ρ ⊗ ρ` is the span of any
nonzero invariant matrix.** The two commutant squares of `W₀`
are the same nonzero scalar (their traces agree), so
`c⁻¹ • star W₀` is a two-sided inverse of `W₀`; any other
invariant `W` is then a commutant scalar times `W₀`. -/
theorem pairInvariantSubmodule_repMatrix_self_eq_span_of_ne_zero (hd : 0 < d)
    (hρirr : RepIrreducible ρ) {W₀ : Matrix (Fin d) (Fin d) ℂ}
    (hW₀ : vecOf W₀ ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)) (hW₀0 : W₀ ≠ 0) :
    pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)
      = Submodule.span ℂ {vecOf W₀} := by
  obtain hW₀mat : ∀ h : G, repMatrix ρ h * W₀ * (repMatrix ρ h)ᵀ = W₀ :=
    (pairInvariant_mat ρ).1 hW₀
  obtain ⟨c, hc⟩ := commutant_eq_smul_of_repIrreducible ρ hd hρirr (W₀ * star W₀)
    (fun h => mul_star_mem_commutant ρ hW₀mat h)
  obtain ⟨c', hc'⟩ := commutant_orientConj_eq_smul ρ hd hρirr (star W₀ * W₀)
    (fun h => star_mul_mem_commutant_orientConj ρ hW₀mat h)
  have htr1 : Matrix.trace (W₀ * star W₀) = c * (d : ℂ) := by
    rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have htr2 : Matrix.trace (star W₀ * W₀) = c' * (d : ℂ) := by
    rw [hc', Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  rw [trace_mul_star_self] at htr1
  rw [trace_star_mul_self] at htr2
  have hS : (0 : ℝ) < ∑ i, ∑ j, ‖W₀ i j‖ ^ 2 := sum_normSq_pos hW₀0
  have hSc : ((∑ i, ∑ j, ‖W₀ i j‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hS)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc0 : c ≠ 0 := fun hcz => by
    rw [hcz, zero_mul] at htr1
    exact hSc htr1
  have hcc : c = c' := by
    have heq : c * (d : ℂ) = c' * (d : ℂ) := by rw [← htr1, htr2]
    exact mul_right_cancel₀ hd0 heq
  set L : Matrix (Fin d) (Fin d) ℂ := c⁻¹ • star W₀ with hL
  have hLW : L * W₀ = 1 := by
    rw [hL, Matrix.smul_mul, hc', ← hcc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hWL : W₀ * L = 1 := by
    rw [hL, Matrix.mul_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  apply le_antisymm
  · intro w hw
    obtain hWmat : ∀ h : G, repMatrix ρ h * Matrix.of (fun a b => w (a, b))
        * (repMatrix ρ h)ᵀ = Matrix.of (fun a b => w (a, b)) :=
      (mem_pairInvariantSubmodule_repMatrix_self_iff ρ).1 hw
    have hLinter : ∀ h : G, orientConj (repMatrix ρ) h * L = L * repMatrix ρ h := by
      intro h
      rw [hL, Matrix.mul_smul, Matrix.smul_mul, intertwine_star_of_pairInvariant ρ hW₀mat h]
    have hA : ∀ h : G, orientConj (repMatrix ρ) h * (L * Matrix.of (fun a b => w (a, b)))
        = (L * Matrix.of (fun a b => w (a, b))) * orientConj (repMatrix ρ) h := by
      intro h
      calc orientConj (repMatrix ρ) h * (L * Matrix.of (fun a b => w (a, b)))
          = (orientConj (repMatrix ρ) h * L) * Matrix.of (fun a b => w (a, b)) := by
            rw [mul_assoc]
        _ = (L * repMatrix ρ h) * Matrix.of (fun a b => w (a, b)) := by rw [hLinter h]
        _ = L * (repMatrix ρ h * Matrix.of (fun a b => w (a, b))) := by rw [mul_assoc]
        _ = L * (Matrix.of (fun a b => w (a, b)) * orientConj (repMatrix ρ) h) := by
            rw [← intertwine_of_pairInvariant ρ hWmat h]
        _ = (L * Matrix.of (fun a b => w (a, b))) * orientConj (repMatrix ρ) h := by
            rw [← mul_assoc]
    obtain ⟨e, he⟩ := commutant_orientConj_eq_smul ρ hd hρirr _ hA
    have hWdecomp : Matrix.of (fun a b => w (a, b)) = e • W₀ := by
      have h1 : Matrix.of (fun a b => w (a, b))
          = W₀ * (L * Matrix.of (fun a b => w (a, b))) := by
        rw [← mul_assoc, hWL, one_mul]
      rw [h1, he, Matrix.mul_smul, Matrix.mul_one]
    rw [Submodule.mem_span_singleton]
    refine ⟨e, ?_⟩
    funext ⟨a, b⟩
    have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b) hWdecomp
    have h1 : Matrix.of (fun a b => w (a, b)) a b = w (a, b) := rfl
    rw [h1] at hentry
    show (e • vecOf W₀) (a, b) = w (a, b)
    rw [Pi.smul_apply, vecOf_apply, smul_eq_mul]
    rw [Matrix.smul_apply, smul_eq_mul] at hentry
    exact hentry.symm
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hW₀)

/-! ## §4. The twirl on the line; the flip trace is the indicator

The columns of the twirl `𝒥 = haarTwirl (ρ, ρ)` lie in the
invariant submodule, so on the line of §3 the twirl factors
entrywise as `F⁻¹ · Ŵ p · star (Ŵ q)`. The indicator is the flip
trace of the twirl: `ν = ∑ p, 𝒥 p (flip p)`. The flip preserves
the submodule, acts on the line by a scalar `ε` with `ε² = 1`,
and the flip trace evaluates to `star ε` — hence
`ν ∈ {0, 1, -1}`. -/

/-- The columns of the twirl lie in the invariant submodule. -/
theorem haarTwirl_col_mem (hρcont : Continuous fun g => repMatrix ρ g)
    (q : Fin d × Fin d) :
    (fun s => haarTwirl μG (repMatrix ρ) (repMatrix ρ) s q)
      ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  have h := haarTwirl_mulVec_mem μG (repMatrix ρ) (repMatrix ρ) hMmul hMone hMinv hMcont
    hMmul hMone hMinv hMcont (Pi.single q 1)
  rw [Matrix.mulVec_single_one] at h
  have h2 : (fun s => haarTwirl μG (repMatrix ρ) (repMatrix ρ) s q)
      = (haarTwirl μG (repMatrix ρ) (repMatrix ρ)).col q := by
    funext s
    rfl
  rw [h2]
  exact h

/-- If the invariant submodule is zero, every twirl entry is. -/
theorem twirl_apply_eq_zero_of_bot (hρcont : Continuous fun g => repMatrix ρ g)
    (hbot : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) = ⊥)
    (p q : Fin d × Fin d) :
    haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q = 0 := by
  have hmem := haarTwirl_col_mem μG ρ hρcont q
  rw [hbot] at hmem
  have hz : (fun s => haarTwirl μG (repMatrix ρ) (repMatrix ρ) s q) = 0 :=
    (Submodule.mem_bot ℂ).1 hmem
  simpa using congrFun hz p

/-- **Factorization of the twirl on the invariant line**: for a
nonzero invariant matrix `W₀`, with `Ŵ = vecOf W₀` and
`F = ∑ r, star (Ŵ r) * Ŵ r`,
`𝒥 p q = F⁻¹ * (Ŵ p * star (Ŵ q))`. -/
theorem twirl_pair_factor (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) {W₀ : Matrix (Fin d) (Fin d) ℂ}
    (hW₀ : vecOf W₀ ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)) (hW₀0 : W₀ ≠ 0)
    (p q : Fin d × Fin d) :
    haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q
      = ((∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ : ℂ)
        * (vecOf W₀ p * star (vecOf W₀ q)) := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  have hspan := pairInvariantSubmodule_repMatrix_self_eq_span_of_ne_zero ρ hd hρirr hW₀ hW₀0
  have hcol : ∀ q : Fin d × Fin d, ∃ c : ℂ,
      c • vecOf W₀ = (fun s => haarTwirl μG (repMatrix ρ) (repMatrix ρ) s q) := by
    intro q
    have hmem := haarTwirl_col_mem μG ρ hρcont q
    rw [hspan, Submodule.mem_span_singleton] at hmem
    exact hmem
  choose c hc using hcol
  have hJ : ∀ p q : Fin d × Fin d,
      haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q = c q * vecOf W₀ p := by
    intro p q
    have h := congrFun (hc q) p
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hJrow : ∀ p q : Fin d × Fin d,
      haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q
        = star (c p) * star (vecOf W₀ q) := by
    intro p q
    have hs : haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q
        = star (haarTwirl μG (repMatrix ρ) (repMatrix ρ) q p) := by
      have hstar := haarTwirl_star μG (repMatrix ρ) (repMatrix ρ) hMmul hMone hMinv hMcont
        hMmul hMone hMinv hMcont
      calc haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q
          = (star (haarTwirl μG (repMatrix ρ) (repMatrix ρ))) p q := by rw [hstar]
        _ = star (haarTwirl μG (repMatrix ρ) (repMatrix ρ) q p) :=
            Matrix.star_apply _ _ _
    rw [hs, hJ q p, star_mul, mul_comm]
  have hF : (∑ r, star (vecOf W₀ r) * vecOf W₀ r)
      = ((∑ i, ∑ j, ‖W₀ i j‖ ^ 2 : ℝ) : ℂ) := by
    calc (∑ r, star (vecOf W₀ r) * vecOf W₀ r)
        = ∑ i, ∑ j, star (W₀ i j) * W₀ i j := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            show star (vecOf W₀ (i, j)) * vecOf W₀ (i, j) = _
            rw [vecOf_apply]
      _ = ∑ i, ∑ j, ((‖W₀ i j‖ : ℂ)) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have h := Complex.conj_mul' (W₀ i j)
          rwa [starRingEnd_eq_star] at h
      _ = ((∑ i, ∑ j, ‖W₀ i j‖ ^ 2 : ℝ) : ℂ) := by
          simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]
  have hF0 : (∑ r, star (vecOf W₀ r) * vecOf W₀ r) ≠ 0 := by
    rw [hF]
    exact_mod_cast (ne_of_gt (sum_normSq_pos hW₀0))
  have hfix : ∀ p : Fin d × Fin d,
      star (c p) * (∑ r, star (vecOf W₀ r) * vecOf W₀ r) = vecOf W₀ p := by
    intro p
    have h := haarTwirl_mulVec_of_mem μG (repMatrix ρ) (repMatrix ρ) hMmul hMone hMinv hMcont
      hMmul hMone hMinv hMcont hW₀
    have hentry := congrFun h p
    rw [mat_mulVec_apply] at hentry
    rw [← hentry, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hJrow p q]; ring
  have hcp : ∀ p : Fin d × Fin d,
      (∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ * vecOf W₀ p = star (c p) := by
    intro p
    calc (∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ * vecOf W₀ p
        = (∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹
            * (star (c p) * (∑ r, star (vecOf W₀ r) * vecOf W₀ r)) := by rw [hfix p]
      _ = star (c p) := by
          rw [mul_comm (star (c p)) _, ← mul_assoc, inv_mul_cancel₀ hF0, one_mul]
  calc haarTwirl μG (repMatrix ρ) (repMatrix ρ) p q
      = star (c p) * star (vecOf W₀ q) := hJrow p q
    _ = ((∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ * vecOf W₀ p) * star (vecOf W₀ q) := by
        rw [hcp p]
    _ = ((∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ : ℂ)
          * (vecOf W₀ p * star (vecOf W₀ q)) := by rw [mul_assoc]

/-- The flip preserves the invariant submodule (transposition
preserves pair-invariance: reindexing the defining sum by
`prodComm`). -/
theorem flipVec_mem {w : (Fin d × Fin d) → ℂ}
    (hw : w ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)) :
    flipVec w ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
  rw [mem_pairInvariantSubmodule] at hw ⊢
  intro h
  funext ⟨a, b⟩
  have hwb := congrFun (hw h) (b, a)
  rw [pairMat_mulVec_apply, Fintype.sum_prod_type] at hwb
  rw [pairMat_mulVec_apply]
  show (∑ q, repMatrix ρ h a q.1 * repMatrix ρ h b q.2 * flipVec w q)
      = flipVec w (a, b)
  simp only [flipVec_apply]
  calc (∑ q : Fin d × Fin d, repMatrix ρ h a q.1 * repMatrix ρ h b q.2 * w (q.2, q.1))
      = ∑ x, ∑ y, repMatrix ρ h a x * repMatrix ρ h b y * w (y, x) :=
        Fintype.sum_prod_type
          (fun q : Fin d × Fin d => repMatrix ρ h a q.1 * repMatrix ρ h b q.2 * w (q.2, q.1))
    _ = ∑ y, ∑ x, repMatrix ρ h a x * repMatrix ρ h b y * w (y, x) := Finset.sum_comm
    _ = ∑ x, ∑ y, repMatrix ρ h b x * repMatrix ρ h a y * w (x, y) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    _ = w (b, a) := hwb

/-- The indicator is the flip trace of the twirl:
`ν = ∑ p, 𝒥 p (p.2, p.1)`. -/
theorem fsIndicator_eq_sum (hρcont : Continuous fun g => repMatrix ρ g) :
    fsIndicator ρ μG
      = ∑ p : Fin d × Fin d, haarTwirl μG (repMatrix ρ) (repMatrix ρ) p (p.2, p.1) := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  have hpt : ∀ g : G, charFn ρ (g * g)
      = ∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ g p.2 p.1 := by
    intro g
    calc charFn ρ (g * g)
        = ∑ i, ∑ k, repMatrix ρ g i k * repMatrix ρ g k i := by
          rw [charFn, repMatrix_mul]
          show (∑ i, (repMatrix ρ g * repMatrix ρ g) i i) = _
          exact Finset.sum_congr rfl fun i _ => Matrix.mul_apply
      _ = ∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ g p.2 p.1 :=
          (Fintype.sum_prod_type
            (fun p : Fin d × Fin d => repMatrix ρ g p.1 p.2 * repMatrix ρ g p.2 p.1)).symm
  show (∫ g, charFn ρ (g * g) ∂μG) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum]
  · exact Finset.sum_congr rfl fun p _ =>
      (haarTwirl_apply μG (repMatrix ρ) (repMatrix ρ) p (p.2, p.1)).symm
  · intro p _
    exact matFn_integrable_entry_mul μG (repMatrix ρ) (repMatrix ρ) hMmul hMone hMinv hMcont
      hMmul hMone hMinv hMcont p.1 p.2 p.2 p.1

/-- Vanishing case: if the invariant submodule is zero, the
indicator is zero. -/
theorem fsIndicator_eq_zero_of_bot (hρcont : Continuous fun g => repMatrix ρ g)
    (hbot : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) = ⊥) :
    fsIndicator ρ μG = 0 := by
  rw [fsIndicator_eq_sum μG ρ hρcont]
  exact Finset.sum_eq_zero fun p _ =>
    twirl_apply_eq_zero_of_bot μG ρ hρcont hbot p (p.2, p.1)

/-- Nonvanishing case: if the invariant submodule is nonzero,
the indicator is `star ε` for the flip scalar `ε` of the line,
and `ε² = 1`. -/
theorem exists_flip_scalar_of_ne_bot (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g)
    (hne : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) ≠ ⊥) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ fsIndicator ρ μG = star ε := by
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ), w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Submodule.eq_bot_iff _).2 fun x hx => hcon x hx)
  set W₀ : Matrix (Fin d) (Fin d) ℂ := Matrix.of (fun a b => w (a, b)) with hW₀def
  have hŴ : vecOf W₀ = w := by
    funext ⟨a, b⟩
    rfl
  have hW₀mem : vecOf W₀ ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
    rwa [hŴ]
  have hW₀0 : W₀ ≠ 0 := by
    intro h0
    apply hw0
    rw [← hŴ, h0]
    funext ⟨a, b⟩
    rfl
  have hspan := pairInvariantSubmodule_repMatrix_self_eq_span_of_ne_zero ρ hd hρirr hW₀mem hW₀0
  obtain ⟨ε, hε⟩ : ∃ ε : ℂ, flipVec (vecOf W₀) = ε • vecOf W₀ := by
    have hmem := flipVec_mem ρ hW₀mem
    rw [hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨ε, hε⟩ := hmem
    exact ⟨ε, hε.symm⟩
  have hε2 : ε ^ 2 = 1 := by
    have h2 : flipVec (flipVec (vecOf W₀)) = (ε ^ 2) • vecOf W₀ := by
      rw [hε, flipVec_smul, hε, smul_smul, pow_two]
    have h3 : flipVec (flipVec (vecOf W₀)) = vecOf W₀ := flipVec_flipVec _
    rw [h3] at h2
    have hŴ0 : vecOf W₀ ≠ 0 := by
      rw [hŴ]
      exact hw0
    obtain ⟨p, hp⟩ : ∃ p, vecOf W₀ p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hŴ0 (funext fun p => hcon p)
    have hentry := congrFun h2 p
    rw [Pi.smul_apply, smul_eq_mul] at hentry
    exact mul_right_cancel₀ hp (by rw [one_mul]; exact hentry.symm)
  refine ⟨ε, hε2, ?_⟩
  have hF0 : (∑ r, star (vecOf W₀ r) * vecOf W₀ r) ≠ 0 := by
    have hF : (∑ r, star (vecOf W₀ r) * vecOf W₀ r)
        = ((∑ i, ∑ j, ‖W₀ i j‖ ^ 2 : ℝ) : ℂ) := by
      calc (∑ r, star (vecOf W₀ r) * vecOf W₀ r)
          = ∑ i, ∑ j, star (W₀ i j) * W₀ i j := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              show star (vecOf W₀ (i, j)) * vecOf W₀ (i, j) = _
              rw [vecOf_apply]
        _ = ∑ i, ∑ j, ((‖W₀ i j‖ : ℂ)) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            have h := Complex.conj_mul' (W₀ i j)
            rwa [starRingEnd_eq_star] at h
        _ = ((∑ i, ∑ j, ‖W₀ i j‖ ^ 2 : ℝ) : ℂ) := by
            simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]
    rw [hF]
    exact_mod_cast (ne_of_gt (sum_normSq_pos hW₀0))
  calc fsIndicator ρ μG
      = ∑ p : Fin d × Fin d, haarTwirl μG (repMatrix ρ) (repMatrix ρ) p (p.2, p.1) :=
        fsIndicator_eq_sum μG ρ hρcont
    _ = ∑ p : Fin d × Fin d, ((∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ : ℂ)
          * (vecOf W₀ p * star (vecOf W₀ (p.2, p.1))) :=
        Finset.sum_congr rfl fun p _ =>
          twirl_pair_factor μG ρ hd hρirr hρcont hW₀mem hW₀0 p (p.2, p.1)
    _ = ((∑ r, star (vecOf W₀ r) * vecOf W₀ r)⁻¹ : ℂ)
          * ∑ p : Fin d × Fin d, vecOf W₀ p * star (vecOf W₀ (p.2, p.1)) := by
        rw [Finset.mul_sum]
    _ = star ε := by
        have hS : (∑ p : Fin d × Fin d, vecOf W₀ p * star (vecOf W₀ (p.2, p.1)))
            = star ε * (∑ r, star (vecOf W₀ r) * vecOf W₀ r) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hεp : vecOf W₀ (p.2, p.1) = ε * vecOf W₀ p := by
            have h := congrFun hε p
            rw [Pi.smul_apply, smul_eq_mul] at h
            exact h
          rw [hεp, star_mul]
          ring
        rw [hS, mul_comm (star ε) _, ← mul_assoc, inv_mul_cancel₀ hF0, one_mul]

/-- **The indicator takes values in `{0, 1, -1}`** (Frobenius–Schur):
at an irreducible `ρ`, `ν = 0`, `ν = 1`, or `ν = -1`. -/
theorem fsIndicator_mem (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) :
    fsIndicator ρ μG = 0 ∨ fsIndicator ρ μG = 1 ∨ fsIndicator ρ μG = -1 := by
  by_cases hbot : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) = ⊥
  · exact Or.inl (fsIndicator_eq_zero_of_bot μG ρ hρcont hbot)
  · obtain ⟨ε, hε2, hν⟩ := exists_flip_scalar_of_ne_bot μG ρ hd hρirr hρcont hbot
    have hε01 : ε = 1 ∨ ε = -1 := sq_eq_one_iff.1 hε2
    rcases hε01 with rfl | rfl
    · exact Or.inr (Or.inl (by rw [hν]; simp))
    · exact Or.inr (Or.inr (by rw [hν]; simp))

/-! ## §5. Invariant bilinear forms; the canonical form

The predicate `InvariantBilinearForm ρ J` is pair-invariance of
`J`'s entrywise conjugate, read through §2's transpose
dictionary: `J̄` is invariant under `(ρ, ρ)` iff `J` is
preserved by every `repMatrix ρ g`. Hence the `J`-vector
`jVec J` spans the invariant line when `J ≠ 0`; invariant
forms are unique up to a scalar (the second Schur use,
packaged); and a nonzero invariant form rescales by a positive
real square root to the normalization
`∑ i k, star (J i k) * J i k = d` — the **canonical form**.
The indicator vanishes iff no nonzero invariant form exists. -/

/-- The `J`-vector is the pair-vector of the entrywise
conjugate matrix. -/
theorem jVec_eq_vecOf_map_conj (J : Matrix (Fin d) (Fin d) ℂ) :
    jVec J = vecOf (J.map (starRingEnd ℂ)) := by
  funext p
  rw [jVec_apply, vecOf_apply, Matrix.map_apply, starRingEnd_eq_star]

/-- Entrywise conjugation preserves nonzeroness. -/
theorem map_conj_ne_zero {J : Matrix (Fin d) (Fin d) ℂ} (hJ : J ≠ 0) :
    J.map (starRingEnd ℂ) ≠ 0 := by
  intro h0
  apply hJ
  ext a b
  have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b) h0
  simp only [Matrix.map_apply, starRingEnd_eq_star, Matrix.zero_apply] at h1
  simpa using star_eq_zero.1 h1

/-- **Dictionary, forward**: an invariant bilinear form's
conjugate is pair-invariant. -/
theorem pairInvariant_map_conj_of_invariantBilinearForm {J : Matrix (Fin d) (Fin d) ℂ}
    (hJ : InvariantBilinearForm ρ J) :
    vecOf (J.map (starRingEnd ℂ)) ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
  rw [pairInvariant_mat]
  intro h
  have hJ' := hJ h⁻¹
  rw [repMatrix_transpose, inv_inv] at hJ'
  have e3 : ((repMatrix ρ h)ᵀ).map (starRingEnd ℂ) = repMatrix ρ h⁻¹ := by
    show (orientConj (repMatrix ρ) h)ᵀ = repMatrix ρ h⁻¹
    exact orientConj_transpose ρ h
  have hconj : (repMatrix ρ h * J.map (starRingEnd ℂ) * (repMatrix ρ h)ᵀ).map (starRingEnd ℂ)
      = (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    rw [map_conj_mul, map_conj_mul, map_conj_map_conj, e3]
    exact hJ'
  have hX : (repMatrix ρ h * J.map (starRingEnd ℂ) * (repMatrix ρ h)ᵀ)
      = ((repMatrix ρ h * J.map (starRingEnd ℂ) * (repMatrix ρ h)ᵀ).map
          (starRingEnd ℂ)).map (starRingEnd ℂ) :=
    (map_conj_map_conj _).symm
  rw [hX, hconj, map_conj_map_conj]

/-- **Dictionary, reverse**: pair-invariance of the conjugate
gives the invariant bilinear form. -/
theorem invariantBilinearForm_of_pairInvariant_map_conj {J : Matrix (Fin d) (Fin d) ℂ}
    (hW : vecOf (J.map (starRingEnd ℂ)) ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)) :
    InvariantBilinearForm ρ J := by
  intro g
  obtain hmat : ∀ h : G, repMatrix ρ h * J.map (starRingEnd ℂ) * (repMatrix ρ h)ᵀ
      = J.map (starRingEnd ℂ) := (pairInvariant_mat ρ).1 hW
  have h2 := hmat g⁻¹
  have hconj : (repMatrix ρ g⁻¹ * J.map (starRingEnd ℂ) * (repMatrix ρ g⁻¹)ᵀ).map
        (starRingEnd ℂ)
      = (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by rw [h2]
  rw [map_conj_mul, map_conj_mul, map_conj_map_conj] at hconj
  have e3 : ((repMatrix ρ g⁻¹)ᵀ).map (starRingEnd ℂ) = repMatrix ρ g := by
    show (orientConj (repMatrix ρ) g⁻¹)ᵀ = repMatrix ρ g
    rw [orientConj_transpose, inv_inv]
  have e5 : (repMatrix ρ g⁻¹).map (starRingEnd ℂ) = (repMatrix ρ g)ᵀ := by
    show orientConj (repMatrix ρ) g⁻¹ = (repMatrix ρ g)ᵀ
    exact (repMatrix_transpose ρ g).symm
  rw [e3, e5] at hconj
  exact hconj

/-- The `J`-vector of an invariant form is pair-invariant. -/
theorem jVec_mem {J : Matrix (Fin d) (Fin d) ℂ} (hJ : InvariantBilinearForm ρ J) :
    jVec J ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
  rw [jVec_eq_vecOf_map_conj]
  exact pairInvariant_map_conj_of_invariantBilinearForm ρ hJ

/-- A nonzero invariant submodule yields a nonzero invariant
bilinear form. -/
theorem exists_invariantBilinearForm_of_ne_bot
    (hne : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) ≠ ⊥) :
    ∃ J ≠ 0, InvariantBilinearForm ρ J := by
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ), w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Submodule.eq_bot_iff _).2 fun x hx => hcon x hx)
  set W₀ : Matrix (Fin d) (Fin d) ℂ := Matrix.of (fun a b => w (a, b)) with hW₀def
  have hŴ : vecOf W₀ = w := by
    funext ⟨a, b⟩
    rfl
  have hW₀mem : vecOf W₀ ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
    rwa [hŴ]
  have hW₀0 : W₀ ≠ 0 := by
    intro h0
    apply hw0
    rw [← hŴ, h0]
    funext ⟨a, b⟩
    rfl
  refine ⟨W₀.map (starRingEnd ℂ), map_conj_ne_zero hW₀0, ?_⟩
  apply invariantBilinearForm_of_pairInvariant_map_conj ρ
  show vecOf ((W₀.map (starRingEnd ℂ)).map (starRingEnd ℂ))
    ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)
  rw [map_conj_map_conj]
  exact hW₀mem

/-- **Uniqueness of invariant bilinear forms**: any two are
proportional (the span theorem of §3 read through the
dictionary). -/
theorem InvariantBilinearForm.unique (hd : 0 < d) (hρirr : RepIrreducible ρ)
    {J₁ J₂ : Matrix (Fin d) (Fin d) ℂ} (hJ₁ : InvariantBilinearForm ρ J₁)
    (hJ₂ : InvariantBilinearForm ρ J₂) (hJ₂0 : J₂ ≠ 0) :
    ∃ c : ℂ, J₁ = c • J₂ := by
  have hW₂ : vecOf (J₂.map (starRingEnd ℂ))
      ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) :=
    pairInvariant_map_conj_of_invariantBilinearForm ρ hJ₂
  have hspan := pairInvariantSubmodule_repMatrix_self_eq_span_of_ne_zero ρ hd hρirr hW₂
    (map_conj_ne_zero hJ₂0)
  have hmem : vecOf (J₁.map (starRingEnd ℂ))
      ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) :=
    pairInvariant_map_conj_of_invariantBilinearForm ρ hJ₁
  rw [hspan, Submodule.mem_span_singleton] at hmem
  obtain ⟨e, he⟩ := hmem
  refine ⟨star e, ?_⟩
  ext a b
  have hentry := congrFun he (a, b)
  rw [Pi.smul_apply, smul_eq_mul, vecOf_apply, vecOf_apply, Matrix.map_apply, Matrix.map_apply,
    starRingEnd_eq_star, starRingEnd_eq_star] at hentry
  have h2 := congrArg star hentry
  rw [star_mul, star_star, star_star] at h2
  show J₁ a b = (star e • J₂) a b
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  exact h2.symm

/-- The normalization sum of a matrix is the cast of its real
squared-norm sum. -/
theorem sum_star_mul_self_eq_cast (J : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ k, star (J i k) * J i k) = ((∑ i, ∑ k, ‖J i k‖ ^ 2 : ℝ) : ℂ) := by
  calc (∑ i, ∑ k, star (J i k) * J i k)
      = ∑ i, ∑ k, ((‖J i k‖ : ℂ)) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        have h := Complex.conj_mul' (J i k)
        rwa [starRingEnd_eq_star] at h
    _ = ((∑ i, ∑ k, ‖J i k‖ ^ 2 : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]

/-- A nonzero invariant form rescales by a positive real to
the normalization `∑ i k, star (J i k) * J i k = d`. -/
theorem exists_normalized_invariantBilinearForm
    (h : ∃ J ≠ 0, InvariantBilinearForm ρ J) :
    ∃ J, InvariantBilinearForm ρ J
      ∧ (∑ i, ∑ k, star (J i k) * J i k) = (d : ℂ) := by
  obtain ⟨J₀, hJ₀0, hJ₀⟩ := h
  have hSᵣ : (0 : ℝ) < ∑ i, ∑ k, ‖J₀ i k‖ ^ 2 := sum_normSq_pos hJ₀0
  set s : ℝ := Real.sqrt ((d : ℝ) / (∑ i, ∑ k, ‖J₀ i k‖ ^ 2)) with hs
  refine ⟨(s : ℂ) • J₀, ?_, ?_⟩
  · intro g
    show (repMatrix ρ g)ᵀ * ((s : ℂ) • J₀) * repMatrix ρ g = (s : ℂ) • J₀
    rw [Matrix.mul_smul, Matrix.smul_mul, hJ₀ g]
  · have hterm : ∀ i k : Fin d, star (((s : ℂ) • J₀) i k) * ((s : ℂ) • J₀) i k
        = (s : ℂ) ^ 2 * (star (J₀ i k) * J₀ i k) := by
      intro i k
      rw [Matrix.smul_apply, smul_eq_mul, star_mul]
      have hstar : star ((s : ℂ)) = (s : ℂ) := by simp
      rw [hstar]
      ring
    calc (∑ i, ∑ k, star (((s : ℂ) • J₀) i k) * ((s : ℂ) • J₀) i k)
        = ∑ i, ∑ k, (s : ℂ) ^ 2 * (star (J₀ i k) * J₀ i k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hterm i k
      _ = (s : ℂ) ^ 2 * (∑ i, ∑ k, star (J₀ i k) * J₀ i k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = (s : ℂ) ^ 2 * ((∑ i, ∑ k, ‖J₀ i k‖ ^ 2 : ℝ) : ℂ) := by
          rw [sum_star_mul_self_eq_cast]
      _ = (d : ℂ) := by
          have hs2 : (s : ℂ) ^ 2
              = (d : ℂ) / ((∑ i, ∑ k, ‖J₀ i k‖ ^ 2 : ℝ) : ℂ) := by
            have hsq : s ^ 2 = (d : ℝ) / (∑ i, ∑ k, ‖J₀ i k‖ ^ 2) := by
              rw [hs]
              exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg d) (le_of_lt hSᵣ))
            have hcast : ((s ^ 2 : ℝ) : ℂ)
                = (d : ℂ) / ((∑ i, ∑ k, ‖J₀ i k‖ ^ 2 : ℝ) : ℂ) := by
              rw [hsq, Complex.ofReal_div, Complex.ofReal_natCast]
            rwa [Complex.ofReal_pow] at hcast
          rw [hs2, div_mul_cancel₀ _
            (by exact_mod_cast (ne_of_gt hSᵣ) : ((∑ i, ∑ k, ‖J₀ i k‖ ^ 2 : ℝ) : ℂ) ≠ 0)]

/- The **canonical invariant bilinear form**: the normalized
invariant form when one exists (chosen; any two differ by a
unit-modulus phase, which the headline's `J`-tensor
`star (J i k) * J j l` cannot see), and `0` otherwise. -/
open Classical in
noncomputable def canonicalForm : Matrix (Fin d) (Fin d) ℂ :=
  if h : ∃ J, InvariantBilinearForm ρ J
      ∧ (∑ i, ∑ k, star (J i k) * J i k) = (d : ℂ) then Classical.choose h else 0

/-- Specification of the canonical form. -/
theorem canonicalForm_spec (h : ∃ J ≠ 0, InvariantBilinearForm ρ J) :
    InvariantBilinearForm ρ (canonicalForm ρ)
      ∧ (∑ i, ∑ k, star ((canonicalForm ρ) i k) * (canonicalForm ρ) i k) = (d : ℂ) := by
  obtain ⟨J, hJinv, hJnorm⟩ := exists_normalized_invariantBilinearForm ρ h
  have hex : ∃ J, InvariantBilinearForm ρ J
      ∧ (∑ i, ∑ k, star (J i k) * J i k) = (d : ℂ) := ⟨J, hJinv, hJnorm⟩
  have hcanon : canonicalForm ρ = Classical.choose hex := by
    unfold canonicalForm
    rw [dif_pos hex]
  rw [hcanon]
  exact Classical.choose_spec hex

/-- The canonical form is nonzero when a nonzero invariant
form exists (and `0 < d`). -/
theorem canonicalForm_ne_zero (hd : 0 < d) (h : ∃ J ≠ 0, InvariantBilinearForm ρ J) :
    canonicalForm ρ ≠ 0 := by
  intro h0
  have hnorm := (canonicalForm_spec ρ h).2
  rw [h0] at hnorm
  have hz : (∑ i, ∑ k, star ((0 : Matrix (Fin d) (Fin d) ℂ) i k)
      * ((0 : Matrix (Fin d) (Fin d) ℂ) i k)) = 0 := by simp
  rw [hz] at hnorm
  exact (by exact_mod_cast hd.ne' : (d : ℂ) ≠ 0) hnorm.symm

/-- The invariant submodule is the span of the canonical
`J`-vector, when a nonzero invariant form exists. -/
theorem pairInvariantSubmodule_eq_span_canonicalForm (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (h : ∃ J ≠ 0, InvariantBilinearForm ρ J) :
    pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ)
      = Submodule.span ℂ {jVec (canonicalForm ρ)} := by
  have hmem : vecOf ((canonicalForm ρ).map (starRingEnd ℂ))
      ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) := by
    have h := jVec_mem ρ (canonicalForm_spec ρ h).1
    rwa [jVec_eq_vecOf_map_conj] at h
  have h0 : (canonicalForm ρ).map (starRingEnd ℂ) ≠ 0 :=
    map_conj_ne_zero (canonicalForm_ne_zero ρ hd h)
  have hspan := pairInvariantSubmodule_repMatrix_self_eq_span_of_ne_zero ρ hd hρirr hmem h0
  rwa [← jVec_eq_vecOf_map_conj] at hspan

/-- **Vanishing criterion**: at an irreducible `ρ`, the
indicator is zero iff the invariant submodule is zero. -/
theorem fsIndicator_eq_zero_iff (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) :
    fsIndicator ρ μG = 0 ↔ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) = ⊥ := by
  constructor
  · intro hν
    by_contra hne
    obtain ⟨ε, hε2, hνε⟩ := exists_flip_scalar_of_ne_bot μG ρ hd hρirr hρcont hne
    rw [hν] at hνε
    have hε0 : ε = 0 := star_eq_zero.1 hνε.symm
    rw [hε0] at hε2
    simp at hε2
  · intro hbot
    exact fsIndicator_eq_zero_of_bot μG ρ hρcont hbot

/-- **Nonvanishing criterion** (briefed `fsIndicator_ne_zero_iff`):
at an irreducible `ρ`, the indicator is nonzero iff a nonzero
invariant bilinear form exists. -/
theorem fsIndicator_ne_zero_iff (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) :
    fsIndicator ρ μG ≠ 0 ↔ ∃ J ≠ 0, InvariantBilinearForm ρ J := by
  constructor
  · intro hν
    have hne : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) ≠ ⊥ := by
      intro hbot
      exact hν (fsIndicator_eq_zero_of_bot μG ρ hρcont hbot)
    exact exists_invariantBilinearForm_of_ne_bot ρ hne
  · rintro ⟨J, hJ0, hJinv⟩
    intro hν
    have hbot := (fsIndicator_eq_zero_iff μG ρ hd hρirr hρcont).1 hν
    have hmem := jVec_mem ρ (canonicalForm_spec ρ ⟨J, hJ0, hJinv⟩).1
    rw [hbot] at hmem
    have hz := (Submodule.mem_bot ℂ).1 hmem
    exact canonicalForm_ne_zero ρ hd ⟨J, hJ0, hJinv⟩ (by
      ext a b
      have h1 := congrFun hz (a, b)
      simp only [jVec_apply, Pi.zero_apply] at h1
      simpa using star_eq_zero.1 h1)

/-! ## §6. The headline, its conjugate form, and sewing

The `(2,0)` entry orthogonality: the two plain factors pair
their rows into the conjugated `J` and their columns into the
plain `J` — `star (J i k) * J j l` — at scale `(d:ℂ)⁻¹`,
pinned by the trace consistency of §4–§5 (the projector's
trace is `∫ χ(g)² = ν` composed with the flip; at `ν ≠ 0` the
line's projector has trace `1` and the normalization sum of
the canonical form is exactly `d`). The `(0,2)` form is the
conjugate corollary. Sewing contracts two characters through
the headline. -/

/-- **HEADLINE — the `(2,0)` entry orthogonality.** At an
irreducible `ρ`,
`∫ g, ρ(g) i j * ρ(g) k l = 0` if `ν = 0`, and otherwise
`(d:ℂ)⁻¹ * (star (J i k) * J j l)` for the canonical invariant
form `J` — the conjugated factor carries the row pair `(i, k)`,
the plain factor the column pair `(j, l)`. -/
theorem integral_repMatrix_mul_repMatrix (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) (i j k l : Fin d) :
    ∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else ((d : ℂ))⁻¹ * (star ((canonicalForm ρ) i k) * (canonicalForm ρ) j l) := by
  by_cases hν : fsIndicator ρ μG = 0
  · rw [if_pos hν]
    have hbot : pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) = ⊥ :=
      (fsIndicator_eq_zero_iff μG ρ hd hρirr hρcont).1 hν
    have h := twirl_apply_eq_zero_of_bot μG ρ hρcont hbot (i, k) (j, l)
    rw [show (∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG)
        = haarTwirl μG (repMatrix ρ) (repMatrix ρ) (i, k) (j, l) from
      (haarTwirl_apply μG (repMatrix ρ) (repMatrix ρ) (i, k) (j, l)).symm]
    exact h
  · rw [if_neg hν]
    have hJ : ∃ J ≠ 0, InvariantBilinearForm ρ J :=
      (fsIndicator_ne_zero_iff μG ρ hd hρirr hρcont).1 hν
    obtain ⟨hJinv, hJnorm⟩ := canonicalForm_spec ρ hJ
    have hJ0 : canonicalForm ρ ≠ 0 := canonicalForm_ne_zero ρ hd hJ
    have hmem : vecOf ((canonicalForm ρ).map (starRingEnd ℂ))
        ∈ pairInvariantSubmodule (repMatrix ρ) (repMatrix ρ) :=
      pairInvariant_map_conj_of_invariantBilinearForm ρ hJinv
    have hF : (∑ r, star (vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) r)
          * vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) r) = (d : ℂ) := by
      calc (∑ r, star (vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) r)
              * vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) r)
          = ∑ i, ∑ k, star ((canonicalForm ρ) i k) * (canonicalForm ρ) i k := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            show star (vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) (a, b))
                * vecOf ((canonicalForm ρ).map (starRingEnd ℂ)) (a, b) = _
            simp only [vecOf_apply, Matrix.map_apply, starRingEnd_eq_star, star_star]
            exact mul_comm _ _
        _ = (d : ℂ) := hJnorm
    have hfact := twirl_pair_factor μG ρ hd hρirr hρcont hmem (map_conj_ne_zero hJ0) (i, k) (j, l)
    rw [hF] at hfact
    rw [show (∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG)
        = haarTwirl μG (repMatrix ρ) (repMatrix ρ) (i, k) (j, l) from
      (haarTwirl_apply μG (repMatrix ρ) (repMatrix ρ) (i, k) (j, l)).symm, hfact]
    simp only [vecOf_apply, Matrix.map_apply, starRingEnd_eq_star, star_star]

/-- **The `(0,2)` form**: both factors conjugated. The
conjugate corollary of the headline — conjugate the `(2,0)`
identity and use that the twirl is self-adjoint in the form
of the integral of a conjugate. -/
theorem integral_star_repMatrix_mul_star_repMatrix (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) (i j k l : Fin d) :
    ∫ g, star (repMatrix ρ g i j) * star (repMatrix ρ g k l) ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else ((d : ℂ))⁻¹ * ((canonicalForm ρ) i k * star ((canonicalForm ρ) j l)) := by
  have hstar : star (∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG)
      = ∫ g, star (repMatrix ρ g i j) * star (repMatrix ρ g k l) ∂μG := by
    have h2 : star (∫ g, repMatrix ρ g i j * repMatrix ρ g k l ∂μG)
        = ∫ g, star (repMatrix ρ g i j * repMatrix ρ g k l) ∂μG := by
      simpa only [starRingEnd_apply] using
        (integral_conj (μ := μG) (f := fun g => repMatrix ρ g i j * repMatrix ρ g k l)).symm
    rw [h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show star (repMatrix ρ g i j * repMatrix ρ g k l)
        = star (repMatrix ρ g i j) * star (repMatrix ρ g k l)
    rw [star_mul, mul_comm]
  rw [← hstar, integral_repMatrix_mul_repMatrix μG ρ hd hρirr hρcont i j k l]
  by_cases hν : fsIndicator ρ μG = 0
  · rw [if_pos hν, if_pos hν, star_zero]
  · rw [if_neg hν, if_neg hν]
    simp only [star_mul, star_inv₀, star_star, star_natCast]
    ring

/-- **Character sewing** (the form PW-5 consumes): two
characters sewn through the `(2,0)` evaluation contract
against the `J`-tensor; the frozen words enter as
`repMatrix ρ (b * a)` and `repMatrix ρ (e * c)` by trace
cyclicity. -/
theorem charFn_sewing (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g => repMatrix ρ g) (a b c e : G) :
    ∫ g, charFn ρ (a * g * b) * charFn ρ (c * g * e) ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else ((d : ℂ))⁻¹ * ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
          (repMatrix ρ (b * a) p.2 p.1 * repMatrix ρ (e * c) q.2 q.1
            * (star ((canonicalForm ρ) p.1 q.1) * (canonicalForm ρ) p.2 q.2)) := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  have hχ : ∀ (x z g : G), charFn ρ (x * g * z)
      = ∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ (z * x) p.2 p.1 := by
    intro x z g
    calc charFn ρ (x * g * z)
        = Matrix.trace (repMatrix ρ g * (repMatrix ρ z * repMatrix ρ x)) := by
          rw [charFn, repMatrix_mul, repMatrix_mul, Matrix.trace_mul_comm, ← mul_assoc,
            Matrix.trace_mul_comm]
      _ = ∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ (z * x) p.2 p.1 := by
          rw [show repMatrix ρ z * repMatrix ρ x = repMatrix ρ (z * x) from
            (repMatrix_mul ρ z x).symm]
          show (∑ j, (repMatrix ρ g * repMatrix ρ (z * x)) j j) = _
          calc (∑ j, (repMatrix ρ g * repMatrix ρ (z * x)) j j)
              = ∑ j, ∑ k, repMatrix ρ g j k * repMatrix ρ (z * x) k j :=
                Finset.sum_congr rfl fun j _ => Matrix.mul_apply
            _ = ∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ (z * x) p.2 p.1 :=
                (Fintype.sum_prod_type
                  (fun p : Fin d × Fin d =>
                    repMatrix ρ g p.1 p.2 * repMatrix ρ (z * x) p.2 p.1)).symm
  have hInt : ∀ p q : Fin d × Fin d,
      Integrable (fun g => (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
        * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1)) μG := by
    intro p q
    have h := matFn_integrable_entry_mul μG (repMatrix ρ) (repMatrix ρ) hMmul hMone hMinv
      hMcont hMmul hMone hMinv hMcont p.1 p.2 q.1 q.2
    have heq : (fun g => (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
          * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1))
        = fun g => (repMatrix ρ (b * a) p.2 p.1 * repMatrix ρ (e * c) q.2 q.1)
          * (repMatrix ρ g p.1 p.2 * repMatrix ρ g q.1 q.2) := by
      funext g
      ring
    rw [heq]
    exact h.const_mul _
  calc ∫ g, charFn ρ (a * g * b) * charFn ρ (c * g * e) ∂μG
      = ∫ g, (∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
          * (∑ q : Fin d × Fin d, repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show charFn ρ (a * g * b) * charFn ρ (c * g * e)
              = (∑ p : Fin d × Fin d, repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
                * (∑ q : Fin d × Fin d, repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1)
          rw [hχ a b g, hχ c e g])
    _ = ∫ g, ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
          (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
            * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => Finset.sum_mul_sum ..)
    _ = ∑ p : Fin d × Fin d, ∫ g, ∑ q : Fin d × Fin d,
          (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
            * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1) ∂μG :=
        integral_finsetSum _ fun p _ => integrable_finset_sum _ fun q _ => hInt p q
    _ = ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
          ∫ g, (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
            * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1) ∂μG :=
        Finset.sum_congr rfl fun p _ => integral_finsetSum _ fun q _ => hInt p q
    _ = ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
          (repMatrix ρ (b * a) p.2 p.1 * repMatrix ρ (e * c) q.2 q.1)
            * ∫ g, repMatrix ρ g p.1 p.2 * repMatrix ρ g q.1 q.2 ∂μG := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        have heq : (fun g => (repMatrix ρ g p.1 p.2 * repMatrix ρ (b * a) p.2 p.1)
              * (repMatrix ρ g q.1 q.2 * repMatrix ρ (e * c) q.2 q.1))
            = fun g => (repMatrix ρ (b * a) p.2 p.1 * repMatrix ρ (e * c) q.2 q.1)
              * (repMatrix ρ g p.1 p.2 * repMatrix ρ g q.1 q.2) := by
          funext g
          ring
        rw [heq, integral_const_mul]
    _ = if fsIndicator ρ μG = 0 then 0
          else ((d : ℂ))⁻¹ * ∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
            (repMatrix ρ (b * a) p.2 p.1 * repMatrix ρ (e * c) q.2 q.1
              * (star ((canonicalForm ρ) p.1 q.1) * (canonicalForm ρ) p.2 q.2)) := by
        by_cases hν : fsIndicator ρ μG = 0
        · rw [if_pos hν]
          refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
          rw [integral_repMatrix_mul_repMatrix μG ρ hd hρirr hρcont p.1 p.2 q.1 q.2,
            if_pos hν, mul_zero]
        · rw [if_neg hν, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [integral_repMatrix_mul_repMatrix μG ρ hd hρirr hρcont p.1 p.2 q.1 q.2,
            if_neg hν]
          ring

end Setup

end ThetLogos
