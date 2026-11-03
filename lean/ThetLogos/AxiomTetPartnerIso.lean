/-
# AXIOM TET — PARTNER SECTOR, SP-5: ISOSPECTRALITY OF THE TWO HAMILTONIANS

Brick: SP-5, the Partner Sector's stretch pin, fired by Jeff
2026-11-03 by name ("All" — the park on SP-5 is lifted by his word).
Built in the isolated worktree `~/workspace/thet-logos-sp5`, branch
`sp5-lane`, from main-tree HEAD `4e35329`; NOT integrated — the
parent runs the ceremony.

**The pin (registered form, from the scoping
`axiom-zero-supersymmetry-scoping-2026-11-03.md`).** SP-5: the
NONZERO spectra of `vertexHam` and `edgeHam` coincide with
multiplicities — registered there in the characteristic-polynomial
form

  `x ^ |E| * p_v(x) = x ^ |V| * p_e(x)`,

where `p_v`, `p_e` are the characteristic polynomials of the two
Hamiltonians. K-SP-ISO fired on this pin in the Partner brick:
SP-0..SP-4 landed FULL, SP-5 was named OPEN, its blocker recorded
as: the eigenspace-intertwining route "needs spectral machinery
for self-adjoint operators on plain function spaces that this
Mathlib does not provide off the shelf (no inner product instances
on `ι → ℝ` as bare types; the spectral theorem would have to be
assembled via matrices/eigenspaces by hand)".

**VERDICT: FULL.** The pin lands in its registered form
(`sp5_charpoly_identity`), and the eigenspace-intertwining form
lands with it (`eigenspaceEquiv`, `finrank_eigenspace_eq`).

**The blocker, retired — the analysis.** The recorded blocker was
half right and wholly non-fatal. Right: this Mathlib has no
inner-product or spectral-theorem API for bare pi types, and none
is assembled here. Non-fatal, twice over:

1. *The polynomial identity needs no spectral theorem.* For any
   two rectangular matrices `A : Matrix m n R`, `B : Matrix n m R`,
   the identity `X ^ card n * (A * B).charpoly = X ^ card m *
   (B * A).charpoly` is Mathlib stock
   (`Matrix.charpoly_mul_comm'`, proved there by a
   block-determinant computation). The two Hamiltonians are, at
   the level of their standard-basis matrices, exactly such a
   product pair: `H_v = Dᵀ D` and `H_e = D Dᵀ` with
   `D = wDiff G w`, once the matrix of `Dᵀ` is identified
   (`toMatrix'_wAdjDiff_eq_transpose`, through the diagonal
   root-weight matrix and the Partner brick's landed
   `toMatrix'_diffOp`).

2. *The intertwining needs no spectral theorem either.* An
   eigenspace is a kernel; no diagonalization is involved in
   mapping one to the other. On the `lam`-eigenspace with
   `lam ≠ 0`, the composites of the restricted maps are
   `Dᵀ ∘ D = H_v = lam • id` and `D ∘ Dᵀ = H_e = lam • id`, so
   `D` and `lam⁻¹ • Dᵀ` are explicit mutual inverses between the
   two eigenspaces (`eigenspaceEquiv`) — injectivity and
   surjectivity in one line each, exactly the finite-dimensional
   algebra the pin's route described. No eigenvalue is ever
   shown to exist; nothing is diagonalized.

**What is NOT proved here, on the face.** The spectral theorem
itself (diagonalizability of the two Hamiltonians; equality of
algebraic and geometric multiplicities) is neither proved nor
needed: the polynomial identity is the algebraic-multiplicity
statement, the eigenspace equivalence is the
geometric-multiplicity statement, and this brick lands both
independently without asserting that they coincide. The T2
numerical agreement recorded in the Partner dossier is
superseded as evidence by the T1 statements below; it is not
cited anywhere in a proof.

**Weights discipline.** No positivity hypothesis on `w` appears
anywhere in this module: isospectrality is pure algebra of the
pair `(D, Dᵀ)` and holds for arbitrary real weights. Positivity
was the price of the kernel and index statements (SP-2..SP-4),
not of this one.

**Naming fence (inherited, in force).** "Supersymmetry" here is
finite SUSY quantum mechanics on a graph. No particle-physics
claim rides on this brick.

**NO CLAIM** — parts of any official Millennium statement closed
by this module: 0. Dials: 0/4.

This module is NOT in the root import list of the library; it is
verified by a targeted build.
-/

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import ThetLogos.AxiomTetPartner

attribute [local instance] Classical.propDecidable

open Finset SimpleGraph Polynomial

namespace ThetLogos

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)

variable (w : Sym2 V → ℝ)

/-! ## The standard-basis matrices of the weighted operators

`mulEdgeLin` is diagonal in the standard basis; the weighted
operators `D = √W ∘ d` and `Dᵀ = dᵀ ∘ √W` therefore have matrices
`diag(√W) * (matrix of d)` and `(matrix of dᵀ) * diag(√W)`, and
the Partner brick's `toMatrix'_diffOp` then identifies the matrix
of `Dᵀ` as the transpose of the matrix of `D`. -/

/-- The matrix of edge-multiplication is the diagonal matrix. -/
theorem toMatrix'_mulEdgeLin (c : ↥G.edgeSet → ℝ) :
    LinearMap.toMatrix' (mulEdgeLin G c) = Matrix.diagonal c := by
  ext i j
  rw [LinearMap.toMatrix'_apply, mulEdgeLin_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, mul_one, Matrix.diagonal_apply_eq]
  · rw [Pi.single_eq_of_ne h, mul_zero]
    exact (Matrix.diagonal_apply_ne _ h).symm

/-- The matrix of `D = √W ∘ d` is `diag(√W)` times the matrix
of `d`. -/
theorem toMatrix'_wDiff :
    LinearMap.toMatrix' (wDiff G w)
      = Matrix.diagonal (rootWeight G w)
        * LinearMap.toMatrix' (diffOp G) := by
  show LinearMap.toMatrix' ((mulEdgeLin G (rootWeight G w)).comp (diffOp G)) = _
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulEdgeLin]

/-- The matrix of `Dᵀ = dᵀ ∘ √W` is the matrix of `dᵀ` times
`diag(√W)`. -/
theorem toMatrix'_wAdjDiff :
    LinearMap.toMatrix' (wAdjDiff G w)
      = LinearMap.toMatrix' (adjDiff G)
        * Matrix.diagonal (rootWeight G w) := by
  show LinearMap.toMatrix' ((adjDiff G).comp (mulEdgeLin G (rootWeight G w))) = _
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulEdgeLin]

/-- **The matrix of `Dᵀ` is the transpose of the matrix of `D`** —
the matrix-level adjoint statement for the weighted pair,
completing the Partner brick's `toMatrix'_diffOp` (the unweighted
case). -/
theorem toMatrix'_wAdjDiff_eq_transpose :
    LinearMap.toMatrix' (wAdjDiff G w)
      = (LinearMap.toMatrix' (wDiff G w)).transpose := by
  rw [toMatrix'_wAdjDiff, toMatrix'_wDiff, Matrix.transpose_mul,
    Matrix.diagonal_transpose]
  have h := congrArg Matrix.transpose (toMatrix'_diffOp G)
  rw [Matrix.transpose_transpose] at h
  rw [h]

/-- The matrix of `H_v = Dᵀ ∘ D` is the product of the two
matrices. -/
theorem toMatrix'_vertexHam :
    LinearMap.toMatrix' (vertexHam G w)
      = LinearMap.toMatrix' (wAdjDiff G w)
        * LinearMap.toMatrix' (wDiff G w) := by
  show LinearMap.toMatrix' ((wAdjDiff G w).comp (wDiff G w)) = _
  rw [LinearMap.toMatrix'_comp]

/-- The matrix of `H_e = D ∘ Dᵀ` is the product in the other
order. -/
theorem toMatrix'_edgeHam :
    LinearMap.toMatrix' (edgeHam G w)
      = LinearMap.toMatrix' (wDiff G w)
        * LinearMap.toMatrix' (wAdjDiff G w) := by
  show LinearMap.toMatrix' ((wDiff G w).comp (wAdjDiff G w)) = _
  rw [LinearMap.toMatrix'_comp]

/-- The characteristic polynomial of a pi-type operator is the
characteristic polynomial of its standard-basis matrix. -/
theorem charpoly_vertexHam :
    (vertexHam G w).charpoly
      = (LinearMap.toMatrix' (vertexHam G w)).charpoly := by
  nth_rewrite 1 [← Matrix.toLin'_toMatrix' (vertexHam G w)]
  exact Matrix.charpoly_toLin' _

/-- The characteristic polynomial of a pi-type operator is the
characteristic polynomial of its standard-basis matrix. -/
theorem charpoly_edgeHam :
    (edgeHam G w).charpoly
      = (LinearMap.toMatrix' (edgeHam G w)).charpoly := by
  nth_rewrite 1 [← Matrix.toLin'_toMatrix' (edgeHam G w)]
  exact Matrix.charpoly_toLin' _

/-! ## SP-5, the registered form -/

/-- **SP-5 (isospectrality), registered polynomial form.** For
every finite web and EVERY real weight function `w` (no
positivity hypothesis), the characteristic polynomials `p_v`,
`p_e` of the two Partner Hamiltonians satisfy

  `X ^ |E| * p_v(X) = X ^ |V| * p_e(X)`,

`|E| = Fintype.card ↥G.edgeSet`: the nonzero spectra of `H_v`
and `H_e` coincide with (algebraic) multiplicities. One
application of Mathlib's rectangular charpoly identity
`Matrix.charpoly_mul_comm'` to the product pair
`(matrix of Dᵀ, matrix of D)`. -/
theorem sp5_charpoly_identity :
    X ^ Fintype.card ↥G.edgeSet * (vertexHam G w).charpoly
      = X ^ Fintype.card V * (edgeHam G w).charpoly := by
  rw [charpoly_vertexHam, charpoly_edgeHam, toMatrix'_vertexHam,
    toMatrix'_edgeHam]
  exact Matrix.charpoly_mul_comm' _ _

/-- SP-5 with the edge count in the Partner brick's own
bookkeeping (`#G.edgeFinset`, as in SP-3/SP-4). -/
theorem sp5_charpoly_identity_edgeFinset :
    X ^ #G.edgeFinset * (vertexHam G w).charpoly
      = X ^ Fintype.card V * (edgeHam G w).charpoly := by
  rw [SimpleGraph.edgeFinset_card]
  exact sp5_charpoly_identity G w

/-! ## SP-5, the eigenspace-intertwining form

The route the original lane named: `D` maps the `lam`-eigenspace
of `H_v` into the `lam`-eigenspace of `H_e`, `Dᵀ` maps back, and
for `lam ≠ 0` the two restricted maps are mutual inverses up to
the scale `lam`. No spectral theorem is used or needed — an
eigenspace is a kernel, and the inverse is explicit. -/

/-- `D` carries the `lam`-eigenspace of `H_v` into the
`lam`-eigenspace of `H_e`: `H_e (D f) = D (H_v f)` because both
sides are `D Dᵀ D f`. -/
theorem wDiff_mem_eigenspace_image {lam : ℝ} {f : V → ℝ}
    (hf : f ∈ Module.End.eigenspace (vertexHam G w) lam) :
    wDiff G w f ∈ Module.End.eigenspace (edgeHam G w) lam := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  have hcomp : edgeHam G w (wDiff G w f) = wDiff G w (vertexHam G w f) := rfl
  rw [hcomp, hf, map_smul]

/-- `Dᵀ` carries the `lam`-eigenspace of `H_e` into the
`lam`-eigenspace of `H_v`: `H_v (Dᵀ g) = Dᵀ (H_e g)` because
both sides are `Dᵀ D Dᵀ g`. -/
theorem wAdjDiff_mem_eigenspace_image {lam : ℝ} {g : ↥G.edgeSet → ℝ}
    (hg : g ∈ Module.End.eigenspace (edgeHam G w) lam) :
    wAdjDiff G w g ∈ Module.End.eigenspace (vertexHam G w) lam := by
  rw [Module.End.mem_eigenspace_iff] at hg ⊢
  have hcomp : vertexHam G w (wAdjDiff G w g)
      = wAdjDiff G w (edgeHam G w g) := rfl
  rw [hcomp, hg, map_smul]

/-- **The eigenspace equivalence.** For `lam ≠ 0`, the
`lam`-eigenspaces of the two Hamiltonians are linearly
equivalent, by `D` in one direction and `lam⁻¹ • Dᵀ` in the
other — on the eigenspace the composites are `lam⁻¹ • H = id`
on each side. -/
noncomputable def eigenspaceEquiv (lam : ℝ) (hlam : lam ≠ 0) :
    ↥(Module.End.eigenspace (vertexHam G w) lam) ≃ₗ[ℝ]
      ↥(Module.End.eigenspace (edgeHam G w) lam) where
  toFun f := ⟨wDiff G w f, wDiff_mem_eigenspace_image G w f.2⟩
  map_add' f g := by
    apply Subtype.ext
    show wDiff G w (f.1 + g.1) = wDiff G w f.1 + wDiff G w g.1
    exact map_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    show wDiff G w (r • f.1) = r • wDiff G w f.1
    exact map_smul _ _ _
  invFun g := ⟨lam⁻¹ • wAdjDiff G w g,
    Submodule.smul_mem _ _
      (wAdjDiff_mem_eigenspace_image G w g.2)⟩
  left_inv f := by
    apply Subtype.ext
    have hf : vertexHam G w f.1 = lam • f.1 :=
      Module.End.mem_eigenspace_iff.mp f.2
    show lam⁻¹ • wAdjDiff G w (wDiff G w f.1) = f.1
    have h2 : wAdjDiff G w (wDiff G w f.1) = vertexHam G w f.1 := rfl
    rw [h2, hf, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  right_inv g := by
    apply Subtype.ext
    have hg : edgeHam G w g.1 = lam • g.1 :=
      Module.End.mem_eigenspace_iff.mp g.2
    show wDiff G w (lam⁻¹ • wAdjDiff G w g.1) = g.1
    have h2 : wDiff G w (wAdjDiff G w g.1) = edgeHam G w g.1 := rfl
    rw [map_smul, h2, hg, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- **SP-5, geometric-multiplicity form.** For every `lam ≠ 0`,
the `lam`-eigenspaces of `H_v` and `H_e` have the same
dimension: the nonzero spectra coincide with geometric
multiplicities. -/
theorem finrank_eigenspace_eq {lam : ℝ} (hlam : lam ≠ 0) :
    Module.finrank ℝ ↥(Module.End.eigenspace (vertexHam G w) lam)
      = Module.finrank ℝ ↥(Module.End.eigenspace (edgeHam G w) lam) :=
  LinearEquiv.finrank_eq (eigenspaceEquiv G w lam hlam)

end ThetLogos
