/-
# ThetLogos.IcosidodecaFaceSplit — PHI-C2: face-split independence (combinatorics only)

**NO CLAIM. Salvage label (per scoping memo
`routeb-general-scratch/scoping-phi-icosa-2026-10-30.md`, §4–§5):
T1-about-the-polyhedron, zero NCG content, not a promotion of the
mnemonic.** This module is PHI-C2 of the priced salvage line PHI-C
only: over the explicit icosidodecahedron chain model of PHI-C0
(`ThetLogos.IcosidodecaChain` — its names are cited here, never
forked; the chain identity ∂₁ ∘ ∂₂ = 0 is PHI-C1,
`ThetLogos.IcosidodecaBoundary`), the 20 triangle boundary columns
of ∂₂ are linearly independent over ℚ, the 12 pentagon boundary
columns of ∂₂ are linearly independent over ℚ, and the signed sum
of all 32 face boundaries is zero. Combinatorics only. NO CLAIM
attaches to this line; it touches no dial and never mentions W₂₂.

## Uniqueness remainder (named on the face, per the PHI-C2 pack)

This brick does NOT prove that the signed all-face relation is the
*unique* relation among the 32 columns of ∂₂ (equivalently
`ker ∂₂ = ℚ • (1, …, 1)`). That uniqueness statement is exactly
PHI-C3's remainder: it needs the rank census (`rank ∂₂ = 31`, by
coefficient propagation over the connected dual graph), and per the
pre-registered kill K-PHI-4 it may not be closed by citing a machine
rank computation as a hypothesis. What is proved here is what C3's
census consumes as input: the two family independences (ranks 20
and 12 of the two face-split blocks) and the one exhibited relation
`∂₂ (Σ_f single f) = 0`.

## Proof route

Disjoint edge supports, exactly as the memo registers. PHI-C0's
sanity data says every edge lies in exactly one triangle and in
exactly one pentagon (`edge_in_exactly_one_triangle`,
`edge_in_exactly_one_pentagon`). So evaluating a purported
relation among the triangle columns at a chosen edge of triangle
`i` kills every other triangle term and isolates the `i`-th
coefficient, whose value there is a sign `±1 ≠ 0`; likewise for
pentagons. All finite incidence checks are done over ℤ by kernel
`decide` (the rational checks are casts of the integer ones), so
kernel `decide` is never asked to reduce rational arithmetic.
The signed-sum relation is the same pattern: per edge, the integer
sum `∑ f, faceSign f e` vanishes by `decide` — each edge is hit
once by its triangle and once by its pentagon, with opposite
signs — and the rational statement is its cast.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import ThetLogos.IcosidodecaChain

namespace ThetLogos

/-! ## Face-family index embeddings (PHI-C0's ordering: faces
    0..19 triangles, 20..31 pentagons) -/

/-- The `i`-th triangle face, as a face index (`i < 20 ≤ 32`). -/
def triFace (i : Fin 20) : Fin 32 := ⟨i.val, by have h := i.isLt; omega⟩

/-- The `i`-th pentagon face, as a face index (`20 + i < 32`). -/
def penFace (i : Fin 12) : Fin 32 := ⟨i.val + 20, by have h := i.isLt; omega⟩

/-- Triangle faces have boundary length 3 in PHI-C0's data. -/
theorem tri_boundary_length :
    ∀ i : Fin 20, (faceBoundary (triFace i)).length = 3 := by decide

/-- Pentagon faces have boundary length 5 in PHI-C0's data. -/
theorem pen_boundary_length :
    ∀ i : Fin 12, (faceBoundary (penFace i)).length = 5 := by decide

/-! ## Witness edges: the first edge of each face's boundary.
    By PHI-C0's each-edge-in-exactly-one-triangle/pentagon data,
    a triangle's witness edge occurs in no other triangle's
    boundary, and a pentagon's witness edge in no other pentagon's. -/

/-- A witness edge of triangle `i`: the first edge of its signed
    boundary. -/
def triEdge (i : Fin 20) : Fin 60 :=
  ((faceBoundary (triFace i)).get ⟨0, by
    have h := tri_boundary_length i
    omega⟩).1

/-- A witness edge of pentagon `i`: the first edge of its signed
    boundary. -/
def penEdge (i : Fin 12) : Fin 60 :=
  ((faceBoundary (penFace i)).get ⟨0, by
    have h := pen_boundary_length i
    omega⟩).1

/-- The witness edge of triangle `i` carries sign `±1 ≠ 0` in
    triangle `i`'s own boundary (integer check, by `decide`). -/
theorem triEdge_self_sign_ne :
    ∀ i : Fin 20, faceSign (triFace i) (triEdge i) ≠ 0 := by decide

/-- The witness edge of triangle `i` carries sign `0` in every
    other triangle's boundary: triangle edge-supports are pairwise
    disjoint (integer check, by `decide`). -/
theorem triEdge_other_sign_zero :
    ∀ i j : Fin 20, j ≠ i → faceSign (triFace j) (triEdge i) = 0 := by
  decide

/-- The witness edge of pentagon `i` carries sign `±1 ≠ 0` in
    pentagon `i`'s own boundary (integer check, by `decide`). -/
theorem penEdge_self_sign_ne :
    ∀ i : Fin 12, faceSign (penFace i) (penEdge i) ≠ 0 := by decide

/-- The witness edge of pentagon `i` carries sign `0` in every
    other pentagon's boundary: pentagon edge-supports are pairwise
    disjoint (integer check, by `decide`). -/
theorem penEdge_other_sign_zero :
    ∀ i j : Fin 12, j ≠ i → faceSign (penFace j) (penEdge i) = 0 := by
  decide

/-! ## The face-split boundary columns of ∂₂ -/

/-- The `i`-th triangle boundary column of ∂₂, as a vector in the
    edge space `Fin 60 → ℚ`. -/
def triCol (i : Fin 20) : Fin 60 → ℚ := fun e => d2Mat e (triFace i)

/-- The `i`-th pentagon boundary column of ∂₂, as a vector in the
    edge space `Fin 60 → ℚ`. -/
def penCol (i : Fin 12) : Fin 60 → ℚ := fun e => d2Mat e (penFace i)

/-- The triangle columns are PHI-C0's ∂₂ basis columns:
    `triCol i = ∂₂ (single (triFace i) 1)`. -/
theorem triCol_eq_d2_single (i : Fin 20) :
    triCol i = d2 (Pi.single (triFace i) 1) := by
  funext e
  rw [d2_apply_single]
  rfl

/-- The pentagon columns are PHI-C0's ∂₂ basis columns:
    `penCol i = ∂₂ (single (penFace i) 1)`. -/
theorem penCol_eq_d2_single (i : Fin 12) :
    penCol i = d2 (Pi.single (penFace i) 1) := by
  funext e
  rw [d2_apply_single]
  rfl

/-! ## Independence, by witness-edge evaluation -/

/-- **PHI-C2, triangle half.** The 20 triangle boundary columns of
    ∂₂ are linearly independent over ℚ: evaluating a relation at
    triangle `i`'s witness edge isolates its coefficient, which is
    multiplied there by a sign `±1 ≠ 0`. -/
theorem triCol_linearIndependent : LinearIndependent ℚ triCol := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (triEdge i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at h
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun hi => absurd
    (Finset.mem_univ i) hi)] at h
  · -- h : g i * triCol i (triEdge i) = 0, and the column value is a
    -- nonzero sign, so g i = 0.
    have hne : triCol i (triEdge i) ≠ 0 := by
      have hZ := triEdge_self_sign_ne i
      unfold triCol d2Mat
      exact_mod_cast hZ
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hne
  · -- Other triangle columns vanish at triangle `i`'s witness edge.
    have hZ := triEdge_other_sign_zero i j hj
    unfold triCol d2Mat
    rw [show (faceSign (triFace j) (triEdge i) : ℚ) = 0 from by
      exact_mod_cast hZ]
    simp

/-- **PHI-C2, pentagon half.** The 12 pentagon boundary columns of
    ∂₂ are linearly independent over ℚ: evaluating a relation at
    pentagon `i`'s witness edge isolates its coefficient, which is
    multiplied there by a sign `±1 ≠ 0`. -/
theorem penCol_linearIndependent : LinearIndependent ℚ penCol := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (penEdge i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at h
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun hi => absurd
    (Finset.mem_univ i) hi)] at h
  · have hne : penCol i (penEdge i) ≠ 0 := by
      have hZ := penEdge_self_sign_ne i
      unfold penCol d2Mat
      exact_mod_cast hZ
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hne
  · have hZ := penEdge_other_sign_zero i j hj
    unfold penCol d2Mat
    rw [show (faceSign (penFace j) (penEdge i) : ℚ) = 0 from by
      exact_mod_cast hZ]
    simp

/-! ## The signed-sum relation -/

/-- The all-ones vector of `C₂`: the sum of all 32 (signed) face
    basis elements, before applying ∂₂. -/
def faceSumVec : Fin 32 → ℚ := fun _ => 1

/-- The all-ones vector is literally `∑ f, Pi.single f 1`. -/
theorem faceSumVec_eq_sum_single :
    faceSumVec = ∑ f : Fin 32, Pi.single f (1 : ℚ) := by
  funext e
  simp [faceSumVec, Finset.sum_apply, Pi.single_apply,
    Finset.sum_ite_eq, Finset.mem_univ]

set_option maxRecDepth 16384 in
/-- The signed-sum relation over ℤ, entry-wise: for every edge `e`,
    `∑ f, faceSign f e = 0` — each edge is hit once by its triangle
    and once by its pentagon, with opposite signs. Proved by kernel
    `decide` over PHI-C0's explicit generated data, recomputed from
    the definitions, not cited from any probe. -/
theorem signed_sum_zero_Z : ∀ e : Fin 60, ∑ f : Fin 32, faceSign f e = 0 := by
  decide

/-- **PHI-C2, the relation.** `∂₂ (Σ signed faces) = 0`: the signed
    sum of all 32 face boundaries vanishes in the edge space. (That
    this is the *unique* relation is PHI-C3's remainder — see the
    module header; it is NOT claimed here.) -/
theorem d2_faceSumVec_zero : d2 faceSumVec = 0 := by
  funext e
  have h1 : d2 faceSumVec e
      = ∑ f : Fin 32, (faceSign f e : ℚ) := by
    rw [d2, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro f _
    simp [faceSumVec, d2Mat]
  rw [h1, ← Int.cast_sum, signed_sum_zero_Z]
  exact Int.cast_zero

/-- The relation in basis-sum form:
    `∂₂ (∑ f, Pi.single f 1) = 0`. -/
theorem d2_sum_single_zero : d2 (∑ f : Fin 32, Pi.single f (1 : ℚ)) = 0 := by
  rw [← faceSumVec_eq_sum_single]
  exact d2_faceSumVec_zero

/-- The relation as kernel membership: the all-ones vector of `C₂`
    lies in `ker ∂₂`. -/
theorem faceSumVec_mem_ker : faceSumVec ∈ LinearMap.ker d2 := by
  rw [LinearMap.mem_ker]
  exact d2_faceSumVec_zero

#print axioms tri_boundary_length
#print axioms pen_boundary_length
#print axioms triEdge_self_sign_ne
#print axioms triEdge_other_sign_zero
#print axioms penEdge_self_sign_ne
#print axioms penEdge_other_sign_zero
#print axioms triCol_linearIndependent
#print axioms penCol_linearIndependent
#print axioms signed_sum_zero_Z
#print axioms d2_faceSumVec_zero
#print axioms d2_sum_single_zero
#print axioms faceSumVec_mem_ker

end ThetLogos
