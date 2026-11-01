/-
# ThetLogos.IcosidodecaCensus — PHI-C3: the full census, by propagation (combinatorics only)

**NO CLAIM. Salvage label (per scoping memo
`routeb-general-scratch/scoping-phi-icosa-2026-10-30.md`, §4–§5):
T1-about-the-polyhedron, zero NCG content, not a promotion of the
mnemonic.** This module is PHI-C3, the closing brick of the priced
salvage line PHI-C: over the explicit icosidodecahedron chain model
of PHI-C0 (`ThetLogos.IcosidodecaChain` — its names are cited here,
never forked), consuming PHI-C1's chain identity
(`ThetLogos.IcosidodecaBoundary`: `d1 ∘ₗ d2 = 0`) and PHI-C2's
face-split independence and signed-sum relation
(`ThetLogos.IcosidodecaFaceSplit`), the full census is proved:

* `ker ∂₂ = ℚ ∙ (1, …, 1)` — by coefficient propagation over the
  connected dual graph: at each edge the kernel equation involves
  exactly its two incident faces (one triangle, one pentagon, with
  opposite signs, by PHI-C2's relation data), forcing the two
  coefficients to agree; a breadth-first parent table over the 32
  faces (finite incidence data, checked by `decide`) propagates
  that agreement from every face back to face 0.
* `rank ∂₂ = 31` — rank-nullity over `finrank C₂ = 32` with
  `finrank ker ∂₂ = 1`.
* `rank ∂₁ = 29` — by the dual propagation: the kernel of the
  transpose map `∂₁ᵀ` is the constants on vertices (propagation
  over the connected 1-skeleton, via a breadth-first parent table
  over the 30 vertices), so `rank ∂₁ᵀ = 30 − 1 = 29` by
  rank-nullity, and `Matrix.rank_transpose` moves the count back
  to `∂₁`.
* Homology census `(H₀, H₁, H₂) = (1, 0, 1)` in the model's own
  terms: `finrank ker ∂₂ = 1`; exactness at `C₁`,
  `ker ∂₁ = range ∂₂` (PHI-C1's inclusion plus the two finranks
  `31 = 31`), so the `H₁` quotient has finrank `0`;
  `finrank (C₀ ⧸ range ∂₁) = 1`.

**K-PHI-4 compliance (on the face):** no census claim in this
module is closed by citing a machine rank computation. The only
`decide` proofs are finite *incidence* facts over ℤ or over the
explicit tables (the PHI-C1/C2 pattern): which faces meet at the
witness edges, the parent tables' rank decrease, and PHI-C2's
signed-sum relation. Every kernel / rank / homology statement is
closed by the propagation argument and rank-nullity, as above.
Combinatorics only. NO CLAIM attaches to this line; it touches no
dial and never mentions W₂₂.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import ThetLogos.IcosidodecaChain
import ThetLogos.IcosidodecaBoundary
import ThetLogos.IcosidodecaFaceSplit

namespace ThetLogos

/-! ## Dual-graph breadth-first parent table (faces)

Breadth-first search of the dual graph from face 0 over PHI-C0's
incidence data: face order reached is
0; 20, 22, 21; then the triangles across them; etc. `dualParent f`
is the face from which `f` was first reached, `dualWit f` a shared
edge of `f` and its parent, `dualRank f` the BFS depth. These are
explicit finite tables; their *properties* (rank decrease, shared
edge, no third face at the witness edge) are the incidence facts
checked by `decide` below. -/

/-- BFS parent of each face in the dual graph (index = face). -/
def dualParentList : List (Fin 32) :=
  [0, 20, 20, 22, 20, 21, 20, 21, 22, 22, 23, 23, 24, 25, 24, 25,
   26, 27, 28, 29, 0, 0, 0, 1, 2, 3, 4, 5, 8, 10, 12, 13]

/-- A witness edge shared by each face and its BFS parent
    (index = face). -/
def dualWitList : List (Fin 60) :=
  [0, 2, 5, 8, 10, 12, 14, 17, 24, 26, 28, 30, 34, 36, 40, 42,
   44, 46, 54, 57, 0, 1, 4, 9, 15, 18, 20, 22, 32, 38, 48, 50]

/-- BFS depth of each face in the dual graph (index = face). -/
def dualRankList : List ℕ :=
  [0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4,
   4, 4, 4, 6, 1, 1, 1, 3, 3, 3, 3, 3, 3, 5, 5, 5]

/-- The BFS parent of face `f` in the dual graph. -/
def dualParent (f : Fin 32) : Fin 32 :=
  dualParentList.get ⟨f.val, by
    have h1 : dualParentList.length = 32 := rfl
    have h2 := f.isLt
    omega⟩

/-- A witness edge shared by face `f` and its BFS parent. -/
def dualWit (f : Fin 32) : Fin 60 :=
  dualWitList.get ⟨f.val, by
    have h1 : dualWitList.length = 32 := rfl
    have h2 := f.isLt
    omega⟩

/-- The BFS depth of face `f` in the dual graph. -/
def dualRank (f : Fin 32) : ℕ :=
  dualRankList.get ⟨f.val, by
    have h1 : dualRankList.length = 32 := rfl
    have h2 := f.isLt
    omega⟩

/-- Incidence fact (by `decide` over the explicit tables): the BFS
    parent of every non-root face has strictly smaller BFS depth. -/
theorem dual_parent_rank_lt : ∀ f : Fin 32, f ≠ 0 →
    dualRank (dualParent f) < dualRank f := by decide

/-- Incidence fact: face 0 is the unique face of BFS depth 0. -/
theorem dual_rank_zero : ∀ f : Fin 32, dualRank f = 0 ↔ f = 0 := by
  decide

/-- Incidence fact: at the witness edge of a non-root face `f`,
    both `f` and its parent carry a nonzero incidence sign. -/
theorem dual_parent_signs : ∀ f : Fin 32, f ≠ 0 →
    faceSign f (dualWit f) ≠ 0 ∧ faceSign (dualParent f) (dualWit f) ≠ 0 := by
  decide

/-- Incidence fact: at the witness edge of a non-root face `f`, no
    face other than `f` and its parent carries a nonzero incidence
    sign — the witness edge has exactly its two incident faces. -/
theorem dual_wit_other_zero : ∀ f : Fin 32, f ≠ 0 → ∀ h : Fin 32,
    h ≠ f → h ≠ dualParent f → faceSign h (dualWit f) = 0 := by decide

/-! ## The edge equation and propagation over the dual graph -/

/-- `∂₂` applied entry-wise: `(∂₂ x) e = ∑ f, (faceSign f e) • x f`,
    read off PHI-C0's definition of `d2Mat`. -/
theorem d2_apply_sum (x : Fin 32 → ℚ) (e : Fin 60) :
    d2 x e = ∑ f : Fin 32, (faceSign f e : ℚ) * x f := by
  rw [d2, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro f _
  rfl

/-- The two signs at a witness edge cancel over ℤ: by PHI-C2's
    signed-sum relation the sum of all 32 signs at the edge is 0,
    and by `dual_wit_other_zero` only the two incident faces
    contribute. -/
theorem dual_sign_sum_zero (f : Fin 32) (hf : f ≠ 0) :
    faceSign f (dualWit f) + faceSign (dualParent f) (dualWit f) = 0 := by
  have hpf : f ≠ dualParent f := by
    intro h
    have hlt := dual_parent_rank_lt f hf
    rw [← h] at hlt
    exact lt_irrefl _ hlt
  have hz := signed_sum_zero_Z (dualWit f)
  have hsub : (∑ h ∈ ({f, dualParent f} : Finset (Fin 32)), faceSign h (dualWit f))
      = ∑ h : Fin 32, faceSign h (dualWit f) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro h _ hh
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    exact dual_wit_other_zero f hf h hh.1 hh.2
  rw [Finset.sum_pair hpf] at hsub
  omega

/-- **Propagation step.** A kernel vector of `∂₂` takes equal
    values at a non-root face and its BFS parent: the kernel
    equation at their shared witness edge has exactly those two
    terms, with opposite nonzero signs. -/
theorem ker_d2_parent_eq (x : Fin 32 → ℚ) (hx : d2 x = 0)
    (f : Fin 32) (hf : f ≠ 0) : x f = x (dualParent f) := by
  set e := dualWit f with he
  set p := dualParent f with hp
  have hpf : f ≠ p := by
    intro h
    have hlt := dual_parent_rank_lt f hf
    rw [← hp, ← h] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hsf, hsp⟩ := dual_parent_signs f hf
  -- the kernel equation at the witness edge, reduced to two terms
  have hEq : (faceSign f e : ℚ) * x f + (faceSign p e : ℚ) * x p = 0 := by
    have h0 : d2 x e = 0 := by rw [hx]; rfl
    rw [d2_apply_sum] at h0
    have hsub : (∑ h ∈ ({f, p} : Finset (Fin 32)), (faceSign h e : ℚ) * x h)
        = ∑ h : Fin 32, (faceSign h e : ℚ) * x h := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro h _ hh
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      have hZ := dual_wit_other_zero f hf h hh.1 hh.2
      rw [hZ]; simp
    rw [Finset.sum_pair hpf] at hsub
    rw [hsub]
    exact h0
  -- the two signs are opposite, so the equation is `s • (x f − x p) = 0`
  have hsign : (faceSign p e : ℚ) = - (faceSign f e : ℚ) := by
    have hZ := dual_sign_sum_zero f hf
    have : ((faceSign f e + faceSign p e : ℤ) : ℚ) = 0 := by
      rw [hZ]; exact Int.cast_zero
    rw [Int.cast_add] at this
    linarith
  have hne : (faceSign f e : ℚ) ≠ 0 := by exact_mod_cast hsf
  have hmul : (faceSign f e : ℚ) * (x f - x p) = 0 := by
    rw [hsign] at hEq
    linarith [hEq]
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact absurd h1 hne
  · exact sub_eq_zero.mp h1

/-- **Propagation.** Every kernel vector of `∂₂` is constant:
    induction on the BFS depth bound, stepping to the parent. -/
theorem ker_d2_apply_eq (x : Fin 32 → ℚ) (hx : d2 x = 0) :
    ∀ f : Fin 32, x f = x 0 := by
  have key : ∀ n : ℕ, ∀ f : Fin 32, dualRank f ≤ n → x f = x 0 := by
    intro n
    induction n with
    | zero =>
      intro f hf
      have hf0 : f = 0 := (dual_rank_zero f).mp (Nat.eq_zero_of_le_zero hf)
      rw [hf0]
    | succ n IH =>
      intro f hf
      by_cases hf0 : f = 0
      · rw [hf0]
      · have h1 : x f = x (dualParent f) := ker_d2_parent_eq x hx f hf0
        have h2 : dualRank (dualParent f) ≤ n := by
          have hlt := dual_parent_rank_lt f hf0
          omega
        rw [h1, IH _ h2]
  intro f
  exact key (dualRank f) f le_rfl

/-- **PHI-C3, clause 1.** `ker ∂₂ = ℚ ∙ (1, …, 1)`: the all-ones
    vector of PHI-C2 spans the kernel of `∂₂`. The reverse
    inclusion is PHI-C2's landed relation
    (`faceSumVec_mem_ker`). -/
theorem ker_d2_eq_span :
    LinearMap.ker d2 = ℚ ∙ faceSumVec := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, faceSumVec, mul_one]
    exact (ker_d2_apply_eq x hx f).symm
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr faceSumVec_mem_ker)

theorem faceSumVec_ne_zero : faceSumVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [faceSumVec] at h0

/-- `finrank ker ∂₂ = 1`. -/
theorem finrank_ker_d2 : Module.finrank ℚ (LinearMap.ker d2) = 1 := by
  rw [ker_d2_eq_span, finrank_span_singleton faceSumVec_ne_zero]

/-- **PHI-C3, clause 2.** `rank ∂₂ = 31`, by rank-nullity from
    clause 1 (`finrank C₂ = 32`). -/
theorem finrank_range_d2 : Module.finrank ℚ (LinearMap.range d2) = 31 := by
  have h := d2.finrank_range_add_finrank_ker
  rw [finrank_ker_d2, Module.finrank_fintype_fun_eq_card] at h
  simp at h
  omega

/-! ## The 1-skeleton parent table (vertices) and `∂₁ᵀ`

Breadth-first search of the 1-skeleton from vertex 0 over PHI-C0's
edge list. `vertParent v` is the vertex from which `v` was first
reached, `vertWit v` a connecting edge, `vertRank v` the BFS
depth — explicit tables, properties by `decide` as before. -/

/-- BFS parent of each vertex in the 1-skeleton (index = vertex). -/
def vertParentList : List (Fin 30) :=
  [0, 0, 0, 0, 0, 1, 2, 3, 4, 1, 2, 3, 4, 9, 5,
   6, 11, 9, 10, 11, 12, 14, 15, 14, 15, 17, 18, 19, 20, 25]

/-- A witness edge joining each vertex to its BFS parent
    (index = vertex). -/
def vertWitList : List (Fin 60) :=
  [0, 0, 1, 2, 3, 5, 7, 10, 12, 6, 8, 11, 13, 24, 16,
   19, 28, 25, 27, 29, 31, 34, 36, 35, 37, 41, 43, 45, 47, 55]

/-- BFS depth of each vertex in the 1-skeleton (index = vertex). -/
def vertRankList : List ℕ :=
  [0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3,
   3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5]

/-- The BFS parent of vertex `v` in the 1-skeleton. -/
def vertParent (v : Fin 30) : Fin 30 :=
  vertParentList.get ⟨v.val, by
    have h1 : vertParentList.length = 30 := rfl
    have h2 := v.isLt
    omega⟩

/-- A witness edge joining vertex `v` to its BFS parent. -/
def vertWit (v : Fin 30) : Fin 60 :=
  vertWitList.get ⟨v.val, by
    have h1 : vertWitList.length = 30 := rfl
    have h2 := v.isLt
    omega⟩

/-- The BFS depth of vertex `v` in the 1-skeleton. -/
def vertRank (v : Fin 30) : ℕ :=
  vertRankList.get ⟨v.val, by
    have h1 : vertRankList.length = 30 := rfl
    have h2 := v.isLt
    omega⟩

/-- Incidence fact: the BFS parent of every non-root vertex has
    strictly smaller BFS depth. -/
theorem vert_parent_rank_lt : ∀ v : Fin 30, v ≠ 0 →
    vertRank (vertParent v) < vertRank v := by decide

/-- Incidence fact: vertex 0 is the unique vertex of BFS depth 0. -/
theorem vert_rank_zero : ∀ v : Fin 30, vertRank v = 0 ↔ v = 0 := by
  decide

/-- Incidence fact: the witness edge of a non-root vertex joins it
    to its BFS parent (in one of the two orientations). -/
theorem vert_parent_edge : ∀ v : Fin 30, v ≠ 0 →
    (edgeTail (vertWit v) = v ∧ edgeHead (vertWit v) = vertParent v) ∨
    (edgeTail (vertWit v) = vertParent v ∧ edgeHead (vertWit v) = v) := by
  decide

/-! ## Propagation over the 1-skeleton: `ker ∂₁ᵀ` is the constants -/

/-- The transpose boundary map `∂₁ᵀ : C₀ → C₁` over ℚ. -/
def d1T : (Fin 30 → ℚ) →ₗ[ℚ] (Fin 60 → ℚ) := Matrix.mulVecLin (Matrix.transpose d1Mat)

/-- The all-ones vector of `C₀`. -/
def vertOnes : Fin 30 → ℚ := fun _ => 1

/-- `∂₁ᵀ` applied entry-wise: `(∂₁ᵀ y) e = y (head e) − y (tail e)`,
    since the `e`-th column of `∂₁` is `−1` at the tail, `+1` at
    the head, `0` elsewhere (PHI-C0's definition). -/
theorem d1T_apply (y : Fin 30 → ℚ) (e : Fin 60) :
    d1T y e = y (edgeHead e) - y (edgeTail e) := by
  have hne : edgeTail e ≠ edgeHead e := ne_of_lt (edge_tail_lt_head e)
  have hsum : d1T y e = ∑ v : Fin 30, d1Mat v e * y v := by
    rw [d1T, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro v _
    rw [Matrix.transpose_apply]
  rw [hsum]
  have hsub : (∑ v ∈ ({edgeTail e, edgeHead e} : Finset (Fin 30)), d1Mat v e * y v)
      = ∑ v : Fin 30, d1Mat v e * y v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    simp [d1Mat, hv.1, hv.2]
  rw [← hsub, Finset.sum_pair hne]
  have ht : d1Mat (edgeTail e) e = -1 := by simp [d1Mat]
  have hh : d1Mat (edgeHead e) e = 1 := by
    simp [d1Mat, Ne.symm hne]
  rw [ht, hh]
  ring

/-- **Propagation step (vertices).** A kernel vector of `∂₁ᵀ`
    takes equal values at a non-root vertex and its BFS parent:
    the kernel equation at their shared witness edge is
    `y (head) − y (tail) = 0`. -/
theorem ker_d1T_parent_eq (y : Fin 30 → ℚ) (hy : d1T y = 0)
    (v : Fin 30) (hv : v ≠ 0) : y v = y (vertParent v) := by
  have h0 : d1T y (vertWit v) = 0 := by
    rw [hy]; rfl
  rw [d1T_apply] at h0
  rcases vert_parent_edge v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at h0
  · exact (sub_eq_zero.mp h0).symm
  · exact sub_eq_zero.mp h0

/-- **Propagation (vertices).** Every kernel vector of `∂₁ᵀ` is
    constant: induction on the BFS depth bound. -/
theorem ker_d1T_apply_eq (y : Fin 30 → ℚ) (hy : d1T y = 0) :
    ∀ v : Fin 30, y v = y 0 := by
  have key : ∀ n : ℕ, ∀ v : Fin 30, vertRank v ≤ n → y v = y 0 := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hv0 : v = 0 := (vert_rank_zero v).mp (Nat.eq_zero_of_le_zero hv)
      rw [hv0]
    | succ n IH =>
      intro v hv
      by_cases hv0 : v = 0
      · rw [hv0]
      · have h1 : y v = y (vertParent v) := ker_d1T_parent_eq y hy v hv0
        have h2 : vertRank (vertParent v) ≤ n := by
          have hlt := vert_parent_rank_lt v hv0
          omega
        rw [h1, IH _ h2]
  intro v
  exact key (vertRank v) v le_rfl

theorem vertOnes_ne_zero : vertOnes ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vertOnes] at h0

/-- `∂₁ᵀ` kills the all-ones vertex vector. -/
theorem d1T_vertOnes : d1T vertOnes = 0 := by
  funext e
  rw [d1T_apply]
  simp [vertOnes]

/-- `ker ∂₁ᵀ = ℚ ∙ (1, …, 1)`: the constants on vertices. -/
theorem ker_d1T_eq_span :
    LinearMap.ker d1T = ℚ ∙ vertOnes := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [Submodule.mem_span_singleton]
    refine ⟨y 0, ?_⟩
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, vertOnes, mul_one]
    exact (ker_d1T_apply_eq y hy v).symm
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (LinearMap.mem_ker.mpr d1T_vertOnes))

/-- `finrank ker ∂₁ᵀ = 1`. -/
theorem finrank_ker_d1T : Module.finrank ℚ (LinearMap.ker d1T) = 1 := by
  rw [ker_d1T_eq_span, finrank_span_singleton vertOnes_ne_zero]

/-- `rank ∂₁ᵀ = 29`, by rank-nullity from `finrank ker ∂₁ᵀ = 1`
    (`finrank C₀ = 30`). -/
theorem finrank_range_d1T : Module.finrank ℚ (LinearMap.range d1T) = 29 := by
  have h := d1T.finrank_range_add_finrank_ker
  rw [finrank_ker_d1T, Module.finrank_fintype_fun_eq_card] at h
  simp at h
  omega

/-- **PHI-C3, clause 3.** `rank ∂₁ = 29`: the transpose count
    moved back across `Matrix.rank_transpose` (`Matrix.rank` is by
    definition the finrank of the range of `mulVecLin`, which is
    what `∂₁` and `∂₁ᵀ` are). -/
theorem finrank_range_d1 : Module.finrank ℚ (LinearMap.range d1) = 29 := by
  have e1 : (Matrix.transpose d1Mat).rank = Module.finrank ℚ (LinearMap.range d1T) := rfl
  have e2 : d1Mat.rank = Module.finrank ℚ (LinearMap.range d1) := rfl
  rw [← e2, ← Matrix.rank_transpose, e1]
  exact finrank_range_d1T

/-- `finrank ker ∂₁ = 31`, by rank-nullity from clause 3
    (`finrank C₁ = 60`). -/
theorem finrank_ker_d1 : Module.finrank ℚ (LinearMap.ker d1) = 31 := by
  have h := d1.finrank_range_add_finrank_ker
  rw [finrank_range_d1, Module.finrank_fintype_fun_eq_card] at h
  simp at h
  omega

/-! ## Homology census -/

/-- PHI-C1's inclusion, as submodules: `range ∂₂ ≤ ker ∂₁`. -/
theorem range_d2_le_ker_d1 :
    LinearMap.range d2 ≤ LinearMap.ker d1 := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [LinearMap.mem_ker, ← hx]
  have h := LinearMap.ext_iff.mp d1_comp_d2 x
  simpa [LinearMap.comp_apply] using h

/-- **PHI-C3, clause 4 (H₁).** Exactness at `C₁`:
    `ker ∂₁ = range ∂₂` — PHI-C1's inclusion closed by the two
    finranks `finrank ker ∂₁ = 31 = finrank range ∂₂`, so the
    `H₁` quotient `ker ∂₁ ⧸ range ∂₂` has finrank `0`. -/
theorem ker_d1_eq_range_d2 :
    LinearMap.ker d1 = LinearMap.range d2 :=
  (Submodule.eq_of_le_of_finrank_eq range_d2_le_ker_d1 (by
    rw [finrank_ker_d1, finrank_range_d2])).symm

/-- **PHI-C3, clause 4 (H₀).** `finrank (C₀ ⧸ range ∂₁) = 1`,
    from clause 3 by the quotient rank-nullity identity. -/
theorem finrank_quotient_range_d1 :
    Module.finrank ℚ ((Fin 30 → ℚ) ⧸ LinearMap.range d1) = 1 := by
  have h := (LinearMap.range d1).finrank_quotient_add_finrank
  rw [finrank_range_d1, Module.finrank_fintype_fun_eq_card] at h
  simp at h
  omega

/-- **PHI-C3, the census.** The homology finranks of PHI-C0's
    explicit model are `(H₀, H₁, H₂) = (1, 0, 1)`, in the model's
    own terms: `H₂ = ker ∂₂` has finrank `1`; `H₁` vanishes by
    exactness `ker ∂₁ = range ∂₂` with both finranks `31`;
    `H₀ = C₀ ⧸ range ∂₁` has finrank `1`; and the two ranks are
    `rank ∂₂ = 31`, `rank ∂₁ = 29`. -/
theorem icosidodeca_census :
    Module.finrank ℚ (LinearMap.ker d2) = 1 ∧
    Module.finrank ℚ (LinearMap.range d2) = 31 ∧
    Module.finrank ℚ (LinearMap.range d1) = 29 ∧
    LinearMap.ker d1 = LinearMap.range d2 ∧
    Module.finrank ℚ (LinearMap.ker d1) = 31 ∧
    Module.finrank ℚ ((Fin 30 → ℚ) ⧸ LinearMap.range d1) = 1 :=
  ⟨finrank_ker_d2, finrank_range_d2, finrank_range_d1,
   ker_d1_eq_range_d2, finrank_ker_d1, finrank_quotient_range_d1⟩

#print axioms dual_parent_rank_lt
#print axioms dual_rank_zero
#print axioms dual_parent_signs
#print axioms dual_wit_other_zero
#print axioms dual_sign_sum_zero
#print axioms ker_d2_parent_eq
#print axioms ker_d2_apply_eq
#print axioms ker_d2_eq_span
#print axioms finrank_ker_d2
#print axioms finrank_range_d2
#print axioms vert_parent_rank_lt
#print axioms vert_rank_zero
#print axioms vert_parent_edge
#print axioms d1T_apply
#print axioms ker_d1T_parent_eq
#print axioms ker_d1T_apply_eq
#print axioms ker_d1T_eq_span
#print axioms finrank_ker_d1T
#print axioms finrank_range_d1T
#print axioms finrank_range_d1
#print axioms finrank_ker_d1
#print axioms range_d2_le_ker_d1
#print axioms ker_d1_eq_range_d2
#print axioms finrank_quotient_range_d1
#print axioms icosidodeca_census

end ThetLogos
