/-
# AXIOM TET — THE PARTNER SECTOR: finite supersymmetry of the Axiom Zero model

Brick: THE PARTNER SECTOR (working label; the scope's own name for the
object is the partner sector of the Axiom Zero model). Commission: Jeff,
2026-11-03 02:05 EST — "run it", fired the moment the Axiom Tet brick
landed FULL, because this brick consumes AZ-2W. Built from the frozen
scope `axiom-zero-supersymmetry-scoping-2026-11-03.md` (pins SP-0..SP-5)
on top of `ThetLogos.AxiomTet` (the Axiom Zero model: web, need weights,
break energy).

**What this module proves — and all it proves.** The Axiom Tet model has
the square supersymmetry is built from: break energy `= dᵀ W d`, a sum of
weighted squares, whose zero modes are the constants. This module builds
the OTHER half of the pair and the supercharge that generates both.
One difference operator, two Hamiltonians:

* `diffOp` — the (unweighted) difference operator `d`, vertex states →
  edge states, `(df)(e) = f(head) − f(tail)` for the orientation induced
  by the linear order on `V` (head = max endpoint, tail = min endpoint).
* `adjDiff` — its adjoint `dᵀ`, edge states → vertex states, the
  divergence: at each vertex, the signed sum of edge values over
  incident edges (sign `+` at the head, `−` at the tail).
* `wDiff` / `wAdjDiff` — the WEIGHTED difference operator
  `D = √W ∘ d` and its adjoint `Dᵀ = dᵀ ∘ √W`, where the root weight
  `√W` multiplies an edge state by `√(w e)`. Then
  `vertexHam = Dᵀ ∘ D` (its energy is AxiomTet's `breakEnergy` — SP-1)
  and `edgeHam = D ∘ Dᵀ` is the partner Hamiltonian on the edge sector.
* `supercharge` — `Q` on the direct sum (vertex ⊕ edge),
  `Q(x, y) = (Dᵀ y, D x)`: it swaps the two sectors (odd under the
  grading) and `Q² = vertexHam ⊕ edgeHam` (SP-0).

**Pins.** SP-0 the supercharge (above). SP-1 both energies are sums of
squares: `⟨f, vertexHam f⟩ = breakEnergy` and
`⟨g, edgeHam g⟩ = ∑_v (Dᵀ g)(v)²`. SP-2 vertex zero modes:
`ker vertexHam` is exactly the per-component constants (consuming
AZ-2W), of dimension the number of connected components. SP-3 edge zero
modes: `ker edgeHam = ker Dᵀ` — the (weighted) circulation space — of
dimension `#edges − #vertices + #components`. SP-4 THE INDEX:
`finrank ker vertexHam + #edges = finrank ker edgeHam + #vertices`,
the Euler characteristic of the web as the difference of the two
sectors' zero-mode counts, stated in addition form so no subtraction
is ever taken. SP-5 (nonzero spectra of the two Hamiltonians coincide
with multiplicities) is the scope's stretch, priced L as its own
brick; it is NOT in this module — K-SP-ISO fires, see the dossier.

**Orientation (K-SP-ORIENT), discharged on the face.** The signed
difference operator needs an orientation; the one used here is induced
by the ambient `LinearOrder V` (every edge points from its smaller
endpoint to its larger). The orientation is fixed explicitly in the
definitions, and everything the pins assert — both energy forms, both
kernels, both dimensions, the index — is proved from the energy forms
and the adjoint identity, which are exactly the quantities that do not
depend on the choice: flipping an edge's orientation negates one row
of `d` and one column of `dᵀ` and leaves every statement below
unchanged in content. The one place the orientation is visible at all
is the entry lemma `adjDiff_single`, and it is stated orientation-
explicitly there.

**Naming fence (from the scope, verbatim in force).** "Supersymmetry"
here is finite SUSY quantum mechanics on a graph — a grading, a
supercharge, two sectors. The edge sector is the partner / odd sector;
calling it "fermionic" is the standard grading analogy and is labeled
as such wherever it appears. No particle-physics claim rides on this
module.

**NO CLAIM** — parts of any official Millennium statement closed by
this module: 0. Dials: 0/4. Cabinet-tier finite brick; no ladder rung
claimed.
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Sqrt
import ThetLogos.AxiomTet

attribute [local instance] Classical.propDecidable

open Finset SimpleGraph

namespace ThetLogos

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)

/-! ## The oriented difference (the signed square root of `diffSq`)

AxiomTet's `diffSq` is the SQUARED break across an unordered edge. The
partner sector needs the signed difference itself. An unordered edge
`s(a, b)` is oriented by the order on `V`: tail `= min a b`, head
`= max a b`. `pairOf` packages the two endpoints as an ordered pair;
it is a legitimate `Sym2` lift because `(min, max)` is symmetric in
the endpoints. -/

/-- The endpoints of an unordered edge, ordered: `(tail, head) =
(min, max)`. Symmetric in the endpoints, hence a `Sym2` lift. -/
noncomputable def pairOf : Sym2 V → V × V :=
  Sym2.lift ⟨fun a b => (min a b, max a b), fun a b => by
    simp only [Prod.mk.injEq]
    exact ⟨min_comm a b, max_comm a b⟩⟩

omit [Fintype V] in
theorem pairOf_mk (a b : V) : pairOf s(a, b) = (min a b, max a b) := by
  simp [pairOf, Sym2.lift_mk]

/-- The signed (oriented) difference of a state across an unordered
edge: `f(head) − f(tail)`. Its square is AxiomTet's `diffSq`. -/
noncomputable def odiff (f : V → ℝ) : Sym2 V → ℝ :=
  fun e => f (pairOf e).2 - f (pairOf e).1

omit [Fintype V] in
theorem odiff_mk (f : V → ℝ) (a b : V) :
    odiff f s(a, b) = f (max a b) - f (min a b) := by
  simp [odiff, pairOf_mk]

omit [Fintype V] in
/-- The signed difference squares to AxiomTet's squared break. -/
theorem odiff_sq (f : V → ℝ) (e : Sym2 V) : (odiff f e) ^ 2 = diffSq f e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [odiff_mk, diffSq_mk]
    rcases le_total a b with h | h
    · rw [max_eq_right h, min_eq_left h]
    · rw [max_eq_left h, min_eq_right h]; ring

omit [Fintype V] in
theorem odiff_add (f g : V → ℝ) (e : Sym2 V) :
    odiff (f + g) e = odiff f e + odiff g e := by
  induction e using Sym2.inductionOn with
  | hf a b => simp [odiff_mk, Pi.add_apply]; ring

omit [Fintype V] in
theorem odiff_smul (r : ℝ) (f : V → ℝ) (e : Sym2 V) :
    odiff (r • f) e = r * odiff f e := by
  induction e using Sym2.inductionOn with
  | hf a b => simp [odiff_mk, Pi.smul_apply, smul_eq_mul]; ring

/-! ## The difference operator and its adjoint

The edge sector is the space of functions on the edge subtype
`↥G.edgeSet`. `diffOp` is `d`; `adjDiff` is `dᵀ`, defined through
`edgeExt`, the extension of an edge state by `0` off the edge set —
so in `adjDiff`'s defining sum over ALL vertices `u`, the non-neighbors
contribute `0` automatically and no adjacency case split is needed in
the definition itself. -/

/-- The difference operator `d`: vertex states → edge states,
`(df)(e) = f(head) − f(tail)`. -/
noncomputable def diffOp : (V → ℝ) →ₗ[ℝ] (↥G.edgeSet → ℝ) where
  toFun f e := odiff f e.1
  map_add' f g := by
    funext e
    exact odiff_add f g e.1
  map_smul' r f := by
    funext e
    simp only [RingHom.id_apply]
    exact odiff_smul r f e.1

omit [Fintype V] in
@[simp]
theorem diffOp_apply (f : V → ℝ) (e : ↥G.edgeSet) :
    diffOp G f e = odiff f e.1 := rfl

/-- Extension of an edge state to all unordered pairs, by `0` off the
edge set. The adjoint's defining sum runs over this extension. -/
noncomputable def edgeExt (g : ↥G.edgeSet → ℝ) : Sym2 V → ℝ :=
  fun e => if h : e ∈ G.edgeSet then g ⟨e, h⟩ else 0

omit [Fintype V] [LinearOrder V] in
theorem edgeExt_of_mem (g : ↥G.edgeSet → ℝ) {e : Sym2 V} (h : e ∈ G.edgeSet) :
    edgeExt G g e = g ⟨e, h⟩ := by simp [edgeExt, h]

omit [Fintype V] [LinearOrder V] in
theorem edgeExt_mk_adj (g : ↥G.edgeSet → ℝ) {u v : V} (h : G.Adj u v) :
    edgeExt G g s(u, v) = g ⟨s(u, v), (mem_edgeSet G).mpr h⟩ :=
  edgeExt_of_mem G g ((mem_edgeSet G).mpr h)

omit [Fintype V] [LinearOrder V] in
theorem edgeExt_not_mem (g : ↥G.edgeSet → ℝ) {e : Sym2 V} (h : e ∉ G.edgeSet) :
    edgeExt G g e = 0 := by simp [edgeExt, h]

/-- The adjoint `dᵀ` of the difference operator: edge states → vertex
states, the divergence. At vertex `v` it sums, over every `u`, the
edge value on `s(u, v)` with sign `+1` if `u < v` (so `v` is the head
of the edge) and `−1` if `u > v` (`v` is the tail); non-edges and the
diagonal contribute `0` through `edgeExt`. -/
noncomputable def adjDiff : (↥G.edgeSet → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun g v := ∑ u : V, (if u < v then (1 : ℝ) else -1) * edgeExt G g s(u, v)
  map_add' g₁ g₂ := by
    funext v
    simp only [Pi.add_apply]
    have hpt : ∀ u : V, (if u < v then (1 : ℝ) else -1) * edgeExt G (g₁ + g₂) s(u, v)
        = (if u < v then (1 : ℝ) else -1) * edgeExt G g₁ s(u, v)
          + (if u < v then (1 : ℝ) else -1) * edgeExt G g₂ s(u, v) := by
      intro u
      by_cases h : s(u, v) ∈ G.edgeSet
      · rw [edgeExt_of_mem G _ h, edgeExt_of_mem G _ h, edgeExt_of_mem G _ h]
        simp [Pi.add_apply, mul_add]
      · rw [edgeExt_not_mem G _ h, edgeExt_not_mem G _ h, edgeExt_not_mem G _ h]
        simp
    rw [Finset.sum_congr rfl (fun u _ => hpt u), Finset.sum_add_distrib]
  map_smul' r g := by
    funext v
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : s(u, v) ∈ G.edgeSet
    · rw [edgeExt_of_mem G _ h, edgeExt_of_mem G _ h]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [edgeExt_not_mem G _ h, edgeExt_not_mem G _ h]
      simp

@[simp]
theorem adjDiff_apply (g : ↥G.edgeSet → ℝ) (v : V) :
    adjDiff G g v = ∑ u : V, (if u < v then (1 : ℝ) else -1) * edgeExt G g s(u, v) := rfl

/-! ## The root weight and the weighted operators

The need weights `w` enter through their square roots: the weighted
difference operator is `D = √W ∘ d`, so that `Dᵀ D` has energy
`∑ w_e (df)(e)²` — AxiomTet's `breakEnergy`. Positivity of `w` on
edges (AxiomTet's standing hypothesis shape) makes `√W` a linear
equivalence of the edge sector. -/

variable (w : Sym2 V → ℝ)

/-- The root weight: `√(w e)` on each edge. -/
noncomputable def rootWeight (e : ↥G.edgeSet) : ℝ := Real.sqrt (w e.1)

omit [Fintype V] [LinearOrder V] in
theorem rootWeight_pos (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (e : ↥G.edgeSet) :
    0 < rootWeight G w e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v =>
    exact Real.sqrt_pos.mpr (hw u v ((mem_edgeSet G).mp he))

omit [Fintype V] [LinearOrder V] in
theorem rootWeight_sq (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (e : ↥G.edgeSet) :
    (rootWeight G w e) ^ 2 = w e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v =>
    exact Real.sq_sqrt (hw u v ((mem_edgeSet G).mp he)).le

omit [Fintype V] [LinearOrder V] in
theorem rootWeight_ne_zero (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (e : ↥G.edgeSet) :
    rootWeight G w e ≠ 0 :=
  (rootWeight_pos G w hw e).ne'

/-- Multiplication of an edge state by a fixed edge function, as a
linear map of the edge sector. -/
noncomputable def mulEdgeLin (c : ↥G.edgeSet → ℝ) :
    (↥G.edgeSet → ℝ) →ₗ[ℝ] (↥G.edgeSet → ℝ) where
  toFun g e := c e * g e
  map_add' g₁ g₂ := by
    funext e
    simp [Pi.add_apply, mul_add]
  map_smul' r g := by
    funext e
    simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

omit [Fintype V] [LinearOrder V] in
@[simp]
theorem mulEdgeLin_apply (c g : ↥G.edgeSet → ℝ) (e : ↥G.edgeSet) :
    mulEdgeLin G c g e = c e * g e := rfl

/-- Under positive need weights, multiplication by the root weight
`√W` is a linear EQUIVALENCE of the edge sector (inverse: multiply
by `1/√W`). -/
noncomputable def wMulEquiv (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    (↥G.edgeSet → ℝ) ≃ₗ[ℝ] (↥G.edgeSet → ℝ) :=
  LinearEquiv.ofLinearMap
    (mulEdgeLin G (rootWeight G w))
    (mulEdgeLin G (fun e => (rootWeight G w e)⁻¹))
    (by
      ext g e
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mulEdgeLin_apply]
      rw [← mul_assoc, mul_inv_cancel₀ (rootWeight_ne_zero G w hw e), one_mul])
    (by
      ext g e
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mulEdgeLin_apply]
      rw [← mul_assoc, inv_mul_cancel₀ (rootWeight_ne_zero G w hw e), one_mul])

/-- The weighted difference operator `D = √W ∘ d`. -/
noncomputable def wDiff : (V → ℝ) →ₗ[ℝ] (↥G.edgeSet → ℝ) :=
  (mulEdgeLin G (rootWeight G w)).comp (diffOp G)

omit [Fintype V] in
@[simp]
theorem wDiff_apply (f : V → ℝ) (e : ↥G.edgeSet) :
    wDiff G w f e = rootWeight G w e * odiff f e.1 := rfl

/-- The adjoint of the weighted difference operator, `Dᵀ = dᵀ ∘ √W`. -/
noncomputable def wAdjDiff : (↥G.edgeSet → ℝ) →ₗ[ℝ] (V → ℝ) :=
  (adjDiff G).comp (mulEdgeLin G (rootWeight G w))

/-! ## The two Hamiltonians and the supercharge (SP-0) -/

/-- The VERTEX Hamiltonian `H_v = Dᵀ ∘ D`. Its energy form is
AxiomTet's `breakEnergy` (SP-1, proved below). -/
noncomputable def vertexHam : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  (wAdjDiff G w).comp (wDiff G w)

/-- The EDGE Hamiltonian `H_e = D ∘ Dᵀ`, the partner of `vertexHam`. -/
noncomputable def edgeHam : (↥G.edgeSet → ℝ) →ₗ[ℝ] (↥G.edgeSet → ℝ) :=
  (wDiff G w).comp (wAdjDiff G w)

/-- The SUPERCHARGE `Q` on the direct sum (vertex ⊕ edge):
`Q(x, y) = (Dᵀ y, D x)`. It swaps the two sectors — the odd operator
of the grading — and its square is `vertexHam ⊕ edgeHam` (SP-0). -/
noncomputable def supercharge :
    ((V → ℝ) × (↥G.edgeSet → ℝ)) →ₗ[ℝ] ((V → ℝ) × (↥G.edgeSet → ℝ)) where
  toFun z := (wAdjDiff G w z.2, wDiff G w z.1)
  map_add' z₁ z₂ := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk]

@[simp]
theorem supercharge_apply (z : (V → ℝ) × (↥G.edgeSet → ℝ)) :
    supercharge G w z = (wAdjDiff G w z.2, wDiff G w z.1) := rfl

/-- SP-0, oddness at the vertex sector: `Q` sends a pure vertex state
to a pure edge state, `(0, D x)`. -/
theorem supercharge_fst (x : V → ℝ) :
    supercharge G w (x, 0) = (0, wDiff G w x) := by
  simp [map_zero]

/-- SP-0, oddness at the edge sector: `Q` sends a pure edge state to
a pure vertex state, `(Dᵀ y, 0)`. -/
theorem supercharge_snd (y : ↥G.edgeSet → ℝ) :
    supercharge G w (0, y) = (wAdjDiff G w y, 0) := by
  simp [map_zero]

/-- **SP-0 (the supercharge squares to the two Hamiltonians).**
`Q (Q z) = (vertexHam z.1, edgeHam z.2)` for every `z` of the direct
sum: one odd operator, both Hamiltonians as its square. -/
theorem supercharge_sq (z : (V → ℝ) × (↥G.edgeSet → ℝ)) :
    supercharge G w (supercharge G w z)
      = (vertexHam G w z.1, edgeHam G w z.2) := rfl

/-! ## The adjoint identity

The one analytic fact of the brick: `adjDiff` is the adjoint of
`diffOp` for the two counting pairings. Both sides are computed into
the common "ordered-edge" sum over
`S = {(a, b) : a < b, a ~ b}` — the vertex side by splitting the
ordered-pair sum into its `a < b` and `b < a` halves (the second half
reindexed by the swap), the edge side by reindexing edges by their
ordered endpoints. Everything downstream (SP-1, SP-2, SP-3) is
bookkeeping on top of this identity and AZ-2W. -/

omit [Fintype V] in
/-- Reconstruction: an unordered edge is the unordered pair of its
own ordered endpoints. -/
theorem pairOf_fst_snd (e : Sym2 V) : s((pairOf e).1, (pairOf e).2) = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [pairOf_mk]
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact Sym2.eq_swap

/-- The vertex side of the adjoint identity, computed into the
ordered-edge sum: summing `f · (dᵀh)` over vertices equals summing
`(f(head) − f(tail)) · h` over ordered edges. -/
theorem sum_adjDiff_eq (f : V → ℝ) (h : ↥G.edgeSet → ℝ) :
    ∑ v, f v * adjDiff G h v
      = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2),
          (f p.2 - f p.1) * edgeExt G h s(p.1, p.2) := by
  set A : Finset (V × V) :=
    Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2) with hA
  set B : Finset (V × V) :=
    Finset.univ.filter (fun p : V × V => p.2 < p.1 ∧ G.Adj p.1 p.2) with hB
  set T : V × V → ℝ := fun p =>
    f p.2 * ((if p.1 < p.2 then (1 : ℝ) else -1) * edgeExt G h s(p.1, p.2)) with hT
  have h1 : ∀ v : V, f v * adjDiff G h v
      = ∑ u, f v * ((if u < v then (1 : ℝ) else -1) * edgeExt G h s(u, v)) := by
    intro v
    rw [adjDiff_apply, Finset.mul_sum]
  have h2 : ∑ p : V × V, T p = ∑ p ∈ A ∪ B, T p := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    by_cases hadj : G.Adj p.1 p.2
    · exfalso
      apply hp
      rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
      · exact Finset.mem_union_left B (by rw [hA]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hlt, hadj⟩)
      · exact absurd heq (hadj.ne)
      · exact Finset.mem_union_right A (by rw [hB]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hgt, hadj⟩)
    · have hnot : s(p.1, p.2) ∉ G.edgeSet := by
        rw [mem_edgeSet]
        exact hadj
      simp [hT, edgeExt_not_mem G h hnot]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    rw [hA, Finset.mem_filter] at hpA
    rw [hB, Finset.mem_filter] at hpB
    exact absurd hpB.2.1 (not_lt_of_gt hpA.2.1)
  have hA' : ∑ p ∈ A, T p = ∑ p ∈ A, f p.2 * edgeExt G h s(p.1, p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    simp only [hT, ite_eq_left hp.2.1, one_mul]
  have hB' : ∑ p ∈ B, T p = ∑ p ∈ A, -(f p.1 * edgeExt G h s(p.1, p.2)) := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [hB, Finset.mem_filter] at hp
      rw [hA]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2.1, hp.2.2.symm⟩
    · intro p _ q _ hpq
      rw [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 hpq.1
    · intro q hq
      rw [hA, Finset.mem_filter] at hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [hB]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq.2.1, hq.2.2.symm⟩
    · intro p hp
      rw [hB, Finset.mem_filter] at hp
      have hcoeff : (if p.1 < p.2 then (1 : ℝ) else -1) = -1 := by
        simp [not_lt_of_gt hp.2.1]
      simp only [hT]
      rw [hcoeff]
      have hswap : edgeExt G h s(p.1, p.2) = edgeExt G h s(p.2, p.1) := by
        rw [Sym2.eq_swap]
      rw [hswap]
      ring
  calc ∑ v, f v * adjDiff G h v
      = ∑ v, ∑ u, f v * ((if u < v then (1 : ℝ) else -1) * edgeExt G h s(u, v)) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ u, ∑ v, f v * ((if u < v then (1 : ℝ) else -1) * edgeExt G h s(u, v)) :=
        Finset.sum_comm
    _ = ∑ p : V × V, T p := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ A ∪ B, T p := h2
    _ = ∑ p ∈ A, T p + ∑ p ∈ B, T p := Finset.sum_union hdisj
    _ = ∑ p ∈ A, (f p.2 - f p.1) * edgeExt G h s(p.1, p.2) := by
        rw [hA', hB', ← Finset.sum_add_distrib, hA]
        exact Finset.sum_congr rfl (fun p _ => by ring)

/-- The edge side of the adjoint identity, computed into the same
ordered-edge sum: summing `(df) · h` over the edge finset equals
summing `(f(head) − f(tail)) · h` over ordered edges. -/
theorem sum_odiff_edgeFinset_eq (f : V → ℝ) (h : ↥G.edgeSet → ℝ) :
    ∑ e ∈ G.edgeFinset, odiff f e * edgeExt G h e
      = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2),
          (f p.2 - f p.1) * edgeExt G h s(p.1, p.2) := by
  refine Finset.sum_bij (fun e _ => pairOf e) ?_ ?_ ?_ ?_
  · intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [pairOf_mk]
      rw [SimpleGraph.mem_edgeFinset, mem_edgeSet] at he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases lt_trichotomy a b with hlt | heq | hgt
        · rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact hlt
        · exact absurd heq he.ne
        · rw [min_eq_right hgt.le, max_eq_left hgt.le]; exact hgt
      · rcases le_total a b with hle | hle
        · rwa [min_eq_left hle, max_eq_right hle]
        · rw [min_eq_right hle, max_eq_left hle]; exact he.symm
  · intro e₁ _ e₂ _ hp
    have h1 := pairOf_fst_snd e₁
    have h2 := pairOf_fst_snd e₂
    rw [← h1, ← h2, hp]
  · intro p hp
    rw [Finset.mem_filter] at hp
    refine ⟨s(p.1, p.2), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, mem_edgeSet]
      exact hp.2.2
    · rw [pairOf_mk, min_eq_left hp.2.1.le, max_eq_right hp.2.1.le]
  · intro e _
    simp only [odiff, pairOf_fst_snd]

/-- **The adjoint identity.** `adjDiff` is the adjoint of `diffOp`
for the counting pairings:
`∑_e (df)(e) · h(e) = ∑_v f(v) · (dᵀh)(v)`, the edge sum taken over
the edge finset through `edgeExt`. -/
theorem adjoint_identity (f : V → ℝ) (h : ↥G.edgeSet → ℝ) :
    ∑ e ∈ G.edgeFinset, odiff f e * edgeExt G h e
      = ∑ v, f v * adjDiff G h v :=
  (sum_odiff_edgeFinset_eq G f h).trans (sum_adjDiff_eq G f h).symm



/-! ## SP-1: both energies are sums of squares

The vertex energy of `vertexHam` is AxiomTet's `breakEnergy` — the
square `dᵀ W d`, consumed, not re-proved. The edge energy of
`edgeHam` is the sum of squares of `Dᵀ g`. Both are the adjoint
identity read at `h = D f` resp. `f = Dᵀ g`. -/

omit [Fintype V] [LinearOrder V] in
/-- `edgeExt` at a genuine edge is the edge state's own value. -/
theorem edgeExt_coe (g : ↥G.edgeSet → ℝ) (e : ↥G.edgeSet) :
    edgeExt G g e.1 = g e :=
  edgeExt_of_mem G g e.2

theorem wAdjDiff_apply (g : ↥G.edgeSet → ℝ) (v : V) :
    wAdjDiff G w g v = adjDiff G (mulEdgeLin G (rootWeight G w) g) v := rfl

theorem vertexHam_apply (f : V → ℝ) (v : V) :
    vertexHam G w f v
      = adjDiff G (mulEdgeLin G (rootWeight G w) (wDiff G w f)) v := rfl

theorem edgeHam_apply (g : ↥G.edgeSet → ℝ) (e : ↥G.edgeSet) :
    edgeHam G w g e = wDiff G w (wAdjDiff G w g) e := rfl

omit [Fintype V] in
/-- One edge-term of the vertex energy: `odiff · (√W · (√W · odiff))`
is `w · diffSq` — the root weight squares back to the need weight
and the signed difference squares to AxiomTet's squared break. -/
theorem vertex_energy_term (hw : ∀ u v, G.Adj u v → 0 < w s(u, v))
    (f : V → ℝ) (e : ↥G.edgeSet) :
    odiff f e.1 * edgeExt G (mulEdgeLin G (rootWeight G w) (wDiff G w f)) e.1
      = w e.1 * diffSq f e.1 := by
  rw [edgeExt_coe, mulEdgeLin_apply, wDiff_apply,
    ← rootWeight_sq G w hw e, ← odiff_sq]
  ring

/-- **SP-1, vertex side.** The energy of the vertex Hamiltonian is
the break energy: `∑_v f(v) · (H_v f)(v) = breakEnergy G w f`. -/
theorem vertex_energy (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (f : V → ℝ) :
    ∑ v, f v * vertexHam G w f v = breakEnergy G w f := by
  have h1 : ∑ v, f v * vertexHam G w f v
      = ∑ e ∈ G.edgeFinset,
          odiff f e * edgeExt G (mulEdgeLin G (rootWeight G w) (wDiff G w f)) e := by
    exact (Finset.sum_congr rfl (fun v _ => by rw [vertexHam_apply])).trans
      (adjoint_identity G f _).symm
  rw [h1]
  show ∑ e ∈ G.edgeFinset, odiff f e
      * edgeExt G (mulEdgeLin G (rootWeight G w) (wDiff G w f)) e
    = ∑ e ∈ G.edgeFinset, w e * diffSq f e
  exact Finset.sum_congr rfl
    (fun e he => vertex_energy_term G w hw f ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩)

/-- One edge-term of the edge energy, rearranged into adjoint
identity form. -/
theorem edge_energy_term (g : ↥G.edgeSet → ℝ) (e : ↥G.edgeSet) :
    edgeExt G g e.1 * edgeExt G (edgeHam G w g) e.1
      = odiff (wAdjDiff G w g) e.1
        * edgeExt G (mulEdgeLin G (rootWeight G w) g) e.1 := by
  rw [edgeExt_coe, edgeExt_coe, edgeExt_coe, edgeHam_apply, wDiff_apply,
    mulEdgeLin_apply]
  ring

/-- **SP-1, edge side.** The energy of the edge Hamiltonian is a sum
of squares of the adjoint: `∑_e g(e) · (H_e g)(e) = ∑_v (Dᵀ g)(v)²`,
the edge sum taken over the edge finset through `edgeExt`. -/
theorem edge_energy (g : ↥G.edgeSet → ℝ) :
    ∑ e ∈ G.edgeFinset, edgeExt G g e * edgeExt G (edgeHam G w g) e
      = ∑ v, (wAdjDiff G w g v) ^ 2 := by
  have step1 : ∑ e ∈ G.edgeFinset, edgeExt G g e * edgeExt G (edgeHam G w g) e
      = ∑ e ∈ G.edgeFinset, odiff (wAdjDiff G w g) e
          * edgeExt G (mulEdgeLin G (rootWeight G w) g) e :=
    Finset.sum_congr rfl
      (fun e he => edge_energy_term G w g ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩)
  rw [step1, adjoint_identity]
  exact Finset.sum_congr rfl (fun v _ => by rw [wAdjDiff_apply, pow_two])


/-! ## SP-2 and SP-3: the two kernels

The vertex kernel is the per-component constants (AZ-2W read through
the energy identity). The edge kernel is the circulation space. The
component count is the dimension of the vertex kernel, via the
evaluation map from functions on `G.ConnectedComponent`. -/

/-- The per-component constants: states agreeing on every reachable
pair. One free value per connected component. -/
def perCompSubmodule : Submodule ℝ (V → ℝ) where
  carrier := {f | ∀ u v, G.Reachable u v → f u = f v}
  add_mem' := fun hf hg u v h => by simp only [Pi.add_apply, hf u v h, hg u v h]
  zero_mem' := fun u v _ => rfl
  smul_mem' := fun r _ hf u v h => by simp only [Pi.smul_apply, hf u v h]

omit [Fintype V] [LinearOrder V] in
theorem perCompSubmodule_mem {f : V → ℝ} :
    f ∈ perCompSubmodule G ↔ ∀ u v, G.Reachable u v → f u = f v :=
  Iff.rfl

omit [Fintype V] in
/-- The kernel of the weighted difference operator is the
per-component constants: `D f = 0` iff `f` agrees across every edge
(the root weight is positive there), iff it agrees on every
reachable pair (AZ-1's walk propagation). -/
theorem ker_wDiff_eq (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    (wDiff G w).ker = perCompSubmodule G := by
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    rw [perCompSubmodule_mem]
    intro u v huv
    obtain ⟨p⟩ := huv
    apply eq_of_walk G _ p
    intro a b hab
    have hD : wDiff G w f ⟨s(a, b), (mem_edgeSet G).mpr hab⟩ = 0 := by
      rw [hf]; rfl
    rw [wDiff_apply] at hD
    have hodd : odiff f s(a, b) = 0 :=
      (mul_eq_zero.mp hD).resolve_left (rootWeight_ne_zero G w hw _)
    rw [odiff_mk] at hodd
    rcases le_total a b with hle | hle
    · rw [max_eq_right hle, min_eq_left hle] at hodd
      exact (sub_eq_zero.mp hodd).symm
    · rw [max_eq_left hle, min_eq_right hle] at hodd
      exact sub_eq_zero.mp hodd
  · intro f hf
    rw [perCompSubmodule_mem] at hf
    rw [LinearMap.mem_ker]
    funext e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [wDiff_apply]
      have hab : f a = f b :=
        hf a b ((mem_edgeSet G).mp he).reachable
      rw [odiff_mk]
      rcases le_total a b with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, ← hab]
        simp
      · rw [max_eq_left hle, min_eq_right hle, ← hab]
        simp

/-- **SP-2 (vertex zero modes).** The kernel of the vertex
Hamiltonian is exactly the per-component constants: `H_v f = 0`
forces `breakEnergy = 0` (SP-1), and AZ-2W's per-component form
finishes; conversely a per-component constant is killed by `D`,
hence by `H_v = Dᵀ D`. -/
theorem ker_vertexHam_eq (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    (vertexHam G w).ker = perCompSubmodule G := by
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have h2 : breakEnergy G w f = 0 := by
      have hsum : (∑ v, f v * vertexHam G w f v) = 0 := by simp [hf]
      rwa [vertex_energy G w hw f] at hsum
    rw [perCompSubmodule_mem]
    exact (breakEnergy_eq_zero_iff_forall_reachable G hw f).mp h2
  · intro f hf
    have hD : wDiff G w f = 0 := by
      have hmem : f ∈ (wDiff G w).ker := by
        rwa [ker_wDiff_eq G w hw]
      exact LinearMap.mem_ker.mp hmem
    rw [LinearMap.mem_ker]
    funext v
    rw [vertexHam_apply, hD]
    simp [edgeExt]

/-- Evaluation at vertices descends to components: the linear map
from functions on the component type to vertex states. -/
noncomputable def perCompMap : (G.ConnectedComponent → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun h v := h (G.connectedComponentMk v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] [LinearOrder V] in
theorem perCompMap_apply (h : G.ConnectedComponent → ℝ) (v : V) :
    perCompMap G h v = h (G.connectedComponentMk v) := rfl

omit [Fintype V] [LinearOrder V] in
theorem range_perCompMap : (perCompMap G).range = perCompSubmodule G := by
  apply le_antisymm
  · rintro f ⟨h, rfl⟩
    rw [perCompSubmodule_mem]
    intro u v huv
    show h (G.connectedComponentMk u) = h (G.connectedComponentMk v)
    have hmk : G.connectedComponentMk u = G.connectedComponentMk v :=
      Quot.sound huv
    rw [hmk]
  · intro f hf
    rw [perCompSubmodule_mem] at hf
    refine ⟨Quot.lift f (fun a b hab => hf a b hab), ?_⟩
    funext v
    rfl

omit [Fintype V] [LinearOrder V] in
theorem perCompMap_injective : Function.Injective (perCompMap G) := by
  intro h₁ h₂ hh
  funext c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    have hcongr := congrFun hh v
    rwa [perCompMap_apply, perCompMap_apply] at hcongr

omit [LinearOrder V] in
/-- The dimension of the per-component constants is the number of
connected components. -/
theorem finrank_perComp :
    Module.finrank ℝ ↥(perCompSubmodule G) = Nat.card G.ConnectedComponent := by
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [← range_perCompMap,
    LinearMap.finrank_range_of_inj (perCompMap_injective G), Module.finrank_pi,
    Nat.card_eq_fintype_card]

/-- **SP-2, dimension form.** `finrank ker H_v = #components`. -/
theorem finrank_ker_vertexHam (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(vertexHam G w).ker = Nat.card G.ConnectedComponent := by
  rw [ker_vertexHam_eq G w hw]
  exact finrank_perComp G

omit [Fintype V] [LinearOrder V] in
/-- `edgeExt` of the zero edge state is zero. -/
theorem edgeExt_zero {e : Sym2 V} : edgeExt G (0 : ↥G.edgeSet → ℝ) e = 0 := by
  by_cases h : e ∈ G.edgeSet <;> simp [edgeExt, h]

/-- **SP-3, kernel form.** The kernel of the edge Hamiltonian is the
kernel of `Dᵀ`: `H_e g = 0` iff the weighted circulation `Dᵀ g`
vanishes — one inclusion by the edge energy (SP-1), the other
because `H_e = D ∘ Dᵀ`. -/
theorem ker_edgeHam_eq : (edgeHam G w).ker = (wAdjDiff G w).ker := by
  apply le_antisymm
  · intro g hg
    rw [LinearMap.mem_ker] at hg
    have hE : ∑ v, (wAdjDiff G w g v) ^ 2 = 0 := by
      rw [← edge_energy G w g]
      apply Finset.sum_eq_zero
      intro e _
      rw [hg]
      simp [edgeExt]
    have hterm : ∀ v, (wAdjDiff G w g v) ^ 2 = 0 :=
      fun v => (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg _)).mp hE v
        (Finset.mem_univ v)
    rw [LinearMap.mem_ker]
    funext v
    have hv := hterm v
    rwa [sq_eq_zero_iff] at hv
  · intro g hg
    rw [LinearMap.mem_ker] at hg ⊢
    have hcomp : edgeHam G w g = wDiff G w (wAdjDiff G w g) := rfl
    rw [hcomp, hg]
    exact map_zero _

/-- The circulation characterization: an edge state lies in
`ker Dᵀ` iff the weighted flow `√W • g` is divergence-free — at
every vertex, the signed sum of incident edge values vanishes. -/
theorem ker_wAdjDiff_iff (g : ↥G.edgeSet → ℝ) :
    g ∈ (wAdjDiff G w).ker
      ↔ ∀ v, ∑ u, (if u < v then (1 : ℝ) else -1)
          * edgeExt G (mulEdgeLin G (rootWeight G w) g) s(u, v) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hh v
    have := congrFun hh v
    rwa [wAdjDiff_apply, adjDiff_apply] at this
  · intro hh
    funext v
    rw [wAdjDiff_apply, adjDiff_apply]
    exact hh v


/-! ## SP-3 dimension and SP-4: the index

The rank of `adjDiff` equals the rank of `diffOp` — through the
matrix of the operator: the matrix of `adjDiff` is the transpose of
the matrix of `diffOp` (the entry lemma `adjDiff_single`), and a
matrix and its transpose have the same rank. Rank-nullity on both
operators then gives the two dimension formulas by arithmetic. -/

/-- The entry lemma: `adjDiff` on a single edge state. The sum over
all vertices collapses to the one incident pair; the value is the
oriented incidence entry — `+1` at the head, `−1` at the tail, `0`
elsewhere — which is exactly the `diffOp` entry of the transposed
seat. (Orientation-explicit, as fenced in the header.) -/
theorem adjDiff_single (e : ↥G.edgeSet) (v : V) :
    adjDiff G (Pi.single e 1) v = odiff (Pi.single v 1) e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : G.Adj a b := (mem_edgeSet G).mp he
    have hne : a ≠ b := hab.ne
    show adjDiff G (Pi.single ⟨s(a, b), he⟩ 1) v = odiff (Pi.single v 1) s(a, b)
    rw [adjDiff_apply, odiff_mk]
    by_cases hva : v = a
    · subst hva
      rw [Finset.sum_eq_single b]
      · have hsub : (⟨s(b, v), (mem_edgeSet G).mpr hab.symm⟩ : ↥G.edgeSet)
            = ⟨s(v, b), he⟩ :=
          Subtype.ext Sym2.eq_swap
        rw [edgeExt_mk_adj G _ hab.symm, hsub, Pi.single_eq_same]
        rcases lt_trichotomy v b with hlt | heq | hgt
        · rw [ite_eq_right (not_lt_of_gt hlt), max_eq_right hlt.le, min_eq_left hlt.le,
            Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same]
          norm_num
        · exact absurd heq hne
        · rw [ite_eq_left hgt, max_eq_left hgt.le, min_eq_right hgt.le,
            Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)]
          norm_num
      · intro u _ hub
        by_cases hu : s(u, v) ∈ G.edgeSet
        · rw [edgeExt_of_mem G _ hu, Pi.single_eq_of_ne]
          · simp
          · intro hsub
            have hSym : s(v, b) = s(u, v) := congrArg Subtype.val hsub.symm
            have hmem : b ∈ s(u, v) :=
              hSym ▸ (by rw [Sym2.mem_iff]; exact Or.inr rfl)
            rw [Sym2.mem_iff] at hmem
            rcases hmem with h | h
            · exact hub h.symm
            · exact hne h.symm
        · rw [edgeExt_not_mem G _ hu]; simp
      · simp
    · by_cases hvb : v = b
      · subst hvb
        rw [Finset.sum_eq_single a]
        · have hsub : (⟨s(a, v), (mem_edgeSet G).mpr hab⟩ : ↥G.edgeSet)
              = ⟨s(a, v), he⟩ :=
            Subtype.ext rfl
          rw [edgeExt_mk_adj G _ hab, hsub, Pi.single_eq_same]
          rcases lt_trichotomy a v with hlt | heq | hgt
          · rw [ite_eq_left hlt, max_eq_right hlt.le, min_eq_left hlt.le,
              Pi.single_eq_same, Pi.single_eq_of_ne hne]
            norm_num
          · exact absurd heq hne
          · rw [ite_eq_right (not_lt_of_gt hgt), max_eq_left hgt.le, min_eq_right hgt.le,
              Pi.single_eq_of_ne hne, Pi.single_eq_same]
            norm_num
        · intro u _ hua
          by_cases hu : s(u, v) ∈ G.edgeSet
          · rw [edgeExt_of_mem G _ hu, Pi.single_eq_of_ne]
            · simp
            · intro hsub
              have hSym : s(a, v) = s(u, v) := congrArg Subtype.val hsub.symm
              have hmem : a ∈ s(u, v) :=
                hSym ▸ (by rw [Sym2.mem_iff]; exact Or.inl rfl)
              rw [Sym2.mem_iff] at hmem
              rcases hmem with h | h
              · exact hua h.symm
              · exact hne h
          · rw [edgeExt_not_mem G _ hu]; simp
        · simp
      · have hmax : (Pi.single v (1 : ℝ) : V → ℝ) (max a b) = 0 := by
          apply Pi.single_eq_of_ne
          rcases le_total a b with hle | hle
          · rw [max_eq_right hle]; exact fun hh => hvb hh.symm
          · rw [max_eq_left hle]; exact fun hh => hva hh.symm
        have hmin : (Pi.single v (1 : ℝ) : V → ℝ) (min a b) = 0 := by
          apply Pi.single_eq_of_ne
          rcases le_total a b with hle | hle
          · rw [min_eq_left hle]; exact fun hh => hva hh.symm
          · rw [min_eq_right hle]; exact fun hh => hvb hh.symm
        calc (∑ x, (if x < v then (1 : ℝ) else -1)
                * edgeExt G (Pi.single ⟨s(a, b), he⟩ 1) s(x, v)) = 0 := by
              apply Finset.sum_eq_zero
              intro u _
              by_cases hu : s(u, v) ∈ G.edgeSet
              · rw [edgeExt_of_mem G _ hu, Pi.single_eq_of_ne]
                · simp
                · intro hsub
                  have hSym : s(u, v) = s(a, b) := congrArg Subtype.val hsub
                  have hmem : v ∈ s(a, b) :=
                    hSym ▸ (by rw [Sym2.mem_iff]; exact Or.inr rfl)
                  rw [Sym2.mem_iff] at hmem
                  rcases hmem with h | h
                  · exact hva h
                  · exact hvb h
              · rw [edgeExt_not_mem G _ hu]; simp
          _ = (Pi.single v (1 : ℝ) : V → ℝ) (max a b)
              - (Pi.single v (1 : ℝ) : V → ℝ) (min a b) := by
              rw [hmax, hmin, sub_zero]

/-- The rank of a pi-type operator is the rank of its matrix. -/
theorem finrank_range_eq_rank {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Module.finrank ℝ ↥f.range = (LinearMap.toMatrix' f).rank := by
  show Module.finrank ℝ ↥f.range
    = Module.finrank ℝ ↥(LinearMap.range (LinearMap.toMatrix' f).mulVecLin)
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

/-- The matrix of `diffOp` is the transpose of the matrix of
`adjDiff` — entrywise, this is `adjDiff_single`. -/
theorem toMatrix'_diffOp :
    LinearMap.toMatrix' (diffOp G)
      = Matrix.transpose (LinearMap.toMatrix' (adjDiff G)) := by
  apply Matrix.ext
  intro e v
  rw [Matrix.transpose_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply,
    diffOp_apply]
  exact (adjDiff_single G e v).symm

/-- Rank of the adjoint equals rank of the operator. -/
theorem finrank_range_adjDiff :
    Module.finrank ℝ ↥(adjDiff G).range = Module.finrank ℝ ↥(diffOp G).range := by
  rw [finrank_range_eq_rank, finrank_range_eq_rank, toMatrix'_diffOp,
    Matrix.rank_transpose]

/-- The range of `Dᵀ = dᵀ ∘ √W` is the range of `dᵀ`: the root
weight is surjective on the edge sector. -/
theorem range_wAdjDiff (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    (wAdjDiff G w).range = (adjDiff G).range := by
  have hS : Function.Surjective (mulEdgeLin G (rootWeight G w)) := by
    intro g
    refine ⟨fun e => (rootWeight G w e)⁻¹ * g e, ?_⟩
    funext e
    rw [mulEdgeLin_apply, ← mul_assoc, mul_inv_cancel₀ (rootWeight_ne_zero G w hw e),
      one_mul]
  have htop : (mulEdgeLin G (rootWeight G w)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hS
  rw [wAdjDiff, LinearMap.range_comp, htop]
  exact (LinearMap.range_eq_map _).symm

/-- The rank of `D = √W ∘ d` is the rank of `d`: post-composition
with the root-weight equivalence moves the range by an equivalence,
which preserves finrank. -/
theorem finrank_range_wDiff (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(wDiff G w).range = Module.finrank ℝ ↥(diffOp G).range := by
  have h : (wDiff G w).range
      = ((diffOp G).range).map (mulEdgeLin G (rootWeight G w)) := by
    rw [wDiff, LinearMap.range_comp]
  rw [h]
  exact LinearEquiv.finrank_map_eq (wMulEquiv G w hw) _

/-- Rank of `Dᵀ` equals rank of `D`. -/
theorem finrank_range_wAdjDiff (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(wAdjDiff G w).range = Module.finrank ℝ ↥(wDiff G w).range := by
  rw [range_wAdjDiff G w hw, finrank_range_adjDiff]
  exact (finrank_range_wDiff G w hw).symm

/-- **SP-3, dimension form.** `finrank ker H_e + #vertices
= #edges + #components` — the edge zero modes are counted by the
cyclomatic formula. -/
theorem finrank_ker_edgeHam_add (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(edgeHam G w).ker + Fintype.card V
      = #G.edgeFinset + Nat.card G.ConnectedComponent := by
  have hker : Module.finrank ℝ ↥(edgeHam G w).ker
      = Module.finrank ℝ ↥(wAdjDiff G w).ker := by
    rw [ker_edgeHam_eq]
  have hD : Module.finrank ℝ ↥(wDiff G w).range
      + Module.finrank ℝ ↥(wDiff G w).ker = Fintype.card V := by
    have h := LinearMap.finrank_range_add_finrank_ker (wDiff G w)
    rwa [Module.finrank_pi] at h
  have hDT : Module.finrank ℝ ↥(wAdjDiff G w).range
      + Module.finrank ℝ ↥(wAdjDiff G w).ker = #G.edgeFinset := by
    have h := LinearMap.finrank_range_add_finrank_ker (wAdjDiff G w)
    rwa [Module.finrank_pi, ← SimpleGraph.edgeFinset_card] at h
  have hcomp : Module.finrank ℝ ↥(wDiff G w).ker
      = Nat.card G.ConnectedComponent := by
    rw [ker_wDiff_eq G w hw]
    exact finrank_perComp G
  have hr : Module.finrank ℝ ↥(wAdjDiff G w).range
      = Module.finrank ℝ ↥(wDiff G w).range :=
    finrank_range_wAdjDiff G w hw
  omega

/-- **SP-4 (THE INDEX).** For every finite web with positive need
weights,
`finrank ker H_v + #edges = finrank ker H_e + #vertices`:
the difference of the two sectors' zero-mode counts is the Euler
characteristic `#vertices − #edges`, stated in addition form. -/
theorem index_eq (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(vertexHam G w).ker + #G.edgeFinset
      = Module.finrank ℝ ↥(edgeHam G w).ker + Fintype.card V := by
  have h1 := finrank_ker_edgeHam_add G w hw
  have h2 : Module.finrank ℝ ↥(vertexHam G w).ker
      = Nat.card G.ConnectedComponent :=
    finrank_ker_vertexHam G w hw
  omega


end ThetLogos
