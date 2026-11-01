/-
# ThetLogos.IcosidodecaChain — PHI-C0: the icosidodecahedron chain model (combinatorics only)

**NO CLAIM. Salvage label (per scoping memo
`routeb-general-scratch/scoping-phi-icosa-2026-10-30.md`, §4–§5):
T1-about-the-polyhedron, zero NCG content, not a promotion of the
mnemonic.** The bridge form Φ : C_• → W₂₂ was KILLED AT SCOPING
(K-PHI-1 vacuity, K-PHI-2 type, K-PHI-3 numerology guard); this module
is the priced salvage line PHI-C only: a polyhedron's chain complex,
formalized for its own sake. It never mentions W₂₂. NO CLAIM attaches
to this line; it touches no dial.

## The model

The icosidodecahedron as a cell complex on S²: V = 30 vertices,
E = 60 edges, F = 32 faces = 20 triangles + 12 pentagons; vertex
configuration 3.5.3.5; every edge borders exactly one triangle and
exactly one pentagon.

Transcription source: the landed probe PHI-C-PROBE (registry BR1-010):
tables `routeb-general-scratch/phicprobe-tables.json`, run log
`phicprobe-run.txt`. Orientation convention, as recorded there:
vertices 0..29 lexicographic by exact (x, y, z); edges oriented
lower-index → higher-index, ∂₁ = −1 at tail, +1 at head; faces 0..19
triangles then 20..31 pentagons, each face cycle directed so its
Newell normal points outward; face boundary sign +1 when the cycle
traverses an edge tail→head, −1 otherwise.

The bulk data (`edgeList`, `faceList`) in this module was GENERATED
from the probe's JSON tables by
`routeb-general-scratch/phic0-gen.py` — generated literals, not
hand-typed matrices.

**Field choice: ℚ.** The probe certified its incidence data exactly
over ℚ; the later bricks of this line (PHI-C1: ∂₁ ∘ ∂₂ = 0, PHI-C2:
face-split independence, PHI-C3: the census) are stated over this
model's field, ℚ. (The same integer matrices read over ℝ give the
same ranks; nothing in this line consumes ℝ-specific structure.)

**Not in this brick:** ∂₁ ∘ ∂₂ = 0 is PHI-C1 and is NOT proved here.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace ThetLogos

/-- The oriented edge list, transcribed from the probe's tables
    (BR1-010): entry `e` is `(tail, head)` with `tail < head`,
    edges oriented lower-index → higher-index. -/
def edgeList : List (Fin 30 × Fin 30) := [
  (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 9), (2, 6), (2, 10), (3, 4), (3, 7), (3, 11), (4, 8), (4, 12), (5, 7), (5, 9), (5, 14), (6, 8), (6, 10), (6, 15), (7, 11), (7, 14), (8, 12), (8, 15), (9, 13), (9, 17), (10, 13), (10, 18), (11, 16), (11, 19), (12, 16), (12, 20), (13, 17), (13, 18), (14, 21), (14, 23), (15, 22), (15, 24), (16, 19), (16, 20), (17, 21), (17, 25), (18, 22), (18, 26), (19, 23), (19, 27), (20, 24), (20, 28), (21, 23), (21, 25), (22, 24), (22, 26), (23, 27), (24, 28), (25, 26), (25, 29), (26, 29), (27, 28), (27, 29), (28, 29)]

/-- The signed face boundaries, transcribed from the probe's tables
    (BR1-010): faces 0..19 are triangles, 20..31 pentagons; each entry
    is the face's signed boundary as `(edge, sign)` pairs in the
    outward directed cycle order. -/
def faceList : List (List (Fin 60 × ℤ)) := [
  [(0, 1), (4, 1), (1, -1)],
  [(3, 1), (9, -1), (2, -1)],
  [(5, 1), (15, 1), (6, -1)],
  [(8, 1), (18, -1), (7, -1)],
  [(11, 1), (20, -1), (10, -1)],
  [(12, 1), (22, 1), (13, -1)],
  [(14, 1), (21, 1), (16, -1)],
  [(19, 1), (23, -1), (17, -1)],
  [(25, 1), (32, -1), (24, -1)],
  [(26, 1), (33, 1), (27, -1)],
  [(28, 1), (38, 1), (29, -1)],
  [(31, 1), (39, -1), (30, -1)],
  [(35, 1), (48, -1), (34, -1)],
  [(36, 1), (50, 1), (37, -1)],
  [(40, 1), (49, 1), (41, -1)],
  [(43, 1), (51, -1), (42, -1)],
  [(45, 1), (52, -1), (44, -1)],
  [(46, 1), (53, 1), (47, -1)],
  [(55, 1), (56, -1), (54, -1)],
  [(57, 1), (59, 1), (58, -1)],
  [(2, 1), (10, 1), (14, -1), (5, -1), (0, -1)],
  [(1, 1), (7, 1), (17, 1), (12, -1), (3, -1)],
  [(6, 1), (24, 1), (26, -1), (8, -1), (4, -1)],
  [(9, 1), (13, 1), (30, 1), (28, -1), (11, -1)],
  [(16, 1), (34, 1), (40, -1), (25, -1), (15, -1)],
  [(18, 1), (27, 1), (42, 1), (36, -1), (19, -1)],
  [(20, 1), (29, 1), (44, 1), (35, -1), (21, -1)],
  [(23, 1), (37, 1), (46, -1), (31, -1), (22, -1)],
  [(32, 1), (41, 1), (54, 1), (43, -1), (33, -1)],
  [(39, 1), (47, 1), (57, -1), (45, -1), (38, -1)],
  [(48, 1), (52, 1), (58, 1), (55, -1), (49, -1)],
  [(51, 1), (56, 1), (59, -1), (53, -1), (50, -1)]]

/-- The `e`-th oriented edge `(tail, head)`. -/
def edgePair (e : Fin 60) : Fin 30 × Fin 30 :=
  edgeList.get ⟨e.val, by
    have h1 : edgeList.length = 60 := rfl
    have h2 := e.isLt
    omega⟩

/-- The tail (lower-index endpoint) of edge `e`. -/
def edgeTail (e : Fin 60) : Fin 30 := (edgePair e).1

/-- The head (higher-index endpoint) of edge `e`. -/
def edgeHead (e : Fin 60) : Fin 30 := (edgePair e).2

/-- The signed boundary of face `f`, as `(edge, sign)` pairs. -/
def faceBoundary (f : Fin 32) : List (Fin 60 × ℤ) :=
  faceList.get ⟨f.val, by
    have h1 : faceList.length = 32 := rfl
    have h2 := f.isLt
    omega⟩

/-- The signed incidence of edge `e` in the boundary of face `f`:
    the recorded sign if `e` occurs in `f`'s boundary list, else 0. -/
def signOf : List (Fin 60 × ℤ) → Fin 60 → ℤ
  | [], _ => 0
  | (a, s) :: t, e => if a = e then s else signOf t e

/-- The `(e, f)` incidence sign of ∂₂. -/
def faceSign (f : Fin 32) (e : Fin 60) : ℤ := signOf (faceBoundary f) e

/-- Face `f` is a triangle iff its boundary has length 3 (data-level;
    faces 0..19 by the probe's ordering). -/
def isTriangleFace (f : Fin 32) : Bool := (faceBoundary f).length = 3

/-- Face `f` is a pentagon iff its boundary has length 5 (data-level;
    faces 20..31 by the probe's ordering). -/
def isPentagonFace (f : Fin 32) : Bool := (faceBoundary f).length = 5

/-- The edge indices occurring in triangle boundaries, with
    multiplicity (60 entries: 20 triangles × 3 edges). -/
def triEdgeList : List (Fin 60) :=
  (faceList.filter (fun b => b.length = 3)).flatMap (fun b => b.map Prod.fst)

/-- The edge indices occurring in pentagon boundaries, with
    multiplicity (60 entries: 12 pentagons × 5 edges). -/
def penEdgeList : List (Fin 60) :=
  (faceList.filter (fun b => b.length = 5)).flatMap (fun b => b.map Prod.fst)

/-- The ∂₁ matrix (30 × 60) over ℚ: `−1` at an edge's tail, `+1` at
    its head, `0` elsewhere (the probe's orientation convention). -/
def d1Mat : Matrix (Fin 30) (Fin 60) ℚ :=
  fun v e => if v = edgeTail e then -1 else if v = edgeHead e then 1 else 0

/-- The ∂₂ matrix (60 × 32) over ℚ: the signed face-boundary
    incidence transcribed from the probe's tables. -/
def d2Mat : Matrix (Fin 60) (Fin 32) ℚ :=
  fun e f => (faceSign f e : ℚ)

/-- ∂₁ : C₁ → C₀, the edge→vertex boundary map over ℚ,
    `(Fin 60 → ℚ) →ₗ[ℚ] (Fin 30 → ℚ)`. -/
def d1 : (Fin 60 → ℚ) →ₗ[ℚ] (Fin 30 → ℚ) := Matrix.mulVecLin d1Mat

/-- ∂₂ : C₂ → C₁, the face→edge boundary map over ℚ,
    `(Fin 32 → ℚ) →ₗ[ℚ] (Fin 60 → ℚ)`. -/
def d2 : (Fin 32 → ℚ) →ₗ[ℚ] (Fin 60 → ℚ) := Matrix.mulVecLin d2Mat

/-! ## Sanity self-checks (mirroring the probe's, BR1-010) -/

/-- The model has 60 edges. -/
theorem edgeList_length : edgeList.length = 60 := rfl

/-- The model has 32 faces. -/
theorem faceList_length : faceList.length = 32 := rfl

/-- Face count: 20 triangles (data-level, by boundary length). -/
theorem triangle_count :
    (faceList.filter (fun b => b.length = 3)).length = 20 := by decide

/-- Face count: 12 pentagons (data-level, by boundary length). -/
theorem pentagon_count :
    (faceList.filter (fun b => b.length = 5)).length = 12 := by decide

/-- Orientation convention read-back: every edge is oriented
    lower-index → higher-index (tail < head), as recorded in the
    probe's run log. -/
theorem edge_tail_lt_head : ∀ e : Fin 60, edgeTail e < edgeHead e := by decide

/-- Sanity (the probe's headline self-check): every edge lies in
    exactly one triangle. -/
theorem edge_in_exactly_one_triangle : ∀ e : Fin 60, triEdgeList.count e = 1 := by
  decide

/-- Sanity (the probe's headline self-check): every edge lies in
    exactly one pentagon. -/
theorem edge_in_exactly_one_pentagon : ∀ e : Fin 60, penEdgeList.count e = 1 := by
  decide

/-! ## Spot read-backs against the probe's tables -/

/-- Read-back: edge 0 is `(0, 1)` in the probe's tables. -/
theorem edgePair_zero : edgePair 0 = (0, 1) := by decide

/-- Read-back: edge 59 is `(28, 29)` in the probe's tables. -/
theorem edgePair_last : edgePair 59 = (28, 29) := by decide

/-- Read-back: face 0 (triangle `[0, 1, 2]`) has signed boundary
    `[(0, +1), (4, +1), (1, −1)]` in the probe's tables. -/
theorem faceBoundary_zero :
    faceBoundary 0 = [(0, 1), (4, 1), (1, -1)] := by decide

/-- Read-back: face 20 (first pentagon, `[0, 3, 7, 5, 1]`) has signed
    boundary `[(2, +1), (10, +1), (14, −1), (5, −1), (0, −1)]` in the
    probe's tables. -/
theorem faceBoundary_twenty :
    faceBoundary 20 = [(2, 1), (10, 1), (14, -1), (5, -1), (0, -1)] := by decide

/-- Read-back: face 0 is a triangle and face 20 is a pentagon, at the
    data level. -/
theorem face_type_spots : isTriangleFace 0 = true ∧ isPentagonFace 20 = true := by
  decide

/-- ∂₁ applied to a named basis element is the corresponding ∂₁
    matrix column: `(∂₁ (Pi.single e 1)) v = d1Mat v e`. -/
theorem d1_apply_single (v : Fin 30) (e : Fin 60) :
    d1 (Pi.single e 1) v = d1Mat v e := by
  rw [d1, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct_single_one]

/-- ∂₂ applied to a named basis element is the corresponding ∂₂
    matrix column: `(∂₂ (Pi.single f 1)) e = d2Mat e f`. -/
theorem d2_apply_single (e : Fin 60) (f : Fin 32) :
    d2 (Pi.single f 1) e = d2Mat e f := by
  rw [d2, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct_single_one]

/-- Spot read-back: `(∂₁ e₀)₀ = −1` — edge 0's tail is vertex 0
    (probe run log: ∂₁ = −1 at tail). -/
theorem d1_spot_tail : d1 (Pi.single 0 1) 0 = -1 := by
  rw [d1_apply_single]
  decide

/-- Spot read-back: `(∂₁ e₀)₁ = +1` — edge 0's head is vertex 1
    (probe run log: ∂₁ = +1 at head). -/
theorem d1_spot_head : d1 (Pi.single 0 1) 1 = 1 := by
  rw [d1_apply_single]
  decide

/-- Spot read-back: `(∂₁ e₀)₂ = 0` — vertex 2 is not an endpoint of
    edge 0. -/
theorem d1_spot_other : d1 (Pi.single 0 1) 2 = 0 := by
  rw [d1_apply_single]
  decide

/-- Spot read-back: `(∂₂ f₀)₀ = +1` — face 0 traverses edge 0
    tail→head (probe tables, face 0 signed boundary). -/
theorem d2_spot_pos : d2 (Pi.single 0 1) 0 = 1 := by
  rw [d2_apply_single]
  decide

/-- Spot read-back: `(∂₂ f₀)₁ = −1` — face 0 traverses edge 1
    head→tail (probe tables, face 0 signed boundary). -/
theorem d2_spot_neg : d2 (Pi.single 0 1) 1 = -1 := by
  rw [d2_apply_single]
  decide

/-- Spot read-back: `(∂₂ f₀)₂ = 0` — edge 2 is not in face 0's
    boundary (probe tables, face 0 signed boundary). -/
theorem d2_spot_zero : d2 (Pi.single 0 1) 2 = 0 := by
  rw [d2_apply_single]
  decide

/-- Spot read-back: `(∂₂ f₂₀)₀ = −1` — the first pentagon traverses
    edge 0 head→tail (probe tables, face 20 signed boundary). -/
theorem d2_spot_pentagon : d2 (Pi.single 20 1) 0 = -1 := by
  rw [d2_apply_single]
  decide

#print axioms edge_in_exactly_one_triangle
#print axioms edge_in_exactly_one_pentagon
#print axioms triangle_count
#print axioms pentagon_count
#print axioms d1_apply_single
#print axioms d2_apply_single
#print axioms d1_spot_tail
#print axioms d2_spot_neg

end ThetLogos
