/-
# U-2 ONE INDEX — the promoted master index lemma

Brick: U-2 "One Index", second brick of the unification line
(scoping: `your_files/unification-scoping-2026-11-03.md` §2 (U-2),
seats at §1.2). Commission: the scoping's promotion — Partner's
internal helper `finrank_range_eq_rank` (`AxiomTetPartner.lean`,
line ~867), the rank-of-transpose engine inside SP-3/SP-4, becomes
a NAMED master index lemma in its own module, and SP-4 / SP-3 are
re-derived as corollaries at `T = wDiff G w`.

**The form of the transpose (the build-time choice, on the
face).** The scoping's honest form is
`finrank ker T − finrank ker Tᵀ = card ι − card κ`, with the dual
"shaped at build". The dual used here is the **transpose matrix**:
`transposeLin T := Matrix.toLin' (LinearMap.toMatrix' T)ᵀ`, the
linear map `(κ → ℝ) →ₗ[ℝ] (ι → ℝ)` whose matrix is the transpose
of `T`'s matrix. This form was chosen because (i) the engine
already in the tree is exactly `rank T = rank Tᵀ` for matrices
(`Matrix.rank_transpose`), so the master is rank-nullity twice
plus that one fact, with no new adjoint machinery; and (ii) at
the Partner seat, the kernel dimension of `transposeLin (wDiff)`
agrees with that of `wAdjDiff` by a pure rank count (Partner's
`finrank_range_wAdjDiff` + rank-nullity on both maps), which is
all the corollaries consume. The master is stated twice: in
addition form (`finrank_ker_add_card`, no subtraction ever
taken) and in the scoping's integer-difference form
(`finrank_ker_sub_finrank_ker_transposeLin`).

**Corollary wiring.** SP-3
(`finrank_ker_edgeHam_add_via_oneIndex`) is proved FROM the
master at `T = wDiff G w`: the master equates
`finrank ker (wDiff) + #edges` with
`finrank ker (transposeLin wDiff) + #vertices`; the bridge lemma
`finrank_ker_transposeLin_wDiff` identifies the transpose
kernel's dimension with `finrank ker (wAdjDiff) = finrank ker
(edgeHam)` (Partner's `ker_edgeHam_eq`), and
`finrank ker (wDiff) = #components` is Partner's SP-2 seat
(`ker_wDiff_eq` + `finrank_perComp`). SP-4
(`index_eq_via_oneIndex`) then follows from the SP-3 corollary
plus Partner's `finrank_ker_vertexHam`, exactly the shape of
Partner's own `index_eq` proof but consuming the corollary
proved here. The originals `finrank_ker_edgeHam_add` and
`index_eq` in `AxiomTetPartner` are NOT edited, renamed, or
re-proved; the two theorems here are additional routes to the
same statements at the same generality (same `(G, w)`, same
positivity hypothesis `hw`).

**Honest grade (pre-committed in the scoping, K-U2-EMPTY).**
SP-3 and SP-4 were already fully general before this brick, and
no second seat in the corpus consumes the master today (the
scoping checked: `BridgeMagnetic*` carries no finrank/ker
results waiting to be demoted). Promoting the helper therefore
makes nothing a corollary that was not already general:
**K-U2-EMPTY FIRES — this brick is HYGIENE at full rank, not a
unification landing.** What it buys is exactly what hygiene
buys: the index engine now has a name, a statement, and a seat
outside Partner's file, so a future second consumer (a magnetic
index, a second operator pair) can cite one master instead of
re-running rank-nullity. The dossier records the grade the
evidence supports; the scoping's recommendation was that U-2
ride along bundled, and it is recorded here as such.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. This module does not touch
the analytic line, `LayerKernelPos`, W3, or physics (scoping
§4 fence). A named finite index lemma is not a unified theory
of anything.
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import ThetLogos.AxiomTetPartner

attribute [local instance] Classical.propDecidable

open Finset SimpleGraph

namespace ThetLogos

/-! ## The transpose of a pi-type operator

For `T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)` between finite function spaces,
the transpose is taken at the matrix: `transposeLin T` is the
map whose matrix is `(toMatrix' T)ᵀ`. -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The transpose of a linear map between finite function
spaces, via the transpose matrix: `transposeLin T` is the map
`(κ → ℝ) →ₗ[ℝ] (ι → ℝ)` with matrix `(toMatrix' T)ᵀ`. -/
noncomputable def transposeLin (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.toLin' (LinearMap.toMatrix' T).transpose

/-- The matrix of the transpose is the transpose of the matrix. -/
theorem toMatrix'_transposeLin (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    LinearMap.toMatrix' (transposeLin T) = (LinearMap.toMatrix' T).transpose :=
  LinearMap.toMatrix'_toLin' _

/-- The transpose is involutive: transposing twice returns `T`. -/
theorem transposeLin_transposeLin (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    transposeLin (transposeLin T) = T := by
  show Matrix.toLin' (LinearMap.toMatrix' (transposeLin T)).transpose = T
  rw [toMatrix'_transposeLin, Matrix.transpose_transpose, Matrix.toLin'_toMatrix']

/-! ## The promoted rank engine

Partner's helper `finrank_range_eq_rank`, promoted and named:
the finrank of the range is the rank of the matrix. The proof is
the helper's own argument, carried verbatim in content. -/

/- **The promoted helper.** The finrank of the range of a
pi-type operator is the rank of its matrix. (Partner's internal
`finrank_range_eq_rank`, promoted to a named master seat.) -/
omit [Fintype κ] [DecidableEq κ] in
theorem finrank_range_eq_matrixRank (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Module.finrank ℝ ↥T.range = (LinearMap.toMatrix' T).rank := by
  show Module.finrank ℝ ↥T.range
    = Module.finrank ℝ ↥(LinearMap.range (LinearMap.toMatrix' T).mulVecLin)
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

/-- Rank of the transpose equals rank of the operator — the
abstract form of Partner's `finrank_range_adjDiff` /
`finrank_range_wAdjDiff` engine. -/
theorem finrank_range_transposeLin (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Module.finrank ℝ ↥(transposeLin T).range = Module.finrank ℝ ↥T.range := by
  rw [finrank_range_eq_matrixRank, finrank_range_eq_matrixRank, toMatrix'_transposeLin,
    Matrix.rank_transpose]

/-! ## THE MASTER INDEX LEMMA (U-2)

Rank-nullity on `T` and on `transposeLin T`, plus
`rank T = rank Tᵀ`: the kernel dimensions differ by exactly the
difference of the two space dimensions. -/

/-- **U-2 MASTER, addition form.** For every linear map `T`
between finite function spaces,
`finrank ker T + card κ = finrank ker Tᵀ + card ι` — the index
of `T`, stated so no subtraction is ever taken. -/
theorem finrank_ker_add_card (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Module.finrank ℝ ↥T.ker + Fintype.card κ
      = Module.finrank ℝ ↥(transposeLin T).ker + Fintype.card ι := by
  have hT := LinearMap.finrank_range_add_finrank_ker T
  have hTt := LinearMap.finrank_range_add_finrank_ker (transposeLin T)
  rw [Module.finrank_pi] at hT hTt
  have hr := finrank_range_transposeLin T
  omega

/-- **U-2 MASTER, difference form (the scoping's honest form).**
`finrank ker T − finrank ker Tᵀ = card ι − card κ` over `ℤ`. -/
theorem finrank_ker_sub_finrank_ker_transposeLin (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (Module.finrank ℝ ↥T.ker : ℤ) - (Module.finrank ℝ ↥(transposeLin T).ker : ℤ)
      = (Fintype.card ι : ℤ) - (Fintype.card κ : ℤ) := by
  have h := finrank_ker_add_card T
  omega

/-! ## Corollaries at the Partner seat: SP-3 and SP-4 re-derived

At `T = wDiff G w` the two spaces are the vertex sector
(`ι = V`) and the edge sector (`κ = ↥G.edgeSet`). The bridge
between the abstract transpose and Partner's adjoint `wAdjDiff`
is a dimension count only: both kernels have dimension
`#edges − rank (wDiff)`, by rank-nullity and the two rank
equalities (the master's, and Partner's
`finrank_range_wAdjDiff`). -/

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
  (w : Sym2 V → ℝ)

/-- The bridge: at the weighted difference operator, the
abstract transpose's kernel has the same dimension as Partner's
adjoint kernel. (Dimension form only — the maps are not
identified here, and no corollary needs more.) -/
theorem finrank_ker_transposeLin_wDiff
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(transposeLin (wDiff G w)).ker
      = Module.finrank ℝ ↥(wAdjDiff G w).ker := by
  have hT := LinearMap.finrank_range_add_finrank_ker (transposeLin (wDiff G w))
  have hA := LinearMap.finrank_range_add_finrank_ker (wAdjDiff G w)
  rw [Module.finrank_pi] at hT hA
  have hr1 : Module.finrank ℝ ↥(transposeLin (wDiff G w)).range
      = Module.finrank ℝ ↥(wDiff G w).range := finrank_range_transposeLin _
  have hr2 : Module.finrank ℝ ↥(wAdjDiff G w).range
      = Module.finrank ℝ ↥(wDiff G w).range := finrank_range_wAdjDiff G w hw
  omega

/-- **SP-3, re-derived from the master (U-2 corollary).**
`finrank ker H_e + #vertices = #edges + #components` — the same
statement as Partner's `finrank_ker_edgeHam_add`, at the same
generality, proved FROM `finrank_ker_add_card` at
`T = wDiff G w` via the bridge and Partner's SP-2 seat. The
original in `AxiomTetPartner` stands untouched. -/
theorem finrank_ker_edgeHam_add_via_oneIndex
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(edgeHam G w).ker + Fintype.card V
      = #G.edgeFinset + Nat.card G.ConnectedComponent := by
  have hker : Module.finrank ℝ ↥(edgeHam G w).ker
      = Module.finrank ℝ ↥(wAdjDiff G w).ker := by
    rw [ker_edgeHam_eq]
  have hmaster := finrank_ker_add_card (wDiff G w)
  have hbridge := finrank_ker_transposeLin_wDiff G w hw
  have hcomp : Module.finrank ℝ ↥(wDiff G w).ker
      = Nat.card G.ConnectedComponent := by
    rw [ker_wDiff_eq G w hw]
    exact finrank_perComp G
  rw [SimpleGraph.edgeFinset_card]
  omega

/-- **SP-4 (THE INDEX), re-derived from the master (U-2
corollary).** `finrank ker H_v + #edges = finrank ker H_e +
#vertices` — the same statement as Partner's `index_eq`, at the
same generality, proved from the SP-3 corollary above plus
Partner's `finrank_ker_vertexHam`. The original in
`AxiomTetPartner` stands untouched. -/
theorem index_eq_via_oneIndex (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) :
    Module.finrank ℝ ↥(vertexHam G w).ker + #G.edgeFinset
      = Module.finrank ℝ ↥(edgeHam G w).ker + Fintype.card V := by
  have h1 := finrank_ker_edgeHam_add_via_oneIndex G w hw
  have h2 : Module.finrank ℝ ↥(vertexHam G w).ker
      = Nat.card G.ConnectedComponent :=
    finrank_ker_vertexHam G w hw
  omega

end ThetLogos
