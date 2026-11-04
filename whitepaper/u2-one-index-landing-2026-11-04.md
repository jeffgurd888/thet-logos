# U-2 ONE INDEX — Landing Dossier

**Brick:** U-2 "One Index", second brick of the unification line
(scoping: `your_files/unification-scoping-2026-11-03.md` §2 (U-2),
seats at §1.2). **Lane:** worktree `~/workspace/thet-logos-u2`,
branch `u2-one-index-lane`, cut from main HEAD `5050bb2` (local;
census 13,147 strict / 481 modules; fence 190/190 — verified at
lane start). NOT integrated, NOT pushed — lane commit only;
parent runs the integration.

**Module:** `lean/ThetLogos/OneIndex.lean`.

**NO CLAIM** — parts of any official Millennium statement closed
by this module: 0. **Dials: 0/4.** This module does not touch the
analytic line, `LayerKernelPos`, W3, or physics (scoping §4
fence). A named finite index lemma is not a unified theory of
anything.

## Verdict: LANDED as scoped — graded HYGIENE (K-U2-EMPTY FIRES)

The promotion landed in full: the master index lemma is named
and proved at full generality, and SP-3 / SP-4 are re-derived
from it as corollaries at `T = wDiff G w`. The pre-registered
honest grade is nevertheless **HYGIENE, not a unification
landing**: SP-3 and SP-4 were already fully general in
`AxiomTetPartner` before this brick, and no second seat in the
corpus consumes the master today (per the scoping's check,
`BridgeMagnetic*` carries no finrank/ker results waiting to be
demoted). **K-U2-EMPTY therefore fires at full rank**: the
landing made nothing a corollary that was not already general.
What the brick buys is what the scoping priced it as — a named,
reusable master seat outside Partner's file, so a future second
consumer (a magnetic index, a second operator pair) cites one
theorem instead of re-running rank-nullity. The scoping
recommended U-2 only bundled; it is recorded here exactly at
that grade, neither inflated to unification nor hidden.

Strict count: **9 theorems + 1 def** — inside the scoping's S
band (est. strict 5–12). Targeted build green (3228 jobs),
**warning-clean**, zero sorrys, no `native_decide`. `#print
axioms` on all 9 theorems: **exactly {propext, Classical.choice,
Quot.sound}** for every one, no sorryAx.

## What landed

| Item | Status | Name |
|---|---|---|
| The transpose (dual), matrix form | NEW DEF | `transposeLin` |
| Matrix of the transpose | FULL | `toMatrix'_transposeLin` |
| Transpose involutive | FULL | `transposeLin_transposeLin` |
| Promoted helper (Partner's `finrank_range_eq_rank`) | FULL | `finrank_range_eq_matrixRank` |
| Rank of transpose = rank | FULL | `finrank_range_transposeLin` |
| **MASTER, addition form** | **FULL** | **`finrank_ker_add_card`** |
| **MASTER, difference form** | **FULL** | **`finrank_ker_sub_finrank_ker_transposeLin`** |
| Bridge at `wDiff` (dimension form) | FULL | `finrank_ker_transposeLin_wDiff` |
| SP-3 as corollary of the master | FULL | `finrank_ker_edgeHam_add_via_oneIndex` |
| SP-4 as corollary of the master | FULL | `index_eq_via_oneIndex` |

**The dual, shaped at build (as the scoping directed).** The
transpose is the **transpose matrix**: `transposeLin T :=
Matrix.toLin' (LinearMap.toMatrix' T)ᵀ`, the map
`(κ → ℝ) →ₗ[ℝ] (ι → ℝ)` whose matrix is the transpose of `T`'s.
Chosen over the abstract dual map because (i) the engine already
in the tree is `Matrix.rank_transpose`, so the master is
rank-nullity twice plus that one fact, with no new adjoint
machinery; and (ii) the corollaries consume only the transpose
kernel's *dimension* at the Partner seat, which the bridge lemma
supplies by a pure rank count (below). The master is stated in
addition form (`finrank ker T + card κ = finrank ker Tᵀ +
card ι`, no subtraction ever taken) and in the scoping's honest
integer-difference form
(`finrank ker T − finrank ker Tᵀ = card ι − card κ` over `ℤ`).

## Corollary wiring (shown, not asserted)

- `finrank_ker_edgeHam_add_via_oneIndex` — statement
  character-identical to Partner's `finrank_ker_edgeHam_add`
  (SP-3), same `(G, w)`, same positivity hypothesis `hw`. Proof:
  the master `finrank_ker_add_card` at `T = wDiff G w` equates
  `finrank ker (wDiff) + Fintype.card ↥G.edgeSet` with
  `finrank ker (transposeLin wDiff) + Fintype.card V`; the bridge
  `finrank_ker_transposeLin_wDiff` rewrites the transpose
  kernel's dimension to `finrank ker (wAdjDiff)` — both are
  `#edges − rank (wDiff)`, by rank-nullity on each map plus
  `finrank_range_transposeLin` (master side) and Partner's
  `finrank_range_wAdjDiff` (adjoint side); Partner's
  `ker_edgeHam_eq` turns `ker (wAdjDiff)` into `ker (edgeHam)`,
  Partner's `ker_wDiff_eq` + `finrank_perComp` give
  `finrank ker (wDiff) = Nat.card G.ConnectedComponent`, and
  `SimpleGraph.edgeFinset_card` closes the count. `omega`
  assembles.
- `index_eq_via_oneIndex` — statement character-identical to
  Partner's `index_eq` (SP-4), same generality. Proof: the SP-3
  corollary above plus Partner's `finrank_ker_vertexHam`, by
  `omega` — the same shape as Partner's own `index_eq` proof,
  but consuming this module's master-derived SP-3.
- The originals in `AxiomTetPartner.lean` are **untouched** —
  not edited, renamed, or re-proved. The two corollaries are
  additional routes; Partner's file is consumed only through its
  standing statements (`ker_edgeHam_eq`, `ker_wDiff_eq`,
  `finrank_perComp`, `finrank_ker_vertexHam`,
  `finrank_range_wAdjDiff`).

## Build notes (for the integration)

- Name-collision scan of all 10 new names against the main tree
  at `5050bb2`: **zero collisions** (declaration-level grep over
  `lean/ThetLogos/`).
- One linter device on the face: `finrank_range_eq_matrixRank`
  carries `omit [Fintype κ] [DecidableEq κ] in` (the rank of the
  range needs the codomain instances only through the matrix,
  which the local `Classical.propDecidable` instance supplies) —
  this is what keeps the module warning-clean; Partner's helper
  avoided the warning by binding the instances in the theorem
  itself.
- Suggested fence admissions at integration: the 9 theorems
  above — registry edit and module in the same commit, per the
  CI lesson. Lane-side census projection (integration
  re-derives): 13,147 → **13,156 strict / 482 modules**.
- The lane's `.lake` is a hardlink copy of main's packages plus
  a real copy of `build`/`config`; no main-tree file was
  modified by the lane build.

**NO CLAIM. Dials 0/4. Grade: HYGIENE (K-U2-EMPTY fired), at
full rank.**

## INTEGRATION (main tree, 2026-11-04)

Integrated from u2-lane commit `2685348` onto main-tree HEAD
`4ad7b6f` (lane base `5050bb2`; module + dossier new files).
Module and dossier copied **byte-identical** (md5-verified:
module `8c96607b3b2322bb4fa62010c785b5a6`, dossier at copy
`daaab84e6398d1a72d19c8438a2c4647`). Declaration-level
collision scan of all 10 OneIndex names against the **current**
main tree: **zero collisions** (re-scanned at integration, not
only at the lane base). Main-tree targeted build green
(**3228 jobs**, matching the lane), zero sorrys (zero-sorry gate
PASS, 499 files), module **warning-clean** on forced recompile.
Recount: module **9 strict + 1 def** exact; census files-true
(whole-tree 13,858/499 minus frozen remainder 669/15):
13,180/483 → **13,189 strict / 484 modules**; README prose +
badge both 13,189/484, kept equal. Fence: the 9 theorems
admitted WITH the `import ThetLogos.OneIndex` line in the same
commit as the module — **FENCE PASS 222/222**, every new theorem
on exactly {propext, Classical.choice, Quot.sound}, no sorryAx.
Ledger record `u2-one-index` (standing, T3, kill_id
K-U2-EMPTY), validator **PASS** (30 records).

**GRADE CARRIED AT FULL RANK: HYGIENE — K-U2-EMPTY FIRED.**
SP-3/SP-4 were already fully general; no second seat consumes
the master today. This integration places the named master seat
on the public record at exactly that grade — **not** a
unification landing. **NO CLAIM; dials 0/4.**
