# SP-5 — Isospectrality of the Partner Hamiltonians: landing dossier (2026-11-03)

**Brick:** SP-5, the Partner Sector's stretch pin and open remainder.
Fired by Jeff 2026-11-03 by name ("All" — SP-5's park lifted by his
word). Scoping: `~/workspace/your_files/axiom-zero-supersymmetry-scoping-2026-11-03.md`
(SP-5 registered there); Partner landing:
`whitepaper/axiom-tet-partner-landing-2026-11-03.md` (SP-0..SP-4 FULL,
K-SP-ISO fired on SP-5).

**VERDICT: FULL at full rank.** SP-5 lands in its registered form.
K-SP-ISO's recorded blocker is RETIRED (analysis below). With this
landing the Partner Sector stands FULL: SP-0 through SP-5 all at T1.

**Module:** `lean/ThetLogos/AxiomTetPartnerIso.lean` (imports
`ThetLogos.AxiomTetPartner`), built in the isolated worktree
`~/workspace/thet-logos-sp5`, branch `sp5-lane`, from main-tree HEAD
`4e35329` (the item-5 ceremony commit). Strict count **13 theorems
+ 1 def** (theorem/lemma at column 0, comment-stripped, house rule).
Targeted build `lake build ThetLogos.AxiomTetPartnerIso` green
(3231 jobs), warning-clean. `#print axioms` on the headlines
(`sp5_charpoly_identity`, `sp5_charpoly_identity_edgeFinset`,
`finrank_eigenspace_eq`, `toMatrix'_wAdjDiff_eq_transpose`,
`eigenspaceEquiv`, `toMatrix'_mulEdgeLin`, `charpoly_vertexHam`):
each depends on exactly {propext, Classical.choice, Quot.sound} —
inside the fence, no sorryAx. Zero sorrys. NO CLAIM. Dials 0/4.

## The pinned statement form

The scoping registered SP-5 in characteristic-polynomial form:
the nonzero spectra of `H_v`, `H_e` coincide with multiplicities,
as the identity

  `x ^ |E| * p_v(x) = x ^ |X| * p_e(x)`,

with `p_v`, `p_e` the characteristic polynomials of the two
Hamiltonians and `|X| = |V|`. That is exactly what landed, with
`p_v = (vertexHam G w).charpoly`, `p_e = (edgeHam G w).charpoly`
(`LinearMap.charpoly`), and `|E| = Fintype.card ↥G.edgeSet`:

- `sp5_charpoly_identity`:
  `X ^ Fintype.card ↥G.edgeSet * (vertexHam G w).charpoly
   = X ^ Fintype.card V * (edgeHam G w).charpoly`.
- `sp5_charpoly_identity_edgeFinset`: the same identity with the
  edge count in the Partner brick's own bookkeeping
  (`#G.edgeFinset`, as in SP-3/SP-4).

No hypothesis on the weights: the identity holds for EVERY real
weight function `w`. Positivity was the price of SP-2..SP-4
(kernels, dimensions, index); isospectrality is pure algebra of
the pair `(D, Dᵀ)` and is free of it.

## How it lands

1. **Matrices of the weighted operators.** `mulEdgeLin` is
   diagonal in the standard basis (`toMatrix'_mulEdgeLin`), so
   `D = √W ∘ d` and `Dᵀ = dᵀ ∘ √W` have matrices
   `diag(√W) * (matrix of d)` and `(matrix of dᵀ) * diag(√W)`
   (`toMatrix'_wDiff`, `toMatrix'_wAdjDiff`, via
   `LinearMap.toMatrix'_comp`). With the Partner brick's landed
   `toMatrix'_diffOp`, the matrix of `Dᵀ` is the transpose of the
   matrix of `D` (`toMatrix'_wAdjDiff_eq_transpose`) — the
   matrix-level adjoint statement for the weighted pair.
2. **Hamiltonians as products.** `toMatrix'_vertexHam`,
   `toMatrix'_edgeHam`: the matrix of `H_v` is
   `(matrix of Dᵀ) * (matrix of D)`; the matrix of `H_e` is the
   product in the other order. The characteristic polynomial of
   each operator is that of its standard-basis matrix
   (`charpoly_vertexHam`, `charpoly_edgeHam`, via
   `Matrix.toLin'_toMatrix'` and `Matrix.charpoly_toLin'`).
3. **One Mathlib application.** `Matrix.charpoly_mul_comm'`
   (rectangular charpoly identity, proved in Mathlib by a
   block-determinant computation) closes the headline in one
   step.
4. **The eigenspace form lands too.** `D` carries the
   `lam`-eigenspace of `H_v` into that of `H_e`
   (`wDiff_mem_eigenspace_image`: both sides are `D Dᵀ D f`),
   `Dᵀ` carries back (`wAdjDiff_mem_eigenspace_image`), and for
   `lam ≠ 0` the two restricted maps are explicit mutual
   inverses up to the scale `lam` — `eigenspaceEquiv`, a linear
   equivalence of the two eigenspaces by `D` and `lam⁻¹ • Dᵀ`.
   Hence `finrank_eigenspace_eq`: equal eigenspace dimensions
   for every `lam ≠ 0` (geometric multiplicities).

## The blocker analysis (why K-SP-ISO's blocker does not stand)

The Partner lane recorded the blocker as: the
eigenspace-intertwining route "needs spectral machinery for
self-adjoint operators on plain function spaces that this
Mathlib does not provide off the shelf (no inner product
instances on `ι → ℝ` as bare types; the spectral theorem would
have to be assembled via matrices/eigenspaces by hand)". That
blocker is half right and wholly non-fatal:

- **Right:** the pin has no inner-product instances on bare pi
  types and no spectral theorem for operators on them. None is
  assembled or used here.
- **Non-fatal, twice.** (a) The registered polynomial identity
  is not a spectral-theorem statement at all: it is a
  determinant identity for a product pair of rectangular
  matrices, and it is Mathlib stock
  (`Matrix.charpoly_mul_comm'`). The only bridge owed was
  operator → standard-basis matrix, which the Partner brick had
  already half-built for SP-4 (`toMatrix'_diffOp`). (b) The
  intertwining route itself never needed the spectral theorem:
  an eigenspace is a kernel, and on the `lam ≠ 0` eigenspace
  the supercharge relations `DᵀD = H_v`, `DDᵀ = H_e` read
  `Dᵀ ∘ D = lam • id`, `D ∘ Dᵀ = lam • id` — explicit inverses,
  no diagonalization, no existence of eigenvalues anywhere.

**What is NOT proved, on the face.** The spectral theorem
(diagonalizability of the two Hamiltonians; the coincidence of
algebraic and geometric multiplicities) is neither proved nor
asserted: the polynomial identity (algebraic multiplicities)
and the eigenspace equivalence (geometric multiplicities) are
landed independently, and this brick does not claim they are
the same theorem. The T2 numerical agreement recorded in the
Partner dossier is superseded as evidence by these T1
statements; it is cited in no proof.

## Fences

- **Naming fence (inherited, in force):** FINITE SUPERSYMMETRIC
  QUANTUM MECHANICS ON A GRAPH — a grading, a supercharge, two
  finite-dimensional sectors, an index, and now their
  isospectrality. No superpartners of particles, no physics
  claim, no Standard Model contact. **NO CLAIM; dials 0/4.**
- The landed Partner module is untouched: every statement here
  is by addition in a new module.

## Census effect (for the parent ceremony; not asserted here)

This module adds **13 strict / 1 module** on top of HEAD
`4e35329`. Parent re-derives all figures at integration; nothing
in this dossier is a public number.

## Fence-admission candidates (for the parent ceremony)

1. `ThetLogos.sp5_charpoly_identity` — SP-5, the registered
   polynomial identity (headline).
2. `ThetLogos.finrank_eigenspace_eq` — SP-5, geometric form.
3. `ThetLogos.toMatrix'_wAdjDiff_eq_transpose` — the weighted
   matrix adjoint.

## CEREMONY (parent integration, 2026-11-03)

Integrated into the main tree from sp5-lane commit `d652592` (base
`4e35329`) onto main-tree HEAD `eac12f3` (the U-3a ceremony
correction commit); module and this dossier copied byte-identical
(diff-verified). Main-tree targeted build
`lake build ThetLogos.AxiomTetPartnerIso` green (3231 jobs,
matching the lane), zero errors, zero warnings attributable to the
module, zero sorrys. Independent recount: module **13 strict +
1 def**, exact match with the lane. Fence admissions — all 7
headlines checked on the lane's face (`sp5_charpoly_identity`,
`sp5_charpoly_identity_edgeFinset`, `finrank_eigenspace_eq`,
`toMatrix'_wAdjDiff_eq_transpose`, `eigenspaceEquiv`,
`toMatrix'_mulEdgeLin`, `charpoly_vertexHam`) — admitted WITH
`import ThetLogos.AxiomTetPartnerIso` in the same commit as the
module, per the CI lesson: **FENCE PASS 118/118** (111 → 118),
every headline on exactly {propext, Classical.choice, Quot.sound},
no sorryAx. Census (FILES-TRUE, method of record): 12,995/471 →
**13,008 strict / 472 modules**; README prose census and shields
badge both updated to 13,008 / 472, kept equal. Ledger record
`sp5-isospectrality` (standing, T3); validator PASS. **With this
ceremony the Partner Sector stands FULL: SP-0 through SP-5, all at
T1** — the K-SP-ISO blocker is retired on this dossier's face, and
the spectral-theorem fence stands (neither proved nor asserted; no
claim that algebraic and geometric multiplicities coincide). The
ceremony commit hash is recorded in the pipeline log
(`~/workspace/launch-pipeline-2026-10-29.md`), per house pattern.
NO CLAIM; dials 0/4.
