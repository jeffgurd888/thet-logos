# Decoherence toy — verdict (2026-10-18)

**VERDICT: STANDS (T1) at the priced scope (S–M).** The priced
object from the Schrödinger gauntlet §4c, re-scoped in the
parked-fleet gauntlet §9: the corpus's first **partial trace**,
plus the **dephasing toy** built on it. One module, 37 strict T1,
zero sorry. Program total 3,101 + 37 = **3,138 strict**.

Module: `lean/ThetLogos/DecoherenceToy.lean` (581 lines, 6 defs,
37 theorems). Dossier: this file. NO CLAIM beyond the toy's charter
(see Fences).

## What was missing, verified

The gauntlet §9 recorded: partial trace — 0 hits in the corpus,
0 hits in the pinned Mathlib. Re-verified during this build:
`grep partialTrace|partial_trace` over the pinned Mathlib tree
(`Mathlib/`) returns no files; the corpus grep likewise. The
commission's fallback ("if it now exists in Mathlib, use it") did
not trigger. The object is built here from scratch.

## PT-1 — partial trace (priced S) — STANDS

`partialTraceB A` for `A : Matrix (m × n) (m × n) ℂ`, defined by
block trace: entry `(i, i')` is `∑ j, A (i, j) (i', j)`. (Stated
over general finite types `m, n`, not just `Fin m, Fin n` — the
same proofs.) The gauntlet's five named properties, all T1:

| Property | Theorem |
|---|---|
| definition by block trace | `partialTraceB`, `partialTraceB_apply` |
| trace preservation | `trace_partialTraceB` |
| positivity preservation | `partialTraceB_quadratic_nonneg` (via `dotProduct_partialTraceB_mulVec`) |
| product rule Tr_B(A ⊗ₖ B) = Tr(B)·A | `partialTraceB_kronecker` |
| adjoint/star compatibility | `conjTranspose_partialTraceB` |

Supporting package: `partialTraceB_zero/_add/_smul` (linearity),
`isHermitian_partialTraceB`. Positivity is proved in the corpus's
own form — the quadratic-form clause of `IsDensityMatrix`
(FlowKernel.lean) — through the **embedding identity**
`dotProduct_partialTraceB_mulVec`: the reduced quadratic form at
`v` is the sum over environment slices `j` of the joint quadratic
form at the embedded vector `embedB v j`. (The equivalent
`Matrix.PosSemidef` form is the same statement under the standard
finite-dimensional equivalence; the corpus's density-matrix
definition uses the quadratic-form clause, so that is the form
proved.)

Beyond the priced five, two additions, both cheap consequences of
the same machinery and named here so they are not mistaken for
scope creep in either direction:

- **Trace-duality characterization** `trace_partialTraceB_mul`:
  `Tr ((Tr_B A) * X) = Tr (A * (X ⊗ₖ 1))` for all `X`. This is the
  basis-independent content of "well-defined": it pins
  `partialTraceB` uniquely among linear maps, under the
  nondegenerate trace pairing.
- **Reduced states are states** `IsDensityMatrix.partialTraceB`:
  the partial trace of a corpus density matrix is a corpus density
  matrix (Hermitian + positivity + trace, one clause each from the
  preservation package).

## PT-2 — the toy (priced S) — STANDS

The dephasing channel is **diagonal pinching in a fixed product
basis**: `pinch A = Matrix.diagonal (fun i => A i i)`. The
gauntlet's five named statements, all T1:

| Statement | Theorem |
|---|---|
| populations invariant | `pinch_diag` (and `trace_pinch`) |
| off-diagonals killed in one application | `pinch_apply_ne` |
| geometric decay under iteration | `pinch_iterate`: `pinch^[k] = pinch` for all `k ≥ 1` — see the note below |
| purity `Tr ρ²` non-increasing | `trace_sq_pinch_le` |
| equality iff already diagonal | `trace_sq_pinch_eq_iff` |
| reduced diagonal = system populations | `partialTraceB_diag` (PT-1) |

Note on "geometric decay": for the pinching channel the decay
degenerates — the off-diagonals do not shrink by a factor per
step, they are exactly zero after ONE application and stay zero
(`pinch_idem`, `pinch_iterate`). The dossier records this as the
toy behaving *more* trivially than the priced wording, not less:
the priced statement is proved in the stronger exact form.

Purity route: `frobeniusSq A = ∑ i j, ‖A i j‖²`, with the identity
`trace_mul_self_eq_frobeniusSq` (`Tr (A * A) = ↑(frobeniusSq A)`
for Hermitian `A`) connecting it to `Tr ρ²`; pinching deletes
exactly the off-diagonal summands (`frobeniusSq_pinch`,
`diag_frobeniusSq_le`), and equality forces every off-diagonal
summand to vanish.

The named coherence quantity is `offDiagMass` (ℓ¹ mass of the
off-diagonal entries): `offDiagMass_pinch` — zero after one
application; `offDiagMass_pinch_iterate` — zero at every iterate
`k ≥ 1`.

Glue (PT-1 × PT-2), the toy's headline: pinching commutes with the
partial trace (`partialTraceB_pinch`), so after one joint
pinching in the product basis, **every off-diagonal of the reduced
state is exactly zero** (`partialTraceB_pinch_apply_ne`) and the
reduced coherence quantity vanishes
(`offDiagMass_partialTraceB_pinch`). The dephased state is again a
density matrix (`isDensityMatrix_pinch`; the extra content is that
diagonal entries of a density matrix are real and nonnegative —
the quadratic form at a basis vector — proved via `basisVec`,
`star_basisVec`, `mulVec_basisVec`).

## Commission deviations

None of substance. (a) The commission's item (2), "a toy
system⊗environment model with an explicit interaction," was
scoped by the governing gauntlet as the pinching channel with
**no environment dynamics**; per instructions, the gauntlet's
statements govern. The joint system⊗environment space is present
throughout (the product index of PT-1), and the channel acts on it
in the product basis. (b) Everything is stated over general finite
index types rather than `Fin m × Fin n` specifically — strictly
more general, same proofs, named here for the record.

## Fences

- **TOY, by charter.** Finite-dimensional throughout; a single
  channel (pinching in one fixed basis); no environment dynamics,
  no interaction Hamiltonian, no rates, no timescales, no
  continuum. Nothing in the module or this dossier is a claim
  about physical decoherence in any actual system.
- The measurement problem is not touched, in either direction
  (T5 by type, per the Schrödinger gauntlet §4b).
- Hygiene: the module imports `ThetLogos.FlowKernel` for the
  `IsDensityMatrix` *definition only*. No proof routes through
  FlowKernel or ModularTime theorems; in particular the corpus's
  one quarantined sorry (`ModularTime.lean`, inside
  `kms_identity_diagonal`) is not depended on — verified by the
  axiom check below: every headline depends on exactly the
  standard three axioms, no `sorryAx`.

## Verification

- Targeted build: `lake build ThetLogos.DecoherenceToy` — green,
  3,244 jobs; `.olean` present (594 KB).
- Strict recount: **37** (line-initial `^(theorem|lemma) ` on
  comment-stripped source); `@[simp]`-prefixed: **0** (attribute
  count also 37); `sorry`/`admit` in stripped source: **0**.
- Axioms: `#print axioms` on 13 headlines (`trace_partialTraceB`,
  `partialTraceB_kronecker`, `trace_partialTraceB_mul`,
  `dotProduct_partialTraceB_mulVec`,
  `partialTraceB_quadratic_nonneg`, `IsDensityMatrix.partialTraceB`,
  `isDensityMatrix_pinch`, `trace_sq_pinch_le`,
  `trace_sq_pinch_eq_iff`, `partialTraceB_pinch`,
  `partialTraceB_pinch_apply_ne`,
  `offDiagMass_partialTraceB_pinch`, `pinch_iterate`) — each exactly
  `[propext, Classical.choice, Quot.sound]`.
- Existing modules unmodified. Scratch/probe files (name probes,
  axiom check) kept in `/tmp`, never in the tree.
