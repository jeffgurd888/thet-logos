# Gram clause, Route B — step T2: the averaging-projection lemma

**Landed 2026-10-23, parent-verified.** Module:
`lean/ThetLogos/AveragingProjection.lean` (334 lines). Charter:
`whitepaper/gram-clause-scoping-2026-10-23.md` §4 Route B, step T2;
fences §5.

## Verdict: T2 STANDS WHOLE (T1)

For a compact group `G`, a Haar probability measure `μ` on `G`
(left-invariant and inversion-invariant, carried as typeclass
hypotheses), and a continuous finite-dimensional unitary
representation `ρ` of `G` on a complex inner product space `E`
(representation laws as pointwise hypotheses), the averaging operator
`A = ∫ g, ρ g ∂μ` is the orthogonal projection onto the invariant
subspace. All four chartered items are proved:

1. **Idempotence** — `averagingOperator_idempotent`: `A ∘L A = A`,
   via left Haar invariance (`ρ g₀ (A v) = A v`).
2. **Self-adjointness** — `averagingOperator_adjoint`: `A.adjoint = A`,
   from unitarity plus inversion invariance of `μ`.
3. **Range = invariant subspace** — `averagingOperator_range`, with
   `A` the identity there (`averagingOperator_of_mem_invariant`) and
   the orthogonality `inner_apply_sub_left` stated explicitly.
4. **Finite Gram sum** — `averagingOperator_gram`: for an orthonormal
   basis `e` of the invariant subspace,
   `A v = ∑ i, ⟪e i, v⟫ • e i`.

No Peter–Weyl, no Schur, no irreducibility: invariance and unitarity
only. Pure finite-dimensional harmonic analysis — no lattice, no
plaquettes, no `β`, no gauge-theory statement. **NO CLAIM** — parts
of any official Clay statement closed by this module: 0.

## Verification (parent, on the shipped text)

- Targeted build `lake build ThetLogos.AveragingProjection`:
  EXIT 0 (2,645 jobs), fresh `.olean`.
- Recount (house rule, comment-stripped, nesting-aware):
  **15 strict** theorem/lemma declarations, **3 defs**; sorry census
  **0**, admits **0**.
- `#print axioms` (parent-run) on the eight headline declarations:
  each depends only on `[propext, Classical.choice, Quot.sound]` —
  no `sorryAx`, no corpus axioms.

Program census after this landing: **4,204 strict / 4,238
attribute-inclusive, 138 counted modules** (the module's one
`@[simp]` sits on its own line above an already-counted lemma, so
the attribute-inclusive total is unchanged).

## Formulation choices (disclosed, builder's record)

- `E` abstract + pointwise representation hypotheses instead of a
  bundled unitary-group homomorphism: T4 instantiates by discharging
  four `∀`-hypotheses against its concrete matrix representation,
  whose unitarity is definitional.
- `μ` abstract (Haar probability typeclasses); the concrete Haar
  measure is supplied at T4 instantiation.
- `averagingOperator_adjoint` carries an explicit `[CompleteSpace E]`
  binder (the pinned Mathlib does not synthesize it from
  `FiniteDimensional`); T4's concrete spaces carry the instance.

## What remains on Route B

- **T3** — word/tensor bookkeeping: joint tensoring absorbs the
  rectangular pairing (charter kill condition: if joint tensoring
  does not suffice, stop and reprice).
- **T4** — assembly through the integrated criterion of Route C
  (`osForm_nonneg_of_gram_integrated`), discharging Stage 1b-B at
  general `(G, ρ)` for `β ≥ 0`. Landing label if the route closes:
  "Stage 1b-B STANDS WHOLE."
