# Gram clause, Route B — step T3: word/tensor bookkeeping

**Landed 2026-10-23, parent-verified.** Module:
`lean/ThetLogos/GramWordTensor.lean` (1,076 lines). Charter:
`whitepaper/gram-clause-scoping-2026-10-23.md` §4 Route B, step T3;
fences §5.

## Verdict: T3 STANDS WHOLE (T1) — the kill condition did not trigger

Chartered content: *"crossing plaquette words as tensor-representation
matrix coefficients; joint stratum integral = A applied (the
rectangular pairing of the dossier's counterexample 2 is absorbed by
tensoring both stratum factors — T0 confirms the joint, not
per-plaquette, tensoring suffices)."* Both items proved against the
corpus's actual definitions:

**(a) Words are joint tensor-representation coefficients.**
`tensorMat` (multiplicative, unitary-valued, traces multiply over
slots); `conjRep` carries inverse factors
(`repMatrix_inv_entry`: an inverse factor is a conjugate-rep
coefficient with indices swapped); the joint occurrence
representation `occRep` of the stratum product group `ι → G`; the
path formulas `pathSum_eq_sum_paths` / `pathSum_ofFn_eq_sum_paths`.
Headline **`word_entry`**: a word in signed slot factors is a finite
path sum of matrix coefficients of the *single* joint occurrence
representation — both stratum factors tensored together, the
per-plaquette treatment nowhere.

**(b) The joint stratum integral is T2's A applied.**
`occRepCLM` realizes the occurrence representation as a continuous
linear map on `EuclideanSpace ℂ (κ → Fin d)` with its own rep laws,
continuity, and unitarity. Headline **`integral_occMat_eq_averaging`**:
the integral of an occurrence coefficient over the product Haar
measure is the inner product against T2's averaging operator `A`
applied to the joint occurrence CLM. Headline
**`integral_word_entry`**: a word entry's stratum integral is the
finite path sum of `A`-coefficients at the path endpoints — the
rectangular pairing stays absorbed in the joint representation
end-to-end.

## Verification (parent, on the shipped text)

- Targeted build `lake build ThetLogos.GramWordTensor`: EXIT 0
  (3,397 jobs), fresh `.olean`.
- Recount (house rule): **43 strict** theorem/lemma declarations,
  **11 defs**; sorry census **0**, admits **0**.
- `#print axioms` (parent-run) on the ten headline declarations:
  each depends only on `[propext, Classical.choice, Quot.sound]`.

Program census after this landing: **4,247 strict / 4,238
attribute-inclusive, 139 counted modules** (the module's five
`@[simp]` attributes sit on their own lines above already-counted
declarations, so the attribute-inclusive total is unchanged).

## Disclosed accommodations (builder's record)

- Pointwise-hypothesis style throughout, as T2: `μG` an abstract
  Haar probability; `G` carries compact-group/Borel instances plus
  `[SecondCountableTopology G]` (for `Pi.borelSpace` on `ι → G`);
  continuity of the per-occurrence `repMatrix` is a hypothesis
  (`hΨcont`/`hρcont`), inverse-factor continuity proved via `conjMat`.
  Instantiating at the lattice group is T4's job.
- `occRepCLM` is a new CLM realization, proved equal to the
  occurrence representation at the level of matrix coefficients
  (`occRepCLM_inner_basis`), not a definitional unfolding.
- `pathSum_ofFn_eq_sum_paths` is proved by direct induction on `n`
  (transport along `List.length_ofFn` provably fails — the length
  occurs inside the path types); disclosed in its docstring.

## What remains on Route B

- **T4 — assembly:** features Ξ on the strict half, boundedness and
  measurability, series domination across tensor powers, and the
  discharge through Route C's integrated criterion
  (`osForm_nonneg_of_gram_integrated`): OS positivity at every
  β ≥ 0, general (G, ρ). Landing label if the route closes:
  **"Stage 1b-B STANDS WHOLE."**
