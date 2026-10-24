# Gram clause, Route B, step T4b — assembly part 2: the mirror side

**Date:** 2026-10-23. **Module:** `lean/ThetLogos/GramMirror.lean`
(984 lines, namespace `ThetLogos.GramMirror`, importing
`ThetLogos.GramAssembly`). **Parent-verified:** fresh rebuild on the
shipped text (exit 0, new .olean), recount **32 strict / 15 defs**,
sorry census **0**, parent-run `#print axioms` on the memo's
headlines — standard axioms only. Charter:
`gram-clause-scoping-2026-10-23.md` §4 Route B step T4 (parent split:
T4a landed, this is T4b, T4c remains).

## What stands (T1)

**Mirror stratum anatomy.** `negStratumLinks = negLinks ∩ planeLinks`;
the negative half splits disjointly as `mirrorStrictLinks ∪
negStratumLinks`, and `splitNegEquiv` is a measure-preserving
measurable equiv at `haarProb G` (`measurePreserving_splitNegEquiv`)
— the mechanical mirror of GramAssembly §1.

**The dual-word γ identity — held as stated.** For a crossing-word
datum `(slot, flag, a, b)` over the positive stratum, the dual datum
transports slots by the link reflection composed with `Fin.rev`
order-reversal, flips flags under the same reversal
(`flagRevComp`), and swaps endpoints. Headline `dual_gamma`: the
conjugated stratum integral of the dual word entry **equals**
`wordGamma ρ slot flag a b`, the A-side coefficient. Proved by a
per-path term identity — endpoint conditions transported under
`Fin.rev`, path reversal on the dual side, conjugation moved across
T2's self-adjoint averaging operator, reindexing by `pathRevEquiv`,
closure by `wordGamma_eq`. This is the step that forces the **same**
strict-half feature Ξ out of both marginals of the integrated
criterion.

**Mirror features.** `featB` — the mirror scalar factor (through
`mirrorP`'s strict factorization, `mirrorP_eq_mirrorStrictMap`) times
the conjugated dual word entry — with `featB_marginal` in the
criterion's exact `hmargB` shape, damping factor `dB = 1`, pairing
with the **same** `featXi` as T4a, plus the `hBA`/`hBB`-shape
companions (`featB_aestronglyMeasurable`, `featB_norm_le`, bound
`Cφ`).

## Bookkeeping note

The builder's scratch axioms file listed one headline name
(`dualStratum_integral_wordEntry`) that does not occur in the shipped
module — an intermediate name from an earlier draft. Every headline
named in the verdict memo itself exists in the shipped text and was
parent-verified. No theorem content is affected.

## What remains — step T4c (the closer)

The concrete crossing features from the expansion of `exp(−S₀)`
(the plaquette word data and sandwich factors of `wilsonActionZero`),
the Gram series identity `hgram`, the domination `hsum`, and the
final application of `osForm_nonneg_of_gram_integrated`. Landing
label until T4c: Stage 1b-B positivity is T1 for U(1); at general
(G, ρ) it remains **open**.

## Disclosed

Pointwise-hypothesis style inherited: representation continuity
enters as the explicit `hρcont` binder, as in T4a. One headline's
section variables are pinned by name (elaboration necessity, not a
statement change).

**NO CLAIM.** Parts of any official Clay statement closed by this
module: 0. Program census after this landing: **4,299 strict**
(4,238 attribute-inclusive), **141 counted modules**, the
seven-sorry qualification unchanged.
