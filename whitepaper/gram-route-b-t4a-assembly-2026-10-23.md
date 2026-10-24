# Gram clause, Route B, step T4a — assembly part 1: instantiation + features

**Date:** 2026-10-23. **Module:** `lean/ThetLogos/GramAssembly.lean`
(476 lines, namespace `ThetLogos.GramAssembly`). **Parent-verified:**
fresh rebuild on the shipped text (exit 0, new .olean), recount
**20 strict / 8 defs**, sorry census **0**, parent-run `#print axioms`
on 9 headlines — standard axioms only. Charter:
`gram-clause-scoping-2026-10-23.md` §4 Route B step T4, split by the
parent into T4a (this step) and the remaining assembly steps after the
first whole-route builder died in its reading phase.

## What stands (T1)

**Instantiation.** The stratum of the closed half is
`stratumLinks = halfLinks ∩ planeLinks`; the closed half splits
disjointly as `posLinks ∪ stratumLinks`, and `splitHalfEquiv` is a
measure-preserving measurable equiv between configurations on the
closed half and (strict half) × (stratum) at the corpus's Haar
probability `haarProb G`. T3's two integral headlines are specialized
to this stratum group and measure with all abstract-measure
hypotheses discharged by the landed `haarProb` instances:
a stratum word entry integrates to T3's `A`-coefficient
(`stratum_integral_occMat`, `wordGamma_eq`).

**Features (A side).** For one crossing-word datum and a strict-half
scalar factor `φ₀`: the word entry `wordEntry` is continuous (a
polynomial in link entries) and bounded by 1
(`repMatrix_entry_norm_le_one` — a row of `M * star M = 1`). The
positive-half feature `featA y = φ₀ (restrictPos y) · wordEntry (stratPart y)`
is continuous, bounded by `‖φ₀‖∞`, AE strongly measurable, and its
stratum marginal is exactly the integrated criterion's `hmargA`
hypothesis shape with damping factor `dA = 1` and strict-half feature
`featXi z = γ • φ₀ z`, γ the word's `A`-coefficient (`featA_marginal`,
proved by transport along `splitHalfEquiv` then `integral_prod_mul`;
unconditional in `f`).

## What does not stand yet — the split, priced

The criterion's second marginal (`hmargB`) pairs mirror-side features
with the **same** `Ξ` through the corpus's `mirrorP`. T4a scoped it
from the criterion's exact statement and did not force it. In
dependency order:

1. Mirror stratum anatomy (`negStratumLinks`, `splitNegEquiv`) —
   mechanical mirror of §1.
2. **The dual-word γ identity** (the content): the conjugate of the
   mirrored word's entry integrates to the same γ — slots transported
   by the mirror, flags flipped under `Fin.rev`, endpoints swapped;
   consumes `mirrorP`'s linkwise definition, T3 on the dual word,
   T2 self-adjointness of `A`, `integral_conj`.
3. `featB` / `featB_marginal` (`dB = 1`) and the `hBA`/`hBB` mirrors.

No obstruction was found. The B side is a second §1+§4-scale
construction and is commissioned as **step T4b**; series domination
and the final discharge through `osForm_nonneg_of_gram_integrated`
become **step T4c**. Landing label for the clause is unchanged:
Stage 1b-B positivity is T1 for U(1); at general (G, ρ) it remains
**open** until T4c lands.

## Disclosed

`β` does not appear in this module (the criterion carries it); no
sign condition is used. `wordEntry_continuous` takes `hρcont` as a
hypothesis, matching T3's pointwise-hypothesis style. `featXi` /
`wordGamma` are `noncomputable`. The criterion was consumed verbatim.

**NO CLAIM.** Parts of any official Clay statement closed by this
module: 0. Program census after this landing: **4,267 strict**
(4,238 attribute-inclusive), **140 counted modules**, the
seven-sorry qualification unchanged.
