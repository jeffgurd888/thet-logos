# Q7CR-LOOP-3 — LANDED FULL: the factor-exchange loop. The LOOP line closes

**Verdict: LOOP-3 FULL — (a) energy conservation by form, (b) factor entropy bookkeeping proved, (c) the closure theorem proved under its own name with nontrivial content. The surviving meaning of "self-contained thermal loop" is the factor-exchange form. NO CLAIM. Dials 0/4.**

## The three parts

- **(a) Energy-preserving exchange, by form.** Exchange steps are permutations π of `compIndex` with `eigComp (π x) = eigComp x`, acting on weights by relabeling; `weightEnergy_perm` proves conservation of the composite energy ∑ w x · eigComp x from the stated invariance alone, for any such π and any w. The concrete steps are factor site-pair swaps preserving the factor spectra (Q⁷ sites 0↔1, both a₇² = 9; C⁴ sites 0↔3, both d₄² = 9/64), spectrum preservation proved factorwise.
- **(b) Entropy bookkeeping, in the pure-relabeling form, labeled.** All visited states are product-form; T-ENT additivity is proved for them (`entropyW_prod_three` via the pointwise log-product split, zero weights included), marginals of product states are their factors, and the factor-sum identity holds: the sum of the three factor marginal entropy changes = the total composite entropy change (`exchange_entropy_bookkeeping`). Production: these steps are pure relabelings — each step's defect and entropy-change terms are exactly 0, so total production is 0. The memo's conditional clause for defect-carrying steps is explicitly NOT instantiated or claimed.
- **(c) Closure, under a new name — with the distinction proved real.** `exchangeData`: step 1 swaps the Q⁷ and C⁴ pairs (ledger fields c4), step 2 swaps Q⁷ back only (ledger fields r4) — no ledger term carried by q7. The Q⁷ marginal returns exactly; `LedgerClosed` holds with stated total 0; external work = 0; and the content is nontrivial: the final C⁴ marginal differs from its initial value whenever v(3,0) ≠ v(0,0) (`exchange_c4Marg_ne`), with a fully concrete basis-weight instance (`exchange_concrete_factorSelfContained`). The result is registered as **`FactorSelfContainedLoop`** — a NEW name defined in this module — because LOOP-0's `SelfContainedLoop` requires full composite `StateClosed`, and `exchange_not_stateClosed` PROVES full StateClosed fails for this very data. LOOP-0's name is not spent on the weaker statement; the distinction is a theorem, not a label choice.

## The LOOP line, closed (the three readings, separated forever)

- **Autonomous** (LOOP-1): a self-contained autonomous thermal loop is trivial or nonexistent — the no-go is a theorem, with the clock separation enforced by its statement.
- **Protocol** (LOOP-2): the graded protocol is IndexClosed by construction and LedgerClosed with proved additivity, while its Gibbs state is measurably moved at the first grade — index closure is not state closure, exhibited.
- **Factor-exchange** (LOOP-3): the surviving meaning — energy conserved by form, entropy booked factor-by-factor, the working factor returned exactly, production carried on the other factors' ledgers, no external work.

## Parent verification (from disk)

- Module `lean/ThetLogos/Q7C4R4LoopExchange.lean` (NEW): canonical counter **strict=30, defs=14**, zero attribute lines, zero "sorry"/`native_decide` tokens.
- Parent build green (3,733 jobs). Parent axiom check: `weightEnergy_perm`, `exchange_entropy_bookkeeping`, `exchange_factorSelfContained`, `exchange_not_stateClosed`, `exchange_concrete_factorSelfContained` each on exactly `[propext, Classical.choice, Quot.sound]` (builder's check covered 14 headlines, same result).

## Census

9,090 → **9,120 strict** / 9,168 → **9,198 attribute-inclusive** / 313 → **314 modules** (delta +30 strict, +1 module).

## Backers since last landing

No change to the backer roll since the last landing.
