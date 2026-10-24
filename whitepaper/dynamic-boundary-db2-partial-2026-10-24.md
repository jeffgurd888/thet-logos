# Dynamic Boundary, Brick DB2 — PARTIAL: Expansion Stability in Reduced Form; the Total Identity Killed by Name, Its Factor Exhibited

**Date:** 2026-10-24 · **Charter:** `whitepaper/dynamic-boundary-scoping-2026-10-24.md` (§2.2, reduced form only; the attractor/limit reading was killed at scoping as FRONTIER and is not revived). **Priced M.**
**Verdict: PARTIAL.** Parent-verified 2026-10-24: targeted build exit 0 on the shipped text, strict recount 44, zero `sorry`/`admit`, headline axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label unchanged (U(1) T1 at all β ≥ 0; general (G, ρ) OPEN). No positivity assertion about `Bdry` appears anywhere in the module (the K-DB1(c) fence persists); no limit/attractor/convergence language appears anywhere (K-DB2(c)).

## What stands (T1) — module `LatticeBoundaryExpansion` (44 strict / 12 defs)

- **(b0) The β = 0 control — whole.** `bdry_zero_marginal`: Haar-integrating the trivial boundary weight over either half returns it. `bdry_zero_expansion`: the same trivial weight at sizes N and N + 2 (DB1's `bdry_zero` at both). `configMeasure_map_insLink`: product Haar pushes forward under restriction-along-insertion to product Haar at the old size — the inserted layers genuinely marginalize away at zero coupling. K-DB2(b) did not fire.
- **(bβ) Locality — at a single size.** `wilsonActionZero_congr_seam` / `bdry_congr_seam`: the crossing action and the boundary operator see only seam-neighbourhood links (from the landed `isZeroPlaq_iff`).
- **(bβ) Transport — the reduced form.** Full insertion data (inserted times 1 and r+2; seam times r−1 ↦ r, 2r−1 ↦ 2r+1 for N = r + r), the fold as left inverse on the image, the summand identity `plaquetteDensity_insConfig`, stratum transport `insPlaq_mem_zeroFinset`, the transported-stratum sum identity, and the boundary-level factor corollary `bdry_insConfig_factor`.

## The kill — K-DB2(a), fired on the total-identity reading only

The naive total identity S₀^{N+2}(insert U) = S₀^N(U) is **false in this corpus**, and the module proves exactly why: the size parameter is isotropic — growing N grows the seam's spatial extent too, so the inserted configuration's crossing action picks up an **extra stratum** of plaquettes. `wilsonActionZero_insConfig_decomp` proves the exact decomposition (old action + β·(extra-stratum sum)) and `insert_extra_nonempty` proves the extra stratum is nonempty — the differing factor is exhibited at machine-checked rank, not estimated. The kill's scarier trigger — an inserted-layer plaquette landing inside the crossing action and breaking locality — is **refuted by proof**: inserted-time plaquettes are classified into the half strata (`isPosPlaq_inserted_one`, `isNegPlaq_inserted`) and S₀ is invariant under arbitrary changes at inserted times. Locality survives; the identity doesn't; both facts are theorems.

## Census

4,576 → **4,620 strict** · 4,625 → **4,669 attribute-inclusive** (the module carries no `@[simp]`; the inclusive count rises by the 44 strict, as at every landing) · 154 → **155 counted modules**. Seven-sorry qualification unchanged.
