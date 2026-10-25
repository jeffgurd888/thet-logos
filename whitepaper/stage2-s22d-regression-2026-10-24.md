# S2-2d — STANDS: the β = 0 Regression Suite (S2-2 Complete)

**Date:** 2026-10-24 · **Seat:** Stage 2 ladder, brick S2-2d (regression suite, priced S–M) under the revised gate `stage2-s22-gate-revision-2026-10-24.md`. **Verdict: STANDS — agreement on both seats; the regression kills (d)ʳ and (e)ʳ do not fire.** Parent-verified 2026-10-24: targeted build exit 0, strict recount 15, olean confirmed, zero `sorry`/`admit`, package axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Not a Stage 1b-B discharge.

## What landed (module `LatticeSliceRegression`, 15 strict / 0 defs)

- **The fence question answered by discharge, not assumption:** `sliceHPosOne_zero` proves `SliceHPosOne` at β = 0 from landed material alone (the β = 0 diagonal of Π₁ is ‖coord φ‖², via 2a's `slicePairOne_zero`). Every engine object in the suite is instantiated with this discharged term — the hypothesis appears as an assumption in no theorem of the suite. At general β it remains S2-3's business, untouched.
- **Slice seat — full agreement with S2-1's `recon_zero_slice_package`, on the engine's own objects:** class inner product = conj(coord a)·coord b; null submodule = ker coord; every class is coord a • Ω, so the quotient is ℂ·Ω₀ with `sliceCoord_surjective` carried verbatim; **T̂₀ = id** as a linear map on the engine space (via 2c's uniqueness and 2a's Π₂ = Π₁ at β = 0); vacuum clauses ‖Ω‖ = 1 ∧ T̂₀Ω = Ω; the Ĥ₀/exp(−Ĥ₀) package reproduced in S2-1's phrasing, with a bridge clause tying the coordinate operator `transferHatZero` to the engine's T̂₀; S2-1's bundle itself restated verbatim as a package clause.
- **Strict seat — full agreement:** every §3.7 item re-proved verbatim from S2-1 (pairing, diagonal nonnegativity, null = ker strictState, surjectivity, and `strict_transferHat_pairing` — the same `transferHatZero` carries both seats). Nothing needed re-scoping; (e)ʳ's PARTIAL fallback is not invoked.
- **Headline:** `sliceRegression_package` — a 16-clause conjunction bundling the discharge, all slice-seat agreements, the Ĥ₀/exp clauses, S2-1's bundle, and all strict-seat agreements.

## S2-2 complete

With 2d landed, the S2-2 brick set is complete under the revised gate: **2a pairings (19) + 2b descent (21) + 2c engine (49) + 2d regression (15) = 104 strict** over four modules. The revised gate's design bet is now fully cashed: the engine was assembled under exactly one hypothesis (H-pos(1)ʳ), its β = 0 shadow was verified clause-by-clause against the pre-kill ground truth on both surviving seats, and the hypothesis the engine waits on is precisely S2-3's target.

## Census

5,064 → **5,079 strict** · 5,113 → **5,128 attribute-inclusive** · 168 → **169 counted modules**. Seven-sorry qualification unchanged. Next on the ladder: S2-3 (priced M) — the (R-C2)ʳ route: discharge `SliceHPosOne` at the U(1) seat for all β ≥ 0 from Route C's `osForm_circle_nonneg` (LatticeGramSeries) via 2a's Π₁ = osForm identity, instantiating the engine hypothesis-free at that seat; fallback (R-C2′)ʳ per the gate if the direct transport's observable class mismatches.
