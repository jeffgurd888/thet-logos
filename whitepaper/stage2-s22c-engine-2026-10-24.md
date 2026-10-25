# S2-2c — STANDS: the Conditional Slice GNS Engine, Assembled

**Date:** 2026-10-24 · **Seat:** Stage 2 ladder, brick S2-2c (assembly, priced M) under the revised gate `stage2-s22-gate-revision-2026-10-24.md`. **Verdict: STANDS — no kill fires, no PARTIAL.** Parent-verified 2026-10-24: targeted build exit 0, strict recount 49, olean confirmed, zero `sorry`/`admit`, package axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. This engine is **not** a Stage 1b-B discharge; H-pos(1)ʳ remains its one explicit hypothesis.

## What landed (module `LatticeSliceEngine`, 49 strict / 11 defs)

- **The quotient is a genuine pre-Hilbert space:** `sliceObsSubmodule` and `sliceNullSubmodule` built, the null space proved equal to the radical of Π₁ (`slicePairOneObs_self_eq_zero_iff_forall`, via 2b's Cauchy–Schwarz and 2a's sesquilinearity), and the quotient carries a real `InnerProductSpace ℂ` instance stack with Π₁ descended by `Quotient.lift₂`. No completion is taken — the gate's construction is the pre-Hilbert quotient, stated as such.
- **The step operator:** `sliceStepObs` (one transfer step on slice observables) with Π₁(χ, step φ) = Π₂(χ, φ); the descended **`sliceHat`** as a LinearMap and bundled CLM, characterized by ⟪[χ], T̂[φ]⟫ = Π₂(χ, φ), with **uniqueness**, **self-adjointness**, the **contraction bound** ‖T̂x‖ ≤ ‖x‖ (via 2b's domination chain), and **positivity in factored form only** (2b's `sliceHPosTwo_proved`, labeled as factored-form everywhere it is consumed).
- **The vacuum:** `sliceOmega` = [1], ‖Ω‖ = 1, T̂Ω = Ω (from (D-vac)ʳ); cyclicity in the gate's sense (the class map is surjective by construction).
- **The package:** `sliceEngine_package` — a single 13-clause conjunction whose hypothesis list is exactly `SliceHPosOne` (H-pos(1)ʳ) plus standing corpus hypotheses; the `0 < d` side condition enters only through the two vacuum clauses, exactly as in 2b's landed interface.

## Where the remaining work plugs in

S2-3's (R-C2)ʳ target *is* a proof of `SliceHPosOne` — the engine consumes it as a hypothesis argument, nothing else changes. Brick 2d (regression suite, S–M) regresses this package at β = 0 against S2-1's `recon_zero_slice_package` (quotient ℂ·Ω₀, T̂₀ = id, Ĥ₀ = 0), under the revised gate's regression kills (d)ʳ/(e)ʳ: a β = 0 mismatch on either seat kills regardless of β > 0 content.

## Build notes (on the record)

(1) `sliceHatCLM`'s type is the inferred CLM type: a bare `→L[ℂ]` ascription makes typeclass search pick the quotient-module topology instance instead of the norm topology (a genuine diamond), so the package asserts the CLM pointwise. (2) `memLp_of_bounded`'s signature in the pinned Mathlib is `(hρcont) (hd) (β) (f) (hfsm) (C) (hC)` — the builder's first assumption about it was wrong and was corrected against source during the build.

## Census

5,015 → **5,064 strict** · 5,064 → **5,113 attribute-inclusive** · 167 → **168 counted modules**. Seven-sorry qualification unchanged. S2-2 bricks remaining: 2d regression suite (S–M) — then the engine ladder is S2-3's (priced M, (R-C2)ʳ route) and S2-4/S2-5 downstream.
