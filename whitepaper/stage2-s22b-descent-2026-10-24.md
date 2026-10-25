# S2-2b — STANDS, All Four Claims: Π₂ Descends, Bounded by Diagonal Domination — and H-pos(2)ʳ Is a Theorem in Factored Form

**Date:** 2026-10-24 · **Seat:** Stage 2 ladder, brick S2-2b (descent + boundedness, priced M–L, the long pole) under the revised gate `stage2-s22-gate-revision-2026-10-24.md`. **Verdict: STANDS — all four discharge claims; no kill fires.** Parent-verified 2026-10-24: targeted build exit 0 on the shipped text, strict recount 21, olean confirmed, zero `sorry`/`admit`, headline axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label untouched.

## The four claims (module `LatticeSliceDescent`, 21 strict / 2 defs)

- **(D-desc)ʳ STANDS.** Π₂ vanishes on Π₁-null vectors in each slot (`slicePairTwo_eq_zero_of_pairOne_self_eq_zero_left/right`, plus the add-null well-definedness forms). Route: a Cauchy–Schwarz inequality for the bilinear form B(f,g) := ⟪f, T g⟫ (`inner_transferOp_cauchy_schwarz`, discriminant argument; diagonal positivity is the single labeled transport of H-pos(1)ʳ along sliceState's defining surjectivity). Key simplification vs the gate's feared route: Π₂(φ,χ) = B(sφ, T sχ) *definitionally* by 2a, so descent is pure CS-B — no representatives, no R3 consumption. Kill (c)ʳ does not fire.
- **(D-bdd)ʳ STANDS in the gate's stated form.** Diagonal domination `slicePairTwo_self_re_le` via a form-level bootstrap (b² ≤ A·a₁ by CS-B at (v, Tv); a₁ ≤ b by ambient Cauchy–Schwarz + contraction; hence b ≤ A — no operator square root, no spectral theory), assembled as `slicePairTwo_norm_le`: ‖Π₂(φ,χ)‖ ≤ √(Π₁(φ,φ).re)·√(Π₁(χ,χ).re). Kill (b)ʳ does not fire.
- **(D-symm)ʳ STANDS** — `slicePairTwo_conj_symm_descended` and the form-level `inner_transferOp_conj_symm`.
- **(D-vac)ʳ STANDS** — `slicePairTwo_one_right` (via `sliceState_one_eq_osVacuum` + the landed `transferOp_vacuum`; side condition 0 < d; **no positivity consumed**).

## The finding (flagged, fenced)

**`sliceHPosTwo_proved`: H-pos(2)ʳ in the gate's factored form is a THEOREM at every real β** — Π₂'s diagonal is ‖T(sliceState φ)‖² by 2a's stepped identity, a norm squared, nonnegative by construction. Kill (a)ʳ (hypothesis growth by iterate) does not fire — no H-pos(k≥3) was needed anywhere.

**What this is not:** it is factored-form positivity only. It is NOT an osForm positivity discharge and NOT an input to Stage 1b-B, whose general case remains OPEN; the OS-form content of two-step positivity is S2-3's concern via (R-C2)ʳ. H-pos(1)ʳ remains an explicit hypothesis (`SliceHPosOne`) in every positivity-carrying headline — the one-step form's positivity is the engine's single remaining assumption-shaped input, exactly as the revised gate designed.

## Census

4,994 → **5,015 strict** · 5,043 → **5,064 attribute-inclusive** · 166 → **167 counted modules** — the corpus crosses 5,000 strict declarations. Seven-sorry qualification unchanged. Remaining S2-2 bricks: 2c assembly (M), 2d regression suite (S–M).
