# S2-2a — STANDS: The Engine's Pairings Exist, in the Revised Gate's Exact Form

**Date:** 2026-10-24 · **Seat:** Stage 2 ladder, brick S2-2a (factored pairings, priced M) under the revised gate `stage2-s22-gate-revision-2026-10-24.md`. **Verdict: STANDS at full gate generality; no kill fired.** Parent-verified 2026-10-24: targeted build exit 0 on the shipped text, strict recount 19, olean confirmed, zero `sorry`/`admit`, headline axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label untouched.

## What stands (module `LatticeSlicePairing`, 19 strict / 2 defs)

- **The pairings, as definitions on 𝔸_slice:** `slicePairOne` (Π₁) and `slicePairTwo` (Π₂) — Π₂ by bare iteration of the landed `transferOp` on slice states, nothing else; `twoPointOp` is never referenced (the unlanded `twoPointOp 2 = transferOp²` identity is neither consumed nor implied).
- **Π₁ is the OS form:** `slicePairOne_eq_osForm` (polarized, consuming S1's `osForm_depthOne_transfer_pair`) plus the diagonal form — the revised gate's depth-one consistency (T2.3ʳ) is now *definitional*, not a theorem owed.
- **Π₂ in stepped form:** `slicePairTwo_eq_inner_steps` — Π₂ is the inner product of the two once-stepped states. **Hermiticity of both pairings** at general (G, ρ), every real β, even N (from `transferOp_inner_symm`), and **full sesquilinearity** in all four slots.
- **The β=0 package:** Π₂ = Π₁ at β=0 (`slicePairTwo_zero_eq_pairOne`, from the landed `transferOp_zero_comp_self` — T₀ is idempotent); both pairings at β=0 equal conj(sliceCoord φ)·sliceCoord χ (`slicePairOne_zero`/`slicePairTwo_zero`), labeled on their faces as the gate's §3.7 acceptance-test content for brick 2d to check against `LatticeReconZero`; plus β=0 descent of Π₂ in pairing form (coordinate-null ⇒ Π₂ vanishes).

## Fences held (on the module's face)

Descent of Π₂ at general β is **not** asserted — it remains brick 2b's named claim (D-desc)ʳ. H-pos(1)ʳ/(2)ʳ stay hypotheses; no diagonal positivity is asserted at any β > 0. The plane test is recorded as passed **by exclusion**: the pairings see only `sliceState` images, never the plane. No quantification over `transferOp` on arbitrary L² vectors anywhere.

## What 2b consumes (from the builder memo)

(D-desc)ʳ and the diagonal domination (D-bdd)ʳ are stated against these exact definitions and hypothesis shapes; (D-symm)ʳ's pairing-level input is already landed here; (D-vac)ʳ is reduced to the constant-state fixed-point input from R1.

## Census

4,975 → **4,994 strict** · 5,024 → **5,043 attribute-inclusive** · 165 → **166 counted modules**. Seven-sorry qualification unchanged. Remaining S2-2 bricks: 2b descent + boundedness (M–L, the long pole), 2c assembly (M), 2d regression suite (S–M).
