# Q13 Brick 3 — PARTIAL (One Named Class): The Two-Plaquette Contraction, with the Centered Headline Unconditional

**Date:** 2026-10-24 · **Seat:** gap queue Q13 (Stage 1c-0 clause (ii)), brick Q13-3 (two-plaquette tensor-network contraction, priced M–L) per the re-price charter `stage1c0-q13-reprice-2026-10-24.md`. **Verdict: PARTIAL by case class — the named class only, with its scope boundary proved.** Parent-verified 2026-10-24: targeted build exit 0 on the shipped text, strict recount 52, olean confirmed, zero `sorry`/`admit`, headline axioms standard only.

**NO CLAIM.** Parts of any official Clay statement closed: **0**.

## What stands (module `LatticeContr`, 52 strict / 13 defs)

- **`Contr` is defined** — as `wordContr`, the product over links of the combined fiber integrals of the J-moment data. It is *not* the covariance integral renamed: the identification runs through Q13-2's `covZero_prod_linkEntry` engine, per the frozen Q13-0 interface.
- **Charter (8), both signs, unconditional for all (p, q):** 𝔼₀[W_p·W_q] = Contr⁺ and 𝔼₀[W_p·★W_q] = Contr⁻, with the means in the same J data.
- **The centered headline** `covZero_plaquette_density_eq_contr`: Cov₀(W_p, D_q) = −(1/2d)·((Contr⁺ − 𝔼₀[W_p]𝔼₀[W_q]) + (Contr⁻ − 𝔼₀[W_p]𝔼₀[★W_q])) — in exactly the per-q shape the landed clause-(ii) sum consumes.
- **All four orientations wired** (ρ, ρ^∨ transposed, ρ̄, ρ̄^∨); the six pattern evaluations (0,0)/(1,0)/(0,1)/(2,0)/(0,2)/(1,1) plus `linkContr_classify`; non-sharing plaquettes have covariance zero; the fiber geometry is *proved* (combined fiber card ≤ 2 for μ<ν; card ≤ 1 per word when no shift fixes the base), and `plaqLinkContr_classify_of_not_fixed` discharges the classification at the generic seat.

## The PARTIAL — exactly one class, boundary proved

The *evaluated* twirl-entry form stops for exactly one class: a plaquette base fixed by a transverse shift (σ ν x = x or σ μ x = x — a doubled link) whose doubled link is also read by the other word. There the combined fiber has card 3–4 — a higher Haar moment, i.e. the charter's §5 excluded reading 2, deliberately untouched. **The fiber-integral identities and the centered headline hold for that class too**; only the pair-twirl *evaluation* is unasserted there. The scope boundary is a theorem, not an assumption.

## What remains for Q13-4 (statable, per the builder memo)

C2: substitute the headline into `covZero_plaquetteLoop_eq_sum` to obtain the κ_p form (charter (9)). C1: the circle-seat termwise evaluation recovering κ_p = −1/2 — with one flagged interaction: at d = 1 the doubled-link class is a scalar moment, statable there. C3 guards: rotation invariance; trivial-representation κ_p = 0 via Q13-2's entries-one seat. Pre-registered: **any C1 termwise mismatch is a kill of the assembly, not a patch.**

## Census

4,833 → **4,885 strict** · 4,882 → **4,934 attribute-inclusive** · 162 → **163 counted modules**. Seven-sorry qualification unchanged. Remaining: Q13-4 (assembly + consistency discharge, S–M) — the last brick of the last queue item.
