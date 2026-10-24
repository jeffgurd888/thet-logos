# Gram clause, Route B, step T4a′ — occurrence features, A side

**Date:** 2026-10-24. **Verdict: LANDED, parent-verified.**
Module: `lean/ThetLogos/GramAssemblyOcc.lean` (519 lines, imports
only `ThetLogos.GramAssembly`). Parent verification: fresh targeted
build EXIT 0 (3,446 jobs), recount **21 strict / 10 defs**, 0 sorry /
0 admit in the module, parent-run `#print axioms` on five headlines
standard-only (`propext`, `Classical.choice`, `Quot.sound`).

Program census: **4,320 strict / 4,369 attribute-inclusive / 142
counted modules**. (The attribute-inclusive figure is strict + the
49 same-line `@[simp]` declarations of the 2026-10-18/19 sweep; all
six Route-era modules add zero same-line `@[simp]` declarations —
rechecked at this landing. The README footnote's previous figure,
4,238, was the Route-C-era value carried stale through T2–T4b; it
is corrected to 4,369 at this landing.)

## What was built

1. **The arc datum.** Per crossing plaquette at the lower plane, the
   two-slot occurrence datum into `↥stratumLinks`: slots
   `(linkC, linkA)`, flavors `(flavRep ρ false, flavRep ρ true)`.
   Endpoint convention pinned **by proof** (`occArc_apply`): at
   endpoints `(![k, a], ![j, i])` the coefficient is
   `(ρC⁻¹)_{j k} · (ρA)_{a i}` — `(k, a)` the strict pair, `(j, i)`
   the mirror pair; the two stratum factors share no index, which
   is exactly the T4c sandwich anatomy. Membership from
   `zero_link_pattern`: `linkA_mem_stratumLinks`,
   `linkC_mem_stratumLinks`, `linkD_mem_posLinks`. Tensor powers as
   data over `Fin k × Fin 2` (`arcSlotPow`, `arcΨPow`) for T4c′.
2. **Occurrence features.** `featAOcc φ₀ y = φ₀ (restrictPos y) ·
   occEntry (stratPart y)`; `featXiOcc φ₀ z = occGamma • φ₀ z` with
   `occGamma_eq` computing γᵒᶜᶜ via the landed
   `GramAssembly.stratum_integral_occMat`. **Headline
   `featAOcc_marginal`** in the integrated criterion's exact
   `hmargA` shape, per-datum factor `dA = 1`, proved by the T4a
   template — word-ness was never used. Companions:
   `occEntry_continuous`, `occEntry_norm_le_one` (product of unitary
   entries), `featAOcc_continuous`, `featAOcc_norm_le`,
   `featAOcc_aestronglyMeasurable`.
3. **The strict factor.** `phiD hpD k a w β z = (repMatrix ρ
   ((z at linkD)⁻¹))_{k a} · exp(−halfActionP ρ β z) · (√w : ℂ)` —
   the strict matrix coefficient carried by φ₀, as the criterion's
   pointwise identity requires. Design decision (header-documented):
   the series weight is an explicit real parameter `w`; T4c′
   instantiates it per tensor power. `phiD_norm_le` with **no sign
   condition on β**; `phiD_stronglyMeasurable`;
   `featAOccD_stronglyMeasurable`.

**Bonus at general (G, ρ):** `measurable_halfActionP` — the strict
action's regularity, previously in the corpus only for the circle
representation; proved via `measurable_extendP`,
`measurable_plaquetteDensity`, `measurable_wilsonActionPlus`.

Kill-honesty: no obstruction hit, nothing weakened; the one
signature change *strengthened* a headline (`phiD_norm_le` dropped
a superfluous hypothesis).

Landing label unchanged: Stage 1b-B positivity T1 for U(1); general
(G, ρ) OPEN — Route B continues: T4b′ (B side, via the landed
occMat dual transport), then T4c′ (the closer on the ᵒᶜᶜ family).

**NO CLAIM.** Parts of any official Clay statement closed: 0.
