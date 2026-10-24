# Gram clause, Route B, step T4b′ — occurrence features, mirror side

**Date:** 2026-10-24. **Verdict: LANDED, parent-verified.**
Module: `lean/ThetLogos/GramMirrorOcc.lean` (623 lines; imports
`ThetLogos.GramAssemblyOcc`, `ThetLogos.GramMirror`). Parent
verification: fresh targeted build EXIT 0 (3,448 jobs — the same
job count the builder reported), recount **19 strict / 5 defs**,
0 sorry / 0 admit, 0 same-line `@[simp]` declarations, parent-run
`#print axioms` on four headlines standard-only (`propext`,
`Classical.choice`, `Quot.sound`).

Program census: **4,339 strict / 4,388 attribute-inclusive / 143
counted modules**.

## What was built

1. **Mirror arc datum.** `arcSlotNeg := dualSlot hN (arcSlot hpC
   hpA)` — slot 0 is the stratum mirror of `linkA`, slot 1 the
   mirror of `linkC`; `arcΨNeg` flavors swapped under reflection
   (slot 0 is ρ, slot 1 is `conjRep ρ`). Upper-plane membership from
   `zero_link_pattern` (`linkA/linkC_mem_negStratumLinks`).
   Endpoint convention pinned by proof (`occArcNeg_apply`): at
   `(![i, j], ![a, k])` the coefficient is
   `(ρAᵐ)_{i a} · (ρCᵐ⁻¹)_{k j}` — the upper plane's sandwich
   monomial.
2. **The coefficient identity** — the occMat analogue of
   `dual_gamma`, with no path sums: `occGamma_conj_symm`
   (conjugation swaps γᵒᶜᶜ's endpoints, via T2's adjointness), then
   `occGamma_dual_conj` on the landed `integral_occMat_dual`, and
   the headline `occGamma_arc_dual_conj`: the conjugated mirror
   coefficient integrates to **exactly T4a′'s** `occGamma` of the
   arc datum.
3. **Features.** `featBOcc` in `featB`'s shape (scalar factor
   through `mirrorStrictMap`); `featBOcc_marginal` in the
   criterion's exact `hmargB` shape with `dB = 1`; and the pairing
   headline **`featBOccArc_marginal`**, whose right-hand side is
   literally the same `featXiOcc` of the arc datum that T4a′'s
   `featAOcc_marginal` produces — the same function, not a parallel
   copy. Companions: continuity, `hBB`-shape norm bound (same Cφ
   form), `hBA`-shape AE strong measurability,
   `featBOccD_stronglyMeasurable` for the concrete phiD feature.

With both marginals in hand against one shared `featXiOcc`, the
occurrence family is fully assembled for the closer.

Landing label unchanged: Stage 1b-B positivity T1 for U(1);
general (G, ρ) OPEN — one step remains: T4c′ (the concrete family
over `wilsonActionZero`'s crossing plaquettes × tensor powers, the
Gram series identity `hgram` — which holds by construction for the
occurrence family — domination `hsum`, and the discharge).

**NO CLAIM.** Parts of any official Clay statement closed: 0.
