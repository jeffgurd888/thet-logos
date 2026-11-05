# WB-4 — Confirmed-pair collision renames — LANDING NOTE (2026-11-04)

**Brick:** WB-4, fired under Jeff's "fire all welds" (2026-11-04 20:40 EST), following the weld scoping of the same evening (`~/workspace/your_files/weld-scoping-2026-11-04.md`, Map B, §B-2 CONFIRMED pairs).
**Base:** main-tree HEAD `798c680` (remote `08720768`), in isolated worktree `~/workspace/thet-logos-wb4`. Branch ready for parent integration; **not pushed** (parent serializes integration against WB-1/WB-2 landings).
**Scope:** the CONFIRMED collision pairs only. The 18 SUSPECT pairs are WB-3's arbitration and were not touched.
**NO CLAIM; dials 0/4.** This brick changes names only — no statement, proof, or theorem content was altered (diff: 7 files, 41 insertions / 41 deletions, token-for-token).

## Side rule applied

Per the offered default Jeff accepted: **rename the smaller side** of each pair (fewer declarations/usages at stake, determined by count); if counts are within noise, rename the side NOT in the root-build closure / fence environment. Counts below are column-0 declaration counts (`theorem|lemma|def|abbrev|axiom|instance|structure|class|inductive`) and file lines at base HEAD, re-verified by grep at HEAD before renaming. Every pair was decisive on counts; the tiebreak was needed only as a consistency check on Pair 2 (TritGrading is a direct root import; the renamed side, HermitianReduction, is not).

## Pair 1 — CausalProduct × ProductTriple (4 names)

Colliding names (CausalProduct.lean vs ProductTriple.lean): `ThetLogos.Dprod` (axiom :106 vs def :372), `ThetLogos.ηprod` (axiom :120 vs def :1017), `ThetLogos.ηprod_sq` (axiom :121 vs :1027), `ThetLogos.ηprod_selfadj` (axiom :122 vs :1035). Two rival formalizations of the same product-Dirac package — one axiomatized, one defined.

- **Counts:** CausalProduct 29 decls / 261 lines vs ProductTriple 85 decls / 1283 lines → **renamed CausalProduct** (the axiom side).
- **New names:** `Dprod → DprodCausal`, `ηprod → ηprodCausal`, `ηprod_sq → ηprodCausal_sq`, `ηprod_selfadj → ηprodCausal_selfadj` (38 token replacements in-file; the separate lowercase axioms `dprod_selfadj`, `dprod_noncentral` keep their names, their statements' `Dprod` tokens updated).
- **Files touched:** `lean/ThetLogos/CausalProduct.lean` (1). Kept-side referencing file FactorOrderOne.lean imports ProductTriple only — untouched.
- **Co-import proof:** scratch file importing both modules + `#check` on all eight names — **clean, exit 0**; axiom side resolves as `ProdOp`, def side as `Module.End ℂ (…)`, distinctly.
- **Registry impact:** none (no colliding name in `lean/scripts/axiom-fence.txt`).

## Pair 2 — HermitianReduction × TritGrading (1 name)

Colliding name: `ThetLogos.conj_mul_conj` — HermitianReduction.lean:162 (theorem on matrices over ι, `star U * U = 1` form) vs TritGrading.lean:169 (`U_inv` form). TritGrading is one of the 15 direct imports of the root `ThetLogos.lean` — the landmine sat one import away from the root environment.

- **Counts:** HermitianReduction 16 decls / 445 lines vs TritGrading 42 decls / 350 lines → **renamed HermitianReduction** (also the non-root-closure side).
- **New name:** `conj_mul_conj → conj_mul_conj_herm`.
- **Files touched (3):** `HermitianReduction.lean` (declaration + internal use), `ViscousLine.lean` (9 tokens — code calls `conj_mul_conj _ _ _ hU` matching the renamed side's 3-explicit-arg signature, plus prose), `FluxClassification.lean` (1 prose mention of the qualified name). Both referencing files import HermitianReduction — inside the renamed side's lineage; nothing cross-file references TritGrading's version.
- **Co-import proof:** both modules + `#check` on both names — **clean, exit 0**; the two forms resolve distinctly.
- **Registry impact:** none.

## Pair 3a — LayerCubeDistance × MaxwellQuadSpectrum (2 names)

Colliding names: `ThetLogos.layerShift_coord_self` (LayerCubeDistance:276 vs MaxwellQuadSpectrum:287) and `ThetLogos.layerShift_coord_of_ne` (LayerCubeDistance:282 vs MaxwellQuadSpectrum:279). Same statements, different binder structure (distance side: direction implicit, `(hν) (c)`; Maxwell side: `(ν) (hν) (c)`).

- **Counts:** LayerCubeDistance 26 decls / 601 lines vs MaxwellQuadSpectrum 91 decls / 2866 lines → **renamed LayerCubeDistance**.
- **New names:** `layerShift_coord_self → layerShift_coord_self_dist`, `layerShift_coord_of_ne → layerShift_coord_of_ne_dist`.
- **Files touched (2):** `LayerCubeDistance.lean` (5 tokens), `WavePathShadowDecision.lean` (3 tokens; imports LayerCubeDistance, call signatures match the renamed side). WaveFreqShadowDecision.lean resolves to the kept Maxwell side via WaveModeIdentification — untouched.
- **Co-import proof:** both modules + `#check` on all four names — **clean, exit 0** (first dynamic confirmation for this pair; the scoping had confirmed it by source only).
- **Registry impact:** none.

## Pair 3b — LayerCubeRemainderSeat × MaxwellPoincare (2 names)

Colliding names: `ThetLogos.linkTail_layerLinkOf` (LayerCubeRemainderSeat:275 vs MaxwellPoincare:1023) and `ThetLogos.linkHead_layerLinkOf` (LayerCubeRemainderSeat:282 vs MaxwellPoincare:1030).

- **Counts:** LayerCubeRemainderSeat 23 decls / 373 lines vs MaxwellPoincare 56 decls / 1652 lines → **renamed LayerCubeRemainderSeat**.
- **New names:** `linkTail_layerLinkOf → linkTail_layerLinkOf_seat`, `linkHead_layerLinkOf → linkHead_layerLinkOf_seat`.
- **Files touched:** `LayerCubeRemainderSeat.lean` (1; 4 tokens). No cross-file references exist on either side.
- **Co-import proof:** both modules + `#check` on all four names — **clean, exit 0** (first dynamic confirmation for this pair).
- **Registry impact:** none.

## STOP-LINE audit

No STOP-LINE triggered. Whole-tree token grep at HEAD found every reference to every colliding name inside the two lineages of its pair; the cross-file references found (FactorOrderOne, ViscousLine, FluxClassification, WavePathShadowDecision, WaveFreqShadowDecision) each resolve to exactly one side by import + call signature and were handled as above. No colliding name appears in the fence registry, and none appears in any frozen statement (GATE-3/GATE-4 family untouched).

## Verification (worktree, base 798c680 + this change)

- New-name collision scan before renaming: **zero matches** for all nine new names across `lean/`, including untracked files.
- Targeted builds: pairs 1+2 set (CausalProduct, ProductTriple, HermitianReduction, TritGrading, ViscousLine, FluxClassification) **green, 3,593 jobs**; pair 3 set (LayerCubeDistance, WavePathShadowDecision, LayerCubeRemainderSeat, MaxwellQuadSpectrum, MaxwellPoincare) **green, 3,690 jobs**. Warnings observed are pre-existing linter/deprecation items on lines whose content the renames did not change (unused section variables in HermitianReduction/ViscousLine; unused-variable `hN` in MaxwellPoincare; `if_pos`/`if_neg` deprecations in WavePathShadowDecision).
- Co-imports: all four pairs compile clean with both sides' names resolving distinctly (the defusing proof; pairs 3a/3b dynamically confirmed here for the first time).
- `#print axioms` spot-check on renamed headlines: **nil** — no renamed name is fence-registered, so there is nothing to spot-check; recorded as a nil check, not skipped silently.
- Full build (default target, root closure): **green, 3,325 jobs** (only pre-existing ThreeGen unused-simp-arg lints in the tail).
- Axiom fence re-run at the HEAD registry, **unadjusted** (no renamed name registered): **PASS 479/479** — every registered declaration's axioms within {propext, Classical.choice, Quot.sound}. Count unchanged from base, as expected: renames add no theorems.
- Zero sorry introduced; no `native_decide` used.

## Convention recorded

**Environment collisions are resolved by renaming the smaller side to explicit lineage-specific names** — determined by declaration/usage count, tie-broken against the root-build closure — generalizing the two 2026-11-04 fence-time precedents (the `ThetLogos.Config` duplicate → `BosonicConfig`, and the anonymous seat instances → `seatInst*` names) and the 2026-10-31 `reflSite_eq_torusShift_zero` remediation.

## Process note (honesty)

The first pair-3 targeted build was killed mid-run by a runtime restart (its session's processes confirmed dead, 4 of 5 module artifacts absent) and was re-run from scratch to the green result above; wall-clock throughout was dominated by box contention with the parallel WB-2/WB-3 lanes (4 cores, load ≈13), not by any defect in the change. No other deviations.
