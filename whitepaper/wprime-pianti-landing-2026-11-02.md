# W′-BRICK LANDING DOSSIER — WeightQuestionW′ ANSWERED YES — 2026-11-02

**Item:** DECISION 2, second half (Jeff, 2026-11-01 23:23 EST):
the re-pose's first registered brick, fired with the
registration under the full-send tempo.

## VERDICT: LANDED FULL — WeightQuestionW′ answered YES at T1; K-W′-REG does not fire

**Artifact:** `lean/ThetLogos/DialOneRegularPiAnti.lean` —
strict 5, defs 0. Verified by the coordinator in the main
tree (build green); all three headlines (and both transport
helpers) on exactly `[propext, Classical.choice, Quot.sound]`.

**Headlines:**
1. `extractionLemma_piAnti : ExtractionLemma piAnti` — at
   joint **(3, 1)**, transported from CLS-1's
   `extractionLemma_pi1` at (3, −1): the matrix equality
   `piAnti (u1ParamGen 3 1 t) = pi1 (u1ParamGen 3 (−1) t)`
   (via the landed `piAnti_eq_pi1_colourTwist` +
   `colourTwist_u1ParamGen` β-flip) carries the determinant
   clause, the lifted-product diagonality, and the
   differentiability of the diagonal entries in one
   congruence. **piAnti is regular.**
2. `dialOneRegular_piAnti : DialOneRegular piAnti`
   (landed `dialOneBase_piAnti` + item 1).
3. `weightQuestionW'_piAnti : WeightQuestionW'` — assembled
   as ⟨piAnti, `strengthenedFam_piAnti`,
   `dialOneRegular_piAnti`, `piAnti_ne_pi1`,
   `weightAt_piAnti_common`⟩, every component previously
   landed except item 2, which this brick supplies.

**What this settles, at exact rank:** the regular-class
refinement of Grade W has the same answer as the original
question — YES, with the same witness. The common weights are
carried by a non-π₁ strengthened point that is regular in the
CLS-1 sense, so the extraction caveat does not separate W
from W′ at the witness that matters. **No measured number is
derived**: piAnti's weights ARE the table's weights
transported through colour conjugation; the table remains
input. Dial 1 = 0. K-CLS-1 (against the original,
regularity-free pose) remains armed and untouched — this
brick does not address whether a *pathological* base π
exists; it shows the standing witness is not one.

## Fences

NO CLAIM; all dials 0/4.

**Census after landing: 12,647 strict / 13,162 total / 447
counted modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
