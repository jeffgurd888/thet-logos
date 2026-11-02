# W′-PIN LANDING DOSSIER — WeightQuestionW′ REGISTERED (CLS-1b re-pose) — 2026-11-02

**Item:** DECISION 2, first half (Jeff, 2026-11-01 23:23 EST):
register the WeightQuestionW′ re-pose from the CLS-1a/1b
scoping memo (`routeb-general-scratch/scoping-cls1ab-2026-11-02.md`
§2.3/§3), corrected against CLS-3c-A's landed answer.

## VERDICT: REGISTERED — the re-pose is in the tree as a new pin entry; the CLS-0 pin stands unedited

**Artifact:** `lean/ThetLogos/DialOneRegularPin.lean` — strict 1,
defs 3. Verified by the coordinator in the main tree (build
green, 3537 jobs); the read-back headline on exactly
`[propext, Classical.choice, Quot.sound]`.

**Frozen:** `DialOneRegular π := DialOneBase π ∧
ExtractionLemma π`; `WeightRealizable' w := ∃ π,
DialOneStrengthenedFam π ∧ DialOneRegular π ∧ weightAt π w`;
`WeightQuestionW' := ∃ π, DialOneStrengthenedFam π ∧
DialOneRegular π ∧ π ≠ pi1 ∧ weightAt π commonWeightVector` —
the memo's §2.3 forms verbatim, at the landed names. Read-back:
`regular_has_weights` (extraction over the regular class is
FULL, citing CLS-1's landed `extraction_of_extractionLemma`).

## The correction, on the pin's face (why this registration is not the memo verbatim)

1. **The memo's status sentence is superseded.** The memo
   posed W′ while "`WeightQuestionW` (CLS-0) remains open and
   unanswered." **CLS-3c-A then answered the original
   WeightQuestionW YES** (`weightQuestionW_piAnti`: piAnti is
   strengthened, ≠ π₁, and carries the common weights). A
   re-pose that ignored that answer would be VOID; the pin
   therefore registers W′ as **the regular-class refinement of
   an answered question**. What W′ still asked at registration
   that CLS-3c-A did not settle: whether the YES witness (or
   any non-π₁ strengthened point) is **regular** — piAnti's
   `ExtractionLemma` was the unsettled conjunct. (The brick
   fired with this registration settles it — see the companion
   dossier `wprime-pianti-landing-2026-11-02.md`.)
2. **K-CLS-1a has FIRED since the memo**
   (`DialOneConjugationCounterexample.lean`): `DiagLift` is
   NOT a consequence of `DialOneBase`, so `DialOneRegular`'s
   `ExtractionLemma` conjunct is known-genuine extra input.
   Cross-sign diagonality is T1 (`DialOneCrossSign.lean`); the
   diagonality content is within-sign only.
3. **K-CLS-1 remains armed against the original pose**,
   exactly as the memo registered; K-W′-REG is registered on
   the pin: a proof of `¬ ExtractionLemma piAnti` would kill
   the piAnti route to W′ (W′ itself would reopen on other
   witnesses, not die).

## Fences

NO CLAIM; **Dial 1 = 0**; all dials 0/4. Registration derives
no measured number — piAnti's weights are the table's weights,
transported; the table remains input.

**Census after landing (with the companion brick):
12,647 strict / 13,162 total / 447 counted modules; zero
`sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
