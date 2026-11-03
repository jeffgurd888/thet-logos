# GATE-0 ITEM 6 — PAIRINGS PACKAGE LANDING DOSSIER — 2026-11-03

**Item:** GATE-0 item 6's remaining package feeding the
discharged GATE-4C conditional
(`seatSchurTarget_of_approxProductStep_gate4c_proved`):
the positive/mirror off-diagonal pairing assembly and
the `hIntStage`/`hIntLim` seat instances. **Commission:**
Jeff 2026-11-02 ("run them"), re-fired 2026-11-03
("build and run"). Built in the isolated worktree lane
`~/workspace/thet-logos-item6`, branch `item6-lane`,
from main-tree HEAD `459c3c5`; NOT integrated — the
parent runs the ceremony.

## VERDICT: PARTIAL (at full rank)

Landed whole: the off-diagonal fiber identity (the
sesquilinear G2b), the `hIntLim` instances, and the
`hIntStage` instances — the last two verbatim in
GATE-4C's hypothesis-5 / hypothesis-4 shapes, under
the one added hypothesis the GATE-4C dossier itself
named for this entry (`Continuous fun g => repMatrix
ρ g`), plus, for `hIntStage`, factor measurability and
boundedness carried on the data.

Landed conditionally: the hypothesis-6 pairings
themselves. They are proved from `LayerKernelPos` +
the banked `hMarg` + five per-pair named inputs that
are landed NOWHERE: the two dressed product
integrabilities, the two cross identities (the
pos-dressed and mirror-dressed fiber averages agree —
marginal and folded), and the folded fiber average's
gauge invariance. No pairing was restated to make it
pass; no kill fired (nothing here disproves a
pairing — the cross identity is unproved, not false).
`hMarg` is NOT discharged by this package and NOT
added to GATE-4C, whose statement is untouched.
W3 (`seatSchurProductStepOpen`) is NOT closed by
this package. NO CLAIM; dials 0/4.

Module: `lean/ThetLogos/Span3SeatSchurGateItem6.lean`
— **15 strict theorems + 1 def, zero sorrys**;
targeted build green and warning-clean (the only
build warnings are pre-existing ones in dependency
modules); `#print axioms` on all 15 headlines returns
exactly `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`. Per the gate-module house pattern the
module is not in the root import list; it is verified
by targeted build.

## Per-pin verdicts

### P0 — sesquilinear layer pairing: LANDED (def)

`layerPairing₂ μG ρ β F₁ F₂` — the two-argument form
of the landed `layerPairing` (first observable in the
conjugated slot, second in the plain slot);
`layerPairing₂_self`: on the diagonal it is
`layerPairing` by definition (`rfl`).

### P1 — off-diagonal fiber identity: LANDED (conditional on banked inputs)

`seatPairing_pullTop_eq_layerPairing₂_fiberAvg_of_integrable_marg`
— for DIFFERENT observables `a`, `b`, under `hInt`
(the `(a, b)` product integrability) and `hMarg`
(GATE-2's banked splice disintegration, carried as a
hypothesis exactly as GATE-2 banked it):

`seatPairing μG (pullTopKernel μG ρ hN β) a b
  = layerPairing₂ μG ρ β (fiberAvgTop μG hN b)
      (fiberAvgTop μG hN a)`

(the second observable's fiber average sits in the
conjugated slot). GATE-2 landed only the diagonal
`a = b` form; this is the off-diagonal assembly the
hypothesis-6 pairings consume. Engine:
`seatPairing_pullTop_eq_iter_of_integrable₂` (the
two-observable form of GATE-2's G2a engine; Fubini,
the iterated swap, `layerKernel_symm`).

### P5 — `hIntLim` instances: LANDED

`hIntLim_of_continuous_repMatrix` — verbatim
GATE-4C hypothesis 5: for every AEStronglyMeasurable
bounded `f`, both target integrands (marginal form
and half-action-folded form) are `Integrable` on the
product configuration space. Sole added hypothesis:
`hρcont : Continuous fun g => repMatrix ρ g`.
Stock consumed: `measurable_planeCrossingMarginal`,
the twirl measurability/bounds, `layerKernel_norm_le`
on both pulled kernels (the marginal factors as top
times bottom, `planeCrossingMarginal_eq_pull_mul`),
and this module's folded-weight bound
`norm_exp_neg_halfActionP_le` (via
`abs_halfActionP_le_two`, which — unlike the landed
`GramAssemblyWord.abs_halfActionP_le` — needs no
`0 < d` hypothesis, the pointwise density bound
`|plaquetteDensity| ≤ 2` being unconditional).

### P6 — `hIntStage` instances: LANDED (for data carrying factor regularity)

`hIntStage_of_continuous_repMatrix` — verbatim
GATE-4C hypothesis 4 (the inner ∀-statement over
`f`, `n`, `i`), under `hρcont` plus data hypotheses
on the face: `hφm : ∀ n i, Measurable (φ n i)` and
`hφb : ∀ n i, ∃ C, ∀ u, ‖φ n i u‖ ≤ C`. Item 1's
frozen data carries neither property (the GATE-4C pin
finding), so this instance serves data that does —
as the compression route's finite stages would. The
joint kernel measurability is this module's
`aestronglyMeasurable_pullTopKernel` (under `hρcont`,
through `measurable_layerAction` and the measurable
extractions `measurable_tauTop`/`measurable_tauBot` —
the joint measurability the GATE-4 pin finding found
landed nowhere at the pin's generality).

### P2 — marginal pairing: LANDED modulo named inputs

`seatPairing_dressed_marginal_nonneg_of_cross` — at
`4 ≤ N`, under `LayerKernelPos` + `hInt` + `hMarg` +
**`hCross`** (`fiberAvgTop` of the pos-dressed
observable equals `fiberAvgTop` of the
mirror-dressed observable), hypothesis 6's first
conjunct holds: P1 rewrites the pairing as the
sesquilinear layer pairing of the two dressed fiber
averages, `hCross` collapses it to the diagonal, and
the diagonal is nonnegative by `LayerKernelPos` plus
the discharged G2c invariance
(`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved`,
pos conjunct). `hCross` is a named input, landed
nowhere: the two twirls' dressed fiber averages are
not known equal anywhere in the record (the plausible
route — splice equivariance plus the Haar
pushforward — is research-scale, not landed).

### P3 — folded pairing: LANDED modulo named inputs

`seatPairing_dressed_folded_nonneg_of_cross` — same
shape for the half-action-folded dressed observables,
under `LayerKernelPos` + `hIntFold` + `hMarg` +
**`hCrossFold`** (the folded cross identity) +
**`hInvFold`** (gauge invariance of the folded
dressed fiber average — G2c covers only the unfolded
dressed forms). Both are named inputs, landed
nowhere.

### P4 — assembly: LANDED (as a conditional)

`gate4c_hyp6_of_named_inputs` — at `4 ≤ N`, under
`LayerKernelPos` and the banked `hMarg`, hypothesis
6's verbatim ∀-statement holds for every `f`, `φ'`
satisfying hypothesis 6's own prefix AND the five
per-pair named inputs (the two dressed
integrabilities, the two cross identities, the
folded invariance). Nothing is restated away.

## What GATE-4C can now consume

- Hypothesis 5 (`hIntLim`): **discharged** by P5 in
  the regular case (`Continuous repMatrix`). No other
  input.
- Hypothesis 4 (`hIntStage`): **discharged** by P6 in
  the regular case, for factor data carrying
  measurability + boundedness. (GATE-4C's hypotheses
  1–3 — the expansion data itself — remain item 5's,
  untouched by this package.)
- Hypothesis 6 (the pairings): reduced by P4 to five
  named per-pair inputs over the banked `hMarg` and
  the standing `LayerKernelPos`. The off-diagonal
  assembly itself (P1) is landed; what is missing is
  the cross identity (both forms), the folded
  invariance, the two dressed integrabilities as
  standalone facts, and `hMarg`.

## What remains open (unchanged fences)

- **`hMarg`** — GATE-2's banked splice disintegration;
  belongs to the G2b discharge route. Not in this
  package, not in GATE-4C.
- **The cross identities** (`hCross`, `hCrossFold`)
  and **folded invariance** (`hInvFold`) — unlanded;
  the cross identity is the substantive remaining
  analytic input for hypothesis 6.
- **Item 5** — the expansion data (GATE-4C hypotheses
  1–3) and its own hIntStage-shaped consumptions;
  separate lane, core chain single-lane.
- **W3** — re-reads after items 6 and 5; not closed
  here.
- The frozen GATE-4 / item-6 statements stand
  unedited and unproved, as registered.

## Verification record

- Worktree `~/workspace/thet-logos-item6`, branch
  `item6-lane`, base `459c3c5` (Brick 1 ceremony
  commit; main tree has since advanced — no rebase,
  parent integrates).
- `lake build ThetLogos.Span3SeatSchurGateItem6`:
  green; no errors and no warnings originating in
  this module.
- Strict count (theorem/lemma at column 0,
  comment-stripped): **15**, plus 1 def
  (`layerPairing₂`). Zero `sorry` tokens in the file.
- `#print axioms`: all 15 headlines depend on exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- NO CLAIM. Dials 0/4. Nothing public shipped from
  this lane.

## CEREMONY (parent, main tree, 2026-11-03)

- Lane files copied byte-identical from worktree
  `~/workspace/thet-logos-item6` (branch `item6-lane`, commit
  `dc2219e`) into the main tree at local HEAD `0289e82`
  (Triplets ceremony commit); identity verified by diff.
- Targeted main-tree build
  `lake build ThetLogos.Span3SeatSchurGateItem6`: **green**
  (3669 jobs), zero sorrys (no `sorry` token in the module);
  no errors or warnings originating in this module (the only
  build warnings are pre-existing linter warnings in
  dependency modules).
- Independent strict recount of the module (method of record:
  comment/string-stripped, `^(theorem|lemma)\s` at column 0):
  **15 strict + 1 def**, matching the lane count exactly.
- Axiom fence: all 15 headlines admitted to
  `lean/scripts/axiom-fence.txt` WITH their import line
  (`import ThetLogos.Span3SeatSchurGateItem6`) in the SAME
  commit as the module file, per the standing CI lesson.
  Official runner: **FENCE PASS 70/70** (55 → 70) — every
  admitted headline, old and new, on exactly
  {propext, Classical.choice, Quot.sound}, no sorryAx.
- Corpus census (method of record; shipped chain):
  12,907 / 13,433 / 467 → **12,922 strict / 13,448 total /
  468 modules**, zero sorrys. Whole-tree cross-check:
  counted files-true 12,920 = shipped minus the documented
  +2 ledger overstatement of census-reconciliation-2026-11-02,
  unchanged by this landing — restating the public census
  remains Jeff's open decision. README prose census updated
  (12,907 → 12,922 declarations; 467 → 468 modules); the
  README badge was NOT touched (Jeff's pending decision).
- Ledger record `gate-item6-pairings-package` (partial,
  T3) added with the PARTIAL verdict on its face; validator
  PASS, 13 records conform.
- Verdict stands as landed: **PARTIAL** — P1/P5/P6 landed
  (P1 conditional on banked hInt + hMarg); P2/P3/P4 landed
  modulo the five named inputs; no kill fired; `hMarg`
  open on its own route; GATE-4C's statement untouched and
  NOT discharged or fired by this package; W3 stays open.
  NO CLAIM; dials 0/4.
