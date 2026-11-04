# W3 REMAINDER R2c — `hInvFold` LANDING DOSSIER — 2026-11-03

**Item:** brick R2c of the W3 remainder package
(scoping dossier `w3-remainder-scoping-2026-11-03.md`
§2/R2c, correction 4): discharge `hInvFold`, the
folded invariance input among the five per-pair named
inputs that GATE-0 item 6's assembly
(`gate4c_hyp6_of_named_inputs`) carries for GATE-4C
hypothesis 6. **Commission:** Jeff's full-send grant
over the ratified W3 remainder scoping, fired
2026-11-03. Built in the isolated worktree lane
`~/workspace/thet-logos-w3r2c`, branch `w3r2c-lane`,
from main-tree HEAD `b8419d5`; NOT integrated — the
parent runs the ceremony.

## VERDICT: LANDED FULL (the input, at `4 ≤ N`)

`hInvFold` is discharged outright, in the exact form
item 6's folded pairing (P3,
`seatPairing_dressed_folded_nonneg_of_cross`) takes
it as a hypothesis and its assembly (P4) consumes it:

Module: `lean/ThetLogos/Span3SeatSchurGateW3InvFold.lean`
— **1 strict theorem, 0 defs, zero sorrys**;
targeted build green and warning-clean (no warnings
originating in this module; the only build warnings
are pre-existing ones in dependency modules);
`#print axioms` on the headline returns exactly
`[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. Per the gate-module house pattern the
module is not in the root import list; it is verified
by targeted build.

## The landed statement

`fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved`
— at every even `N` with `4 ≤ N`, every `β`, every
strict-half observable `f` and every layer function
`φ'`, with **no hypotheses on `f` or `φ'`** (no
measurability, no boundedness — as with G2c's
unfolded discharge, the invariance needs none):

`GaugeInvariantLayerObs (fiberAvgTop μG hN (fun z =>
  (Real.exp (-(halfActionP ρ β z)) : ℂ)
    * (posGaugeAvg μG f) z * φ' (tauBot hN z)))`

This is verbatim the fifth per-pair input of
`gate4c_hyp6_of_named_inputs`. Consumption was
verified end-to-end in a scratch wiring test (not
shipped): item 6's P3 applied with its `hInvFold`
slot filled by this theorem typechecks with no
adaptation, leaving exactly P3's other three inputs
(`hIntFold`, `hMarg`, `hCrossFold`) as hypotheses.

## Proof route

G2c's discharged pos-conjunct argument
(`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved`)
carried verbatim with one extra factor. Both sides
are unfolded by `fiberAvgTop_eq_spliceTop`; the
bottom extraction collapses on splices
(`tauBot_spliceTop_of_four_le`); the stratum gauge
substitution at the G2c lift `layerGaugeLift γ` is
applied (`measurePreserving_gaugeStratumEquiv` /
`gaugeStratumEquiv`); and under the substitution the
three factors are invariant one by one — the twirl
by `posGaugeAvg_gauge`, the bottom extraction by
`tauBot_gaugePosFun_lift`, and the folded weight by
`halfActionP_gaugePosFun` (landed,
`PlaneCrossingSeparate`: the half action is
invariant under an arbitrary pos gauge function,
hence under the lift). The scoping's correction 4 is
confirmed as priced: the weight is invariant under
exactly the action the argument uses, and no new
machinery was needed.

## Kill status

**K-W3-INVFOLD: NOT FIRED.** The folded dressed
fiber average is not moved by any layer gauge
action. Per the scoping's fence, a failure here
would have been a route kill for P3's diagonal
reduction only — explicitly not K-F2-2; no such
failure occurred, and nothing in this module
certifies any pairing's sign.

## What remains open (unchanged fences)

- **Four of item 6's five named inputs remain
  unlanded:** the two dressed integrabilities
  (R2d+R3a), the marginal cross identity `hCross`
  (R2a), and the folded cross identity `hCrossFold`
  (R2b). Plus the banked `hMarg` (R1). Hypothesis 6
  is therefore NOT discharged; P3 still stands
  conditional on `hIntFold` + `hMarg` + `hCrossFold`,
  now with its invariance input supplied as a
  theorem rather than a hypothesis.
- **W3** (`seatSchurProductStepOpen`) remains OPEN.
  GATE-4C's frozen statement is untouched, and
  nothing here is stated as discharging GATE-0
  item 6 or any part of W3 (K-GATE-4C-2 respected).
- The gate + W3 prove neither FACT nor clause (a);
  `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain
  open (K-F2-4 respected — no sentence here describes
  this landing as progress on any of them).

## Verification record

- Worktree `~/workspace/thet-logos-w3r2c`, branch
  `w3r2c-lane`, base `b8419d5` (main-tree HEAD:
  census 13,086 strict / 475 modules, fence 149/149).
- `lake build ThetLogos.Span3SeatSchurGateW3InvFold`:
  green (3670 jobs); no errors and no warnings
  originating in this module.
- Strict count (theorem/lemma at column 0,
  comment-stripped): **1**, plus 0 defs. Zero
  `sorry` tokens in the file.
- `#print axioms`:
  `fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved`
  depends on exactly `propext`, `Classical.choice`,
  `Quot.sound`.
- One build episode, recorded: the first build
  attempt failed on a single rewrite — the landed
  `halfActionP_gaugePosFun` takes the section
  variable `ρ` as an explicit first argument, which
  the first draft omitted; fixed in-lane, no
  statement changed.
- NO CLAIM. Dials 0/4. Nothing public shipped from
  this lane; no ceremony, no push — the parent
  integrates.

## CEREMONY (parent integration, 2026-11-03)

Integrated from w3r2c-lane `8e9952a` onto main-tree HEAD
`b8419d5` (Q1′′ monotonicity ceremony; census 13,086 / 475,
fence 149/149) — the lane's base IS that HEAD, so no drift
was possible; verified anyway: the module and this dossier
were copied **byte-identical** (md5- and diff-verified) and
no touch of any kind was needed.

- **Build:** main-tree targeted build of
  `ThetLogos.Span3SeatSchurGateW3InvFold` green (3670 jobs,
  matching the lane), zero sorrys, **module warning-clean**
  (every warning in the build belongs to a pre-existing
  dependency module; none names this module).
- **Recount:** module strict **1 + 0 defs**, exact lane match
  (counter re-validated in-run on spot modules:
  MeasuredClockMonotone 6 + 1, PositivityPropagation 43,
  Span3SeatSchurPosBridge 29 + 5). Corpus census (FILES-TRUE,
  method of record): **13,086 / 475 → 13,087 strict / 476
  modules**; README prose census and shields badge both
  updated to 13,087 / 476, kept equal.
- **Fence: PASS 150/150** (149 → 150). The 1 headline
  (`fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved`)
  admitted with `import ThetLogos.Span3SeatSchurGateW3InvFold`
  in the same commit as the module; the headline on exactly
  {propext, Classical.choice, Quot.sound}, no sorryAx.
- **Ledger:** record `w3-r2c-invfold` (standing, T3) — R2c
  FULL; hInvFold discharged at `4 ≤ N`, the fifth of item 6's
  five named inputs; the four remaining inputs plus banked
  hMarg, hyp 6 NOT discharged, W3 OPEN, and
  `gate4c_hyp6_of_named_inputs` untouched, all on its face.
  Validator PASS, 22 records.
- **Commit/push/CI:** recorded in the pipeline log
  (`~/workspace/launch-pipeline-2026-10-29.md`) per house pattern.

Verdict stands FULL at full rank: **hInvFold is discharged
at `4 ≤ N` on the public record** — one of item 6's five
named inputs is now a theorem. K-W3-INVFOLD did not fire.
Hypothesis 6 is NOT discharged; W3 stays OPEN. NO CLAIM;
dials 0/4.
