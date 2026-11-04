# W3 REMAINDER R2a — `hCross` LANDING DOSSIER — 2026-11-03

**Item:** brick R2a (build stage) of the W3 remainder
package (scoping dossier
`w3-remainder-scoping-2026-11-03.md` §2/R2a):
discharge `hCross`, the marginal cross identity
among the five per-pair named inputs that GATE-0
item 6's assembly (`gate4c_hyp6_of_named_inputs`)
carries for GATE-4C hypothesis 6. The falsity probe
ran first, per the scoping's two-stage discipline
(`w3-r2a-hcross-probe-report-2026-11-03.md`): probe
exhausted in its box (ZMod 2 / ZMod 3 / S₃ seats,
`N ∈ {2, 4, 6}`, exact arithmetic, 3,672 word-grid
comparisons + 102 delta-exhaustive matrix checks),
no counterexample, K-W3-CROSS did not fire — and,
per the GATE-3 precedent recorded there, that
failure to kill was NOT evidence; this build owes
the ∀-statement and lands it. **Commission:** Jeff's
full-send grant over the ratified W3 remainder
scoping. Built in the isolated worktree lane
`~/workspace/thet-logos-w3r2a`, branch `w3r2a-lane`,
from main-tree HEAD `a339fba` (the brief's named
base `1a23a9a` plus the R1 ceremony commit, which
does not touch this brick's dependencies); NOT
integrated — the parent runs the ceremony.

## VERDICT: LANDED FULL (the input, at the consumed form)

`hCross` is discharged outright, in the exact form
item 6's marginal pairing (P2,
`seatPairing_dressed_marginal_nonneg_of_cross`)
takes it as a hypothesis and its assembly (P4)
consumes it per pair:

Module: `lean/ThetLogos/Span3SeatSchurGateW3Cross.lean`
— **8 strict theorems + 2 defs, zero sorrys**;
targeted build green (3646 jobs) and warning-clean
(no warnings originating in this module; the only
build warnings are pre-existing ones in dependency
modules); `#print axioms` on the headlines shows no
axioms outside `[propext, Classical.choice,
Quot.sound]` and no `sorryAx` (four headlines on
the full trio; the link-level lemma on
`[propext, Quot.sound]`). Per the gate-module
house pattern the module is not in the root import
list; it is verified by targeted build.

## The landed statement

`fiberAvgTop_twirled_mul_pullback_cross_proved`
— at every even `N`, every strict-half observable
`f` and every layer function `φ'`, with **no
hypotheses on `f` or `φ'`** and no `4 ≤ N` side
condition (the identity is proved at the level of
the twirls, which need neither):

`fiberAvgTop μG hN (fun z => (posGaugeAvg μG f) z
    * φ' (tauBot hN z))
  = fiberAvgTop μG hN (fun z => (mirrorGaugeAvg μG f) z
    * φ' (tauBot hN z))`

This is verbatim the `hCross` hypothesis of P2.
Consumption was verified end-to-end in a scratch
wiring test (not shipped): item 6's P2 applied with
its `hCross` slot filled by this theorem typechecks
with no adaptation, leaving exactly P2's other
inputs (`hInt`, `hMarg`, `LayerKernelPos`, and the
`hf`/`hfb` prefix) as hypotheses.

## Proof route

Exactly the route the probe's §4 exposed at probe
grade (360/360 finite-seat draws), now verified in
corpus vocabulary at general `(G, μG)`:

1. **Pointwise action identity**
   (`gaugeMirrorPos_eq_gaugePosFun_reflComp`, via
   the link-level `gaugeLinkVal_reflLink`): for
   every gauge function `g` and strict-half
   configuration `z`,
   `gaugeMirrorPos g z = gaugePosFun (g ∘ reflSite) z`
   at every strict-half link. In direction `μ ≠ 0`
   both sides reduce to `g (reflSite x) * v
   * (g (reflSite (σ_μ x)))⁻¹` by the spatial
   commutation `reflSite_torusShift_of_ne`. In
   direction `0` the reflected link is based at
   `y = (σ₀)⁻¹ (reflSite x)`; the mirror's inversion
   branch turns `g y * v⁻¹ * (g (σ₀ y))⁻¹` into
   `g (reflSite x) * v * (g y)⁻¹`, and
   `reflSite_torusShift_zero` identifies the plain
   action's shifted reflected site with the same
   `y`. The inversion branch is the crux, as the
   probe's controls predicted (a branch-free mirror
   disagrees 60/60 at the order-3 and nonabelian
   seats): here it is not an extra case to check
   but exactly what the reflected parametrization
   produces.
2. **Pushforward** (`measurePreserving_gaugeReflPrecompEquiv`):
   precomposition with `reflSite` preserves the
   product Haar measure on gauge functions. The
   instance is `MeasurableEquiv.piCongrLeft` at the
   site permutation (`reflSitePerm`, the involution
   `reflSite` packaged), symmetrized — Mathlib's
   `measurePreserving_piCongrLeft`; the corpus owned
   the pattern (e.g. `measurePreserving_gaugeMulRightEquiv`)
   but not this instance.
3. **Assembly** (`posGaugeAvg_eq_mirrorGaugeAvg`):
   substitute step 1 in the mirror average's
   integrand, then change variables by step 2's
   reparametrization: `mirrorGaugeAvg μG f
   = posGaugeAvg μG f` as functions. `hCross` is
   then congruence on the fiber average.

The build landed at strict 8 + 2 defs, below the
scoping's L estimate (30–80) and below even the
probe's "low end" suggestion — the estimate priced
adaptation friction across the if-branch and a
pi-pushforward instance built from lower-level
parts; the branch arithmetic closed by the landed
shift calculus and `group`, and the pushforward was
a single Mathlib transport away. Disclosed here, as
with R1/R2c's under-estimate landings.

## Kill status

**K-W3-CROSS: NOT FIRED.** The cross identity holds
at every even `N` and for the corpus's general
`(G, μG)` — in fact the twirl equality underneath
it needs no evenness at all. Per the scoping's
fence, a counterexample would have killed the
cross-collapse route for P2/P4 only — explicitly
not K-F2-2; no counterexample exists, and nothing
in this module certifies any pairing's sign.

## What remains open (unchanged fences)

- **Of item 6's five named inputs, one remains
  unlanded after this brick:** the folded cross
  identity `hCrossFold` (R2b) — the same identity
  with the half-action weight carried; the weight
  is invariant under both actions by landed facts
  (`halfActionP_gaugePosFun`,
  `halfActionP_gaugeMirrorPos`), and the
  substitution proved here is its natural candidate
  route, but that is R2b's business, not a result
  of this module. (The two dressed integrabilities
  are R2d+R3a's brick; `hInvFold` landed as R2c;
  `hMarg`'s re-pin landed as R1.) Hypothesis 6 is
  therefore NOT discharged by this module alone;
  P2 still stands conditional on `hInt` + `hMarg`
  (re-pin form) + `LayerKernelPos`, now with its
  cross input supplied as a theorem rather than a
  hypothesis.
- **W3** (`seatSchurProductStepOpen`) remains OPEN.
  GATE-4C's frozen statement is untouched, and
  nothing here is stated as discharging GATE-0
  item 6 or any part of W3 (K-GATE-4C-2 respected).
- The gate + W3 prove neither FACT nor clause (a);
  `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain
  open (K-F2-4 respected — no sentence here
  describes this landing as progress on any of
  them).

## Verification record

- Worktree `~/workspace/thet-logos-w3r2a`, branch
  `w3r2a-lane`, base `a339fba` (main-tree HEAD at
  lane creation: census 13,094 strict / 477
  modules, fence 155/155).
- `lake build ThetLogos.Span3SeatSchurGateW3Cross`:
  green (3646 jobs; the module itself built in
  8.1 s); no errors and no warnings originating in
  this module.
- Strict count (theorem/lemma at column 0,
  comment-stripped): **8**, plus 2 defs. Zero
  `sorry` tokens in the file.
- `#print axioms` on the five headline
  declarations (`gaugeLinkVal_reflLink`,
  `gaugeMirrorPos_eq_gaugePosFun_reflComp`,
  `measurePreserving_gaugeReflPrecompEquiv`,
  `posGaugeAvg_eq_mirrorGaugeAvg`,
  `fiberAvgTop_twirled_mul_pullback_cross_proved`):
  no axioms outside `propext`, `Classical.choice`,
  `Quot.sound`, and no `sorryAx` — the four
  measure/action headlines depend on the full
  trio; `gaugeLinkVal_reflLink` on
  `[propext, Quot.sound]` alone.
- Consumption (scratch wiring test, not shipped):
  item 6's P2 applied with its `hCross` slot filled
  by `fiberAvgTop_twirled_mul_pullback_cross_proved`
  typechecks with no adaptation (exit 0, no
  diagnostics), leaving exactly P2's other inputs
  as hypotheses.
- Build episodes, recorded: (i) a first draft used
  the unknown constant `MeasurableEquiv.coe_symm`
  for the precomposition equiv's apply lemma; the
  identity is definitional in this pin and the
  lemma is proved by `rfl`. (ii) `MeasurePreserving.integral_comp`
  in this pin states the substitution in the
  direction `∫ F ∘ Φ = ∫ F`; the assembly takes
  its symmetric form. (iii) The
  `unusedSectionVars` linter warnings were
  discharged by `omit` blocks carrying the linter's
  own variable lists (placed before the doc
  comments, per the propagation lane's recorded
  pin finding); the fixes cascaded twice — shedding
  instance arguments from
  `gaugeReflPrecompEquiv_apply_fun` exposed three
  further unused instances first at
  `posGaugeAvg_eq_mirrorGaugeAvg`, then at the
  headline — each round closed with the linter's
  verbatim list for that declaration. Theorem
  statements unchanged throughout. (iv) The module
  imports only the homes of the constants its
  statements use (`Span3SeatSchurGatePost` for
  `fiberAvgTop`, the plane-crossing chain for the
  twirls and `tauBot`, `LatticeReflection` for the
  reflection calculus) — not item 6's module, whose
  `hCross` hypothesis type this theorem matches
  without referencing item 6 constants; the
  consumption check above imports item 6
  separately. (v) Wall-clock: this lane's early
  compiles ran under severe multi-lane disk
  contention (a sibling lane's Mathlib rebuild, a
  VM reboot that wiped /tmp scratch, and page-cache
  thrash that starved one build's final compile
  for ~30 wall minutes at ~2% CPU); the import
  trim in (iv) shrank the faulting closure and the
  final targeted build ran clean. No statement was
  changed by any episode.
- NO CLAIM. Dials 0/4. Nothing public shipped from
  this lane; no ceremony, no push — the parent
  integrates.

## INTEGRATION (parent integration, 2026-11-03)

Integrated from w3r2a-lane `97e0d7b` onto main-tree HEAD
`aa04767` (W3 R2b integration; census 13,109 / 479, fence
170/170). The lane was cut from `a339fba`, behind that
HEAD; verified at integration: the module and this
dossier were copied **byte-identical** (md5-verified:
`abb5bd87…` / `5c0e0ce7…`), the module is new, and a
declaration-level scan found **no collision** between
this module's ten names (`reflSitePerm`,
`reflSitePerm_apply`, `gaugeReflPrecompEquiv`,
`gaugeReflPrecompEquiv_apply`,
`gaugeReflPrecompEquiv_apply_fun`,
`measurePreserving_gaugeReflPrecompEquiv`,
`gaugeLinkVal_reflLink`,
`gaugeMirrorPos_eq_gaugePosFun_reflComp`,
`posGaugeAvg_eq_mirrorGaugeAvg`,
`fiberAvgTop_twirled_mul_pullback_cross_proved`) and
any declaration in the main tree — no frozen statement
was renamed.

- **Disposition (parent's settled call, recorded
  verbatim on the ledger):** R2b's module, already on
  the public record, discharges the cross pair. This
  integration is **not a second discharge**; it places
  the **independent second proof** of `hCross` on the
  public record under the Foundation doctrine
  (everything learned is stored, for everyone, free
  forever), with this dossier standing. Consumption
  credit for hyp 6's cross input stays with R2b's
  module (first integrated); there is no
  double-counting of the discharge.
- **Build:** main-tree targeted build of
  `ThetLogos.Span3SeatSchurGateW3Cross` green
  (3646 jobs, matching the lane), zero sorrys, **module
  warning-clean** (no warning in the build log names
  this module; every warning belongs to a pre-existing
  dependency module).
- **Recount:** module strict **8 + 2 defs**, exact lane
  match (counter re-validated in-run on spot modules:
  Span3SeatSchurGateMarg 7, PositivityPropagation 43,
  MeasuredClockMonotone 6, Span3SeatSchurGateW3CrossFold
  7, Span3SeatSchurGateW3FactorInt 8). Corpus census
  (FILES-TRUE, method of record): **13,109 / 479 →
  13,117 strict / 480 modules** (whole-tree 13,786 / 495
  minus frozen remainder 669 / 15); README prose census
  and shields badge both updated to 13,117 / 480, kept
  equal.
- **Fence: PASS 175/175** (170 → 175). The 5
  dossier-named headlines admitted
  (`gaugeLinkVal_reflLink`,
  `gaugeMirrorPos_eq_gaugePosFun_reflComp`,
  `measurePreserving_gaugeReflPrecompEquiv`,
  `posGaugeAvg_eq_mirrorGaugeAvg`,
  `fiberAvgTop_twirled_mul_pullback_cross_proved`)
  WITH `import ThetLogos.Span3SeatSchurGateW3Cross` in
  the same commit as the module (CI lesson);
  `gaugeLinkVal_reflLink` on {propext, Quot.sound}, the
  other four on exactly {propext, Classical.choice,
  Quot.sound}; no sorryAx.
- **Ledger:** record `w3-r2a-hcross` (standing, T3)
  added — R2a FULL as the independent second proof of
  hCross, integrated for the record; discharge credit
  unchanged with R2b; K-W3-CROSS retired by proof in
  two packagings; validator PASS, 26 records.
- **What remains:** hypothesis 6 discharges only at
  the R6 assembly (gate open at the factor class,
  Jeff's 2026-11-03 decision); W3 stays OPEN until
  then. NO CLAIM; dials 0/4.
