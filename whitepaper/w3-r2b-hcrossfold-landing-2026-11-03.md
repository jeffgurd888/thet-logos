# W3 REMAINDER R2b — LANDING DOSSIER — 2026-11-03

## VERDICT: FULL — `hCrossFold` DISCHARGED

Brick R2b of the W3 remainder package (scoping dossier
`w3-remainder-scoping-2026-11-03.md` §2, R2b), fired by
Jeff's word 2026-11-04 ("open it" — the R6 gate opened
at the factor class) in parallel with the R2a build
rather than as its increment. Module:
`lean/ThetLogos/Span3SeatSchurGateW3CrossFold.lean`
(**strict 7 theorems + 2 defs**, zero sorrys, module
warning-clean). Lane: worktree
`~/workspace/thet-logos-w3r2b`, branch `w3r2b-lane`,
base = main-tree HEAD `3c22cd6` (R2d+R3a ceremony;
census 13,102 / 478, fence 163/163). NOT integrated,
NOT pushed — the parent runs the ceremony.

## What landed

The fourth of item 6's five per-pair named inputs is
discharged outright, in the **exact form item 6's P3
consumes it**: `fiberAvgTop_dressed_folded_cross_proved`
states, for every even `N`, every `β`, every
strict-half observable `f` and every layer function
`φ'` — no hypotheses on either, and no `4 ≤ N` (P3's
prefix carries none on this input) —

`fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ) * (posGaugeAvg μG f) z
    * φ' (tauBot hN z))`
`= fiberAvgTop μG hN (fun z => (Real.exp
    (-(halfActionP ρ β z)) : ℂ)
    * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z))`.

**Consumption slot, stated exactly:** this headline
fills the `hCrossFold` hypothesis of
`seatPairing_dressed_folded_nonneg_of_cross` (item 6
P3), and thereby the fourth per-pair input of
`gate4c_hyp6_of_named_inputs` (P4). Verified in-lane
by a scratch wiring test (not shipped): P3 applied
with its `hCrossFold` slot filled by this theorem
typechecks unadapted, leaving exactly its other three
inputs (`hIntFold`, `hMarg`, `hInvFold`) as
hypotheses.

## The proof (one substitution, both cross identities)

The scoping priced R2b at L standalone (25–70) /
M as R2a's increment (+8–20), on the expectation that
R2a's machinery would transport. It landed at strict
7 because the transport is not an increment on a
machine — the machine is a single pointwise
substitution, and the folded weight never enters it:

1. **Pointwise substitution**
   (`gaugeMirrorPos_eq_gaugePosFun_refl`): at every
   strict-half link `m`,
   `gaugeMirrorPos g z' m = gaugePosFun (g ∘ reflSite) z' m`.
   Spatial link: reflection commutes with the shift
   (`reflSite_torusShift_of_ne`). Time link: the
   mirror transports to `((σ₀)⁻¹ (θ x), 0)` and inverts
   twice; reflection conjugates the time shift to its
   inverse (`reflSite_torusShift_zero`); the two
   computations agree factor by factor.
2. **Pushforward** (`reflSiteEquiv`, `reflGaugeEquiv`,
   `measurePreserving_reflGaugeEquiv`): precomposition
   with the site reflection is the pi-congruence at
   the reflection's permutation, hence preserves the
   pi Haar measure on gauge functions
   (`MeasureTheory.measurePreserving_piCongrLeft` at
   the constant family).
3. **The twirls coincide**
   (`mirrorGaugeAvg_eq_posGaugeAvg`):
   `mirrorGaugeAvg μG f = posGaugeAvg μG f` as
   functions, for every `f`, by (1) +
   `MeasurePreserving.integral_comp` at (2).
4. **The headline**: both sides of `hCrossFold` carry
   the same folded weight at the same point `z`, so
   the identity is (3) composed with a common
   multiplier — one rewrite. The unconditional
   corollary `fiberAvgTop_dressed_marginal_cross_proved`
   (the unfolded `hCross`, P2's slot) is the same
   rewrite with no weight; it is recorded as the
   engine's byproduct — R2a's brick proper, whose
   landing the parent coordinates with the R2a lane.

This is the mechanism the R2a falsity probe exposed
at its finite seats (probe report §4, T2: 360/360
draws); here it is proved at the corpus's general
`(G, μG)`. The identity is **junk-safe** — an equality
of integrands, pointwise, before any integration —
which is why it lands at the ∀-form with no factor
class restriction, unlike the dressed integrabilities
(compare R1's K-W3-HMARG-FORM lesson). No narrowing
was needed and none was taken.

## Kill status

**K-W3-CROSS does not fire — in either clause.** The
folded clause was the pre-registered kill shape for
this brick; no counterexample can exist at the
consumed generality because the identity is a theorem
there. The unfolded clause is likewise closed by the
corollary. Not K-F2-2 (nothing here certifies or
decertifies any pairing's sign; both pairings'
nonnegativity still routes through P2/P3 under
`LayerKernelPos`).

## Verification

- Targeted lane build green (3,670 jobs), zero
  sorrys, no `native_decide`.
- **Module warning-clean** — no warnings attributed to
  `Span3SeatSchurGateW3CrossFold.lean` (warnings in the
  build log belong to pre-existing dependency modules,
  unchanged). The unused-section-variable cascade was
  discharged in-lane by `omit` at five sites
  (statement texts unchanged).
- `#print axioms` on all seven theorems: six on
  exactly `{propext, Classical.choice, Quot.sound}`;
  `reflSiteEquiv_symm_apply` on the subset
  `{propext, Quot.sound}`. No `sorryAx` anywhere.
- Scratch wiring test (not shipped): P3's
  `hCrossFold` slot accepts the headline unadapted.
- Originals untouched: `Span3SeatSchurGateItem6.lean`
  and all frozen statements unedited.

## Construction friction (on the face)

- **Build environment, two episodes.** The lane's
  first two build attempts died on infrastructure,
  not mathematics: a 1,500 s timeout while the fresh
  worktree compiled its dependency chain, then an
  OOM kill (7 GB machine, concurrent lanes) during a
  from-scratch Mathlib build in the worktree's own
  `.lake`. The lane then seeded its artifact cache by
  hardlinking the main tree's `.lake` build artifacts
  at the *same commit* (`3c22cd6` — identical sources,
  identical traces) and the module compiled against
  them; every subsequent build was a normal targeted
  build of this module alone (3,670-job graph, module
  itself ~5 s). No artifact was committed; the lane
  commit contains only the module and this dossier.
- **First module build, six errors, all local, no
  statement moved:** the dependent-family argument of
  `MeasurableEquiv.piCongrLeft_apply_apply` needed its
  `β` named explicitly; the pointwise identity's two
  branches needed the gauge-value expansions stated by
  `show` (pair projections and `∘` do not unfold under
  `rw`); `MeasurePreserving.integral_comp` in this
  pin states the substitution in the orientation the
  calc needed (no `.symm`); a beta-redex blocked one
  calc rewrite; and the pin's `if_pos`/`if_neg`
  deprecations were replaced by
  `ite_eq_left`/`ite_eq_right`.

## Fences

- This discharges ONE of item 6's five named inputs
  (the fourth). Remaining for hyp 6: `hCross` (R2a —
  in flight in its lane; the engine above proves its
  identity as a corollary, which the parent may use
  or leave as a byproduct), over R1's hMarg re-pin
  (side-condition discharge at use sites is R6's
  wiring question), R2d+R3a's factor-class
  integrabilities, R2c's `hInvFold` (landed), and
  standing `LayerKernelPos`.
- Hypothesis 6 is NOT discharged; the assembly is R6,
  which fires separately under Jeff's 2026-11-03
  decision (factor-class entry; gate opened
  2026-11-04). W3 (`seatSchurProductStepOpen`) stays
  OPEN. GATE-4C's frozen statement is untouched.
- **NO CLAIM** — parts of any official Millennium
  statement closed by this module: 0. Dials: 0/4. The
  gate + W3 prove neither FACT nor clause (a);
  `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain
  open.

## CEREMONY (parent integration, 2026-11-03)

Integrated from w3r2b-lane `525972d` onto main-tree HEAD
`3c22cd6` (W3 R2d+R3a ceremony; census 13,102 / 478, fence
163/163) — the lane's base IS that HEAD, so no drift was
possible; verified anyway: the module and this dossier
were copied **byte-identical** (md5-verified:
`f42685d8…` / `5120f0df…`) and no touch of any kind was
needed.

- **Wiring verification (parent, pre-copy, scratch test
  not shipped): PASS on both cross slots.** Item 6 P3
  (`seatPairing_dressed_folded_nonneg_of_cross`) accepts
  `fiberAvgTop_dressed_folded_cross_proved` in its
  `hCrossFold` slot **unadapted**; item 6 P2
  (`seatPairing_dressed_marginal_nonneg_of_cross`)
  accepts `fiberAvgTop_dressed_marginal_cross_proved`
  in its `hCross` slot **unadapted**; and the P4
  assembly `gate4c_hyp6_of_named_inputs` accepts BOTH
  cross inputs from this module simultaneously,
  unadapted, leaving exactly its other inputs (`hMarg`,
  the two integrabilities, `hInvFold`,
  `LayerKernelPos`) as hypotheses. **The cross pair is
  discharged by this one module.** The still-running
  R2a lane's separate module, if it lands, will be
  dispositioned by the parent as an independent
  duplicate proof of `hCross`, not integrated as a
  second copy.
- **Build:** main-tree targeted build of
  `ThetLogos.Span3SeatSchurGateW3CrossFold` green
  (3670 jobs, matching the lane), zero sorrys, **module
  warning-clean** (no warning in the build log names
  this module; every warning belongs to a pre-existing
  dependency module).
- **Recount:** module strict **7 + 2 defs**, exact lane
  match (counter re-validated in-run on spot modules:
  Span3SeatSchurGateMarg 7, PositivityPropagation 43,
  MeasuredClockMonotone 6). Corpus census (FILES-TRUE,
  method of record): **13,102 / 478 → 13,109 strict /
  479 modules**; README prose census and shields badge
  both updated to 13,109 / 479, kept equal.
- **Fence: PASS 170/170** (163 → 170). The 7
  dossier-named headlines admitted (`reflSiteEquiv_symm_apply`,
  `reflGaugeEquiv_apply`,
  `measurePreserving_reflGaugeEquiv`,
  `gaugeMirrorPos_eq_gaugePosFun_refl`,
  `mirrorGaugeAvg_eq_posGaugeAvg`,
  `fiberAvgTop_dressed_folded_cross_proved`,
  `fiberAvgTop_dressed_marginal_cross_proved`) WITH
  `import ThetLogos.Span3SeatSchurGateW3CrossFold` in
  the same commit as the module (CI lesson); six
  headlines on exactly {propext, Classical.choice,
  Quot.sound}, `reflSiteEquiv_symm_apply` on the subset
  {propext, Quot.sound}; no sorryAx.
- **Ledger:** record `w3-r2b-hcrossfold` (standing, T3)
  added — R2b FULL, the cross-pair discharge and the
  wiring verification on its face, K-W3-CROSS not fired
  in either clause; validator PASS, 25 records.
- **What remains:** NOTHING among item 6's five named
  inputs. Hypothesis 6 discharges only at the R6
  assembly (gate open at the factor class, Jeff's
  2026-11-03 decision); W3 stays OPEN until then.
  NO CLAIM; dials 0/4.
