# POSITIVITY BRIDGE — LANDING DOSSIER (2026-11-03)

## VERDICT: FULL BRIDGE

The positivity bridge priced by
`~/workspace/your_files/positivity-bridge-scoping-2026-11-03.md`
landed WHOLE. `LayerKernelPos` (positivity of the layer pairing
on gauge-invariant observables), under the representation
regularity hypothesis `hρcont` that item 5's seat machinery
already carries, implies `LayerKernelPosAll` (positivity of the
layer-kernel operator on ALL of `L²(layer)`). Item 5's
conditional headline therefore fires at the frozen generality:
the frozen GATE-0 item-5 statement
`pullBotKernel_seatFactorApproxExpansion` holds under
`hρcont` + `LayerKernelPos`.

**`LayerKernelPos` itself stays OPEN.** The bridge is an
implication between two open statements. Nothing in this
landing proves `LayerKernelPos`, `𝒜 ⪰ 0`, FACT, or clause (a)
(K-F2-4). NO CLAIM; dials 0/4.

Module: `lean/ThetLogos/Span3SeatSchurPosBridge.lean`
(strict 29 + 5 defs, zero sorrys). Lane: worktree
`~/workspace/thet-logos-posbridge`, branch `posbridge-lane`,
base = main-tree local HEAD `4e35329` (item-5 ceremony).
NOT integrated, NOT pushed — the parent runs the ceremony
(onto the current main HEAD, which has since advanced with
the U-3a and SP-5 ceremonies).

## Per-stage verdicts

### PB-1 — BRIDGE-SEP: FULL

`layerKernel_gauge_invariant`: for every Even `N`, every `β`,
and independent gauge functions `g g'`,

`layerKernel μG ρ β (layerGaugeAction g u) (layerGaugeAction g' u') = layerKernel μG ρ β u u'`.

Route as priced: the stratum substitution
`α'_c = g(c)·α_c·g'(c)⁻¹` (landed as `stratumSubstEquiv`,
with the inverse substitution as its forward map) makes
every plaquette word conjugate (`plaquette_layerConfig_gauge`,
via the landed `trace_repMatrix_conj`), so the density is
unchanged; the substitution is a per-coordinate two-sided
translation, hence measure-preserving
(`measurePreserving_stratumSubst`). One-slot corollaries
`layerKernel_gauge_invariant_fst` / `_snd` landed alongside.

**K-POS-BRIDGE did NOT fire**: separate invariance is TRUE
for this kernel, proved in Lean. No obstruction.

### PB-2 — operator transport: FULL

- `integralKernelFun_layerKernelFun_gauge`: the
  kernel-defined representative of the layer operator is
  unchanged at a gauge-transformed point (BRIDGE-SEP, first
  slot, inside the defining integral).
- `gaugeInvariantLayerObs_integralKernelFun`: that
  representative is exactly gauge-invariant.
- `exists_gaugeInvariantLayerObs_rep`: every
  `integralKernelOp hK f` has an exactly gauge-invariant
  representative (range inside invariants, at representative
  level, via the landed `coeFn_integralKernelOp`).
- `layerKernelOp_inner_gaugeAvg` — **the form identity**:
  `⟪f, Tf⟫ = ⟪Pf, T(Pf)⟫` at the level of representatives —
  the operator's quadratic form at an observable `F` equals
  its quadratic form at `F`'s gauge average, transported
  through `integralKernelOp_inner`, the class transport
  (`layerPairingProd_congr_ae`), and the master identity.
  Item 5's landed self-adjointness is consistent with and
  consumed by the surrounding machinery; the identity itself
  needs only BRIDGE-SEP and the pairing calculus.

### PB-3 — strictification + assembly: FULL, no seam

The pre-named PARTIAL seam (strictification stalling) did
NOT materialize. The gauge average

`gaugeAvg μG F = ∫ g, F (layerGaugeAction g ·) ∂(Haar pi)`

is an **exactly** gauge-invariant representative:
`gaugeAvg_gauge_invariant` holds pointwise for every `F`
(no measurability hypothesis), via the composition law
`layerGaugeAction_comp` and Haar substitution along
`gaugeMulEquiv`. It stays in `L²` (`gaugeAvg_memLp`, Jensen
through the corpus's sqrt–sqrt estimate and Tonelli over
the measure-preserving joint gauge action).

**Master identity** (`layerPairingProd_gaugeAvg`): the
function-level layer pairing of `F` equals that of
`gaugeAvg μG F` — average the constant pairing over the
probability gauge group, substitute per gauge parameter
(BRIDGE-SEP via `pairing_gauge_integral`), swap (Fubini),
and separate the double average.

**BRIDGE-MAIN** (`layerKernelPosAll_of_layerKernelPos`):
for `f : Lp`, take a measurable representative `F'`; the
operator pairing of `f` is the function pairing of `F'`
(`integralKernelOp_inner` + class transport); the master
identity replaces `F'` by its gauge average; the product
pairing is the iterated pairing
(`layerPairingProd_eq_layerPairing`, Fubini); the gauge
average is exactly invariant, so `LayerKernelPos` applies
(`layerPairing_nonneg_of_layerKernelPos`). ∎

**BRIDGE-COR** (both forms):
- `seatFactorApproxExpansion_of_layerKernelPos`:
  `SeatFactorApproxExpansion` under `LayerKernelPos` +
  `hρcont` at every Even `N`, every `β`.
- `pullBotKernel_seatFactorApproxExpansion_of_cont`:
  the frozen ∀-form — at every Even `N`, every `β ≥ 0`,
  `LayerKernelPos` ⇒ the expansion — holds under `hρcont`.

## ERRATUM VERDICT (explicit, on the face)

Item 5's module header sentence — `layerKernel` "is not
separately first-slot invariant in general (G2c dossier
obstruction)" — is **INCORRECT AS STATED**. PB-1 proves
separate invariance of `layerKernel` in each slot for the
layer gauge action, at every Even `N` and every `β`. The
G2c obstruction on record concerns dressed *fiber averages*
of observables, not invariance of the kernel itself. The
landed item-5 module is NOT edited; this erratum rides this
dossier, the bridge module's header, and the ceremony
record.

## Kill ledger

- **K-POS-BRIDGE** (kernel-specific bridge false): NOT
  fired. BRIDGE-SEP is proved; the bridge stands.
- **K-POS-BRIDGE-GEN** (symmetry-alone argument): fired at
  scoping and respected — every step uses THIS kernel's
  separate invariance (word conjugation of its plaquettes),
  never an abstract symmetry principle. The scoping probe's
  control operator (2P_fix − I) counterexample stands as the
  record of why the kernel-specific step was necessary.
- **K-POS-VAC** (vacuous/stronger restatement): not
  triggered. The bridge's conclusion is the registered
  `LayerKernelPosAll` itself, its hypothesis the registered
  `LayerKernelPos` itself, at the frozen domain; no
  dense-subclass or all-of-`L²` hypothesis was substituted
  for the target anywhere.

## What this does to item 5's headline and to W3

Item 5 landed PARTIAL with the seam on its face:
`seatFactorApproxExpansion_of_layerKernelPosAll` — the
headline under `LayerKernelPosAll`, "strictly stronger
than `LayerKernelPos` and proved nowhere". This bridge
proves `LayerKernelPosAll` FROM `LayerKernelPos` (under
`hρcont`). The frozen GATE-0 item-5 statement is therefore
discharged modulo exactly two still-open inputs:
`LayerKernelPos` (the registered `𝒜 ⪰ 0`-on-invariants
hypothesis, untouched) and `hρcont` (representation
regularity, already a hypothesis of item 5's own seat
machinery).

W3 re-read (the three remainders after items 5+6):
1. Item 5's expansion at frozen generality under
   `LayerKernelPos` alone — **REMOVED by this bridge**
   (up to `hρcont`, as above).
2. Item 6's five named inputs over `hMarg` — untouched,
   still open.
3. Hyps 4/5 beyond the regular case — untouched, still
   open.

**W3 stays OPEN** behind (2) and (3). The frozen GATE-4
stands unedited and unproved; this lane does not touch it.

## Verification

- Targeted build: `lake build ThetLogos.Span3SeatSchurPosBridge`
  green, 3675 jobs; module warning-clean (only pre-existing
  dependency warnings in the log); zero sorrys.
- `#print axioms` on all 18 headline/supporting
  declarations (BRIDGE-SEP + one-slot forms, PB-2 transport
  + form identity, `gaugeAvg_gauge_invariant`,
  `gaugeAvg_memLp`, `pairing_gauge_integral`,
  `memLp_gaugeTensor`, master identity, class transport,
  `memLp_tensorFun`, product/iterated conversion,
  BRIDGE-MAIN, BRIDGE-COR ×2): every one depends on exactly
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`,
  nothing outside the fence set.
- Strict count: 29 theorems/lemmas + 5 defs, by the method
  of record (`theorem`/`lemma` at column 0) — inside the
  priced estimate (26–49).
- Commits on `posbridge-lane`: `9296e02` (PB-1), `7dba491`
  (PB-2), `c0955cc` (PB-3 chunks A+B), `b25a3e8` (PB-3
  chunks C+D), plus the final BRIDGE-MAIN/COR commit
  carrying this dossier. No commits to `master`; no push;
  no posts or sends.

NO CLAIM — parts of any official Millennium statement
closed by this landing: 0. Dials: 0/4.

## CEREMONY (parent, 2026-11-03)

Integrated into the main tree from `posbridge-lane`
`abeba12` onto main HEAD `30eec70` (SP-5 ceremony); module
and this dossier copied **byte-identical** (diff-verified);
the module is unedited — the erratum on item 5's header
sentence rides this dossier and the bridge module's header,
and item 5's own module stays unedited.

- **Build:** main-tree targeted build
  `lake build ThetLogos.Span3SeatSchurPosBridge` green,
  3675 jobs (matching the lane exactly); zero sorrys;
  module warning-clean (only pre-existing dependency
  warnings in the log, in `IntegralKernelSchur`).
- **Recount:** module 29 strict + 5 defs — exact match with
  the lane. Corpus census (FILES-TRUE, method of record:
  whole-tree recount 13,706 strict over 488 files, counter
  re-validated in-run against TritGrading 27,
  MirrorTwentyOneTriplets 32, GateItem6 15, OneKernel 20,
  OddRing 15, AxiomTetPartnerIso 13; minus the frozen
  pre-ledger remainder 669 strict / 15 files) =
  **13,037 strict / 473 modules** (13,008/472 → +29/+1).
  README prose census and shields badge both updated to
  13,037 / 473, kept equal.
- **Fence: PASS 136/136** (118 → 136). The 18 axiom-checked
  declarations named on this dossier's face admitted, every
  one on exactly {propext, Classical.choice, Quot.sound},
  no sorryAx — with `import ThetLogos.Span3SeatSchurPosBridge`
  in the same commit as the module (CI lesson).
- **Ledger:** record `positivity-bridge` (standing, T3)
  added — FULL verdict, BRIDGE-MAIN, the frozen item-5
  headline discharged modulo `LayerKernelPos` (which stays
  OPEN), W3 remainder item (1) removed, and the item-5
  header ERRATUM on its face. Validator PASS, 19 records.
- **Commit/push/CI:** one ceremony commit (hash recorded
  in the pipeline log, per house pattern); remote tree
  verified identical via read-only GitHub API; lean-ci
  verified green on the pushed head from GitHub's API.

Verdict stands FULL at full rank: **the positivity bridge
stands** — `LayerKernelPos` + `hρcont` ⇒ `LayerKernelPosAll`,
and the frozen item-5 expansion headline is discharged
modulo `LayerKernelPos`. `LayerKernelPos` itself stays
OPEN. NO CLAIM; dials 0/4.
