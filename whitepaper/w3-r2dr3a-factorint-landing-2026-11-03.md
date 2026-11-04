# W3 remainder R2d+R3a (merged) — the dressed integrabilities at the factor class: LANDING 2026-11-03

Module: `lean/ThetLogos/Span3SeatSchurGateW3FactorInt.lean`
Lane: worktree `thet-logos-w3r2d`, branch `w3r2d-lane`. Base: **a339fba**
(the main tree had advanced past the brief's 1a23a9a by the R1 ceremony —
census 13,094 strict / 477 modules, fence 155/155 — before this worktree
was cut; the worktree was created from a339fba).
Scoping: `w3-remainder-scoping-2026-11-03.md` §2 bricks R2d and R3a and
§4 correction 2, which governs this landing. Pre-registered kills for
this brick: none (a distributional-failure kill was conceivable only on
the frozen ∀-forms, which correction 2 removes from the target).

## VERDICT (T1, at the factor class): FULL

Both dressed integrability inputs of GATE hypothesis 6 — the third and
fifth per-pair inputs of item 6's assembly
`gate4c_hyp6_of_named_inputs` — are **discharged at the factor class**:
for every observable `f` satisfying hyp 6's own prefix (a.e. strongly
measurable, pointwise bounded) and every layer factor `φ'` with
`MemLp φ' 2` on the layer pi measure. That class is exactly the class
the assembly consumes: item 5's conditional headline
(`seatFactorApproxExpansion_of_layerKernelPosAll`) produces its factors
as `Lp` coeﬃcients `⇑(gramFactor …)`, which are `MemLp 2` by
definition.

The seam, named at full rank (FENCE 1 of the brief, R1's lesson): the
**frozen ∀-forms are NOT proved, and are not claimed here.** Hyp 6's
frozen shape quantifies over a bare `φ'` with no regularity at all,
and hyp 4's frozen `hIntStage` quantifies over arbitrary expansion
data. What this brick lands is a **factor-class variant entry** — the
registered reading of the scoping (its §4 correction 2 and §5 assembly
note): R6 assembles hyp 6/hyp 4 at this entry for factor-produced
data. Item 6's P6 already discharged hyp 4 in the regular case
(pointwise measurable, pointwise bounded factors). The two entries
together still do not cover arbitrary data; that gap is the seam, and
it is a statement-level fact about the frozen forms, not a gap in this
proof. Whether the variant entry is accepted at the assembly is the
parent's/Jeff's decision, already registered — it is not taken here.

FENCE 2 respected: this brick discharges the two integrability INPUTS
only. It does not touch `hIntLim`/`hIntStage` in their frozen forms,
does not touch hyps 4/5 beyond what is stated above, and carries
`hρcont` throughout (the bare-ρ question is probe R3b's, not this
brick's).

## What landed — strict 8, zero sorrys, warning-clean

Support (the Cauchy–Schwarz core, shared by both consumptions):

1. `memLp_factor_pullback` — a layer factor in `MemLp 2` pulls back
   along the bottom-half embedding: `MemLp (φ' ∘ tauBot hN) 2` on the
   strict-half pi space, via item 5's in-tree
   `measurePreserving_tauBot` and `MemLp.comp_measurePreserving`.
2. `memLp_mul_of_aestronglyMeasurable_bounded` — an a.e. strongly
   measurable, pointwise bounded multiplier preserves `MemLp 2`, via
   `MemLp.infty_mul` at the `(∞, 2, 2)` Hölder triple.
3. `integrable_pullTopKernel_mul_of_memLp_slots` — the core: two
   `MemLp 2` slot functions on the strict-half pi space are multiplied
   by the pulled layer kernel into an integrable product, by composing
   each slot to the product space (`measurePreserving_fst`/`snd`),
   `MemLp.mul` at the `(2, 2, 1)` Hölder triple, and
   `Integrable.bdd_mul` against the kernel's a.e. strong
   measurability (item 6) and its uniform norm bound
   (`layerKernel_norm_le`, `exp (|β| * layerBoundConst N)`). A
   genuinely quadratic Cauchy–Schwarz quantum at product level —
   product of two `L²` slots is `L¹`, never `L²`.

The two targets, verbatim in item 6's consumption shapes:

4. `integrable_dressed_marginal_of_memLp_factor` (R2d) — the plain
   dressed integrand of hyp 6's `hInt` is integrable, at the factor
   class.
5. `integrable_dressed_folded_of_memLp_factor` (R3a) — the folded
   dressed integrand of hyp 6's `hIntFold` is integrable, at the
   factor class; the folded weight is measurable
   (`measurable_halfActionP_lf`, under `hρcont` — item 6's P5 stock)
   and uniformly bounded (`norm_exp_neg_halfActionP_le`), so the
   folded slots are `MemLp 2` by the same bounded-multiple step.
6. `gate4c_hyp6_integrability_inputs_of_memLp_factor` — the pair,
   packaged in the assembly's consumption order.

Hypothesis 4 at the factor class (the R3a half of the merged brick):

7. `hIntStage_of_memLp_factors` — hyp 4's verbatim ∀-conclusion
   (both dressed stage integrands, `pullTopKernel` form), proved for
   expansion data whose every factor is `MemLp 2` on the layer pi
   measure, under `hρcont`.
8. `hIntStage_gramFactors` — (7) instantiated at item 5's own factor
   data: `φ n k = ⇑(gramFactor b (Fseq n) (vseq n) k)`, whose `MemLp 2`
   membership is `MeasureTheory.Lp.memLp`. Hypothesis 4 therefore
   holds verbatim for the data the compression route produces.

## Route note (construction friction, resolved in-lane, no statement moved)

The first full assembly timed out at `whnf` (200k heartbeats) on the
two closing `exact`s: the type-level defeq between the core's
`pullTopKernel`-formed conclusion and the `layerKernel`-formed targets
blows up at unification, although the two integrands agree pointwise
by a single delta-unfolding. Resolution: close through
`Integrable.congr` with the pointwise equation proved by `rfl`
(closed-term check, fast), in T1/T2 and again in (7)'s components.
Bisected in a scratch module; the scratch was deleted, not shipped.

## Count against estimate

Scoping price: strict 20–45. **Landed: strict 8, defs 0.** Under the
band, disclosed on the face (R1 precedent): the shared core (3)
absorbs both consumptions at once, and the corpus's landed stock
carried the rest — item 6's kernel measurability and bound, item 5's
measure-preserving embedding, `IntegralKernelHS`'s Hölder-triple
pattern, and item 6's folded-weight measurability/bound stock were all
consumed, not re-proved.

## Verification record

- Targeted build in the lane worktree: `lake build
  ThetLogos.Span3SeatSchurGateW3FactorInt` — **green, 3675 jobs**;
  zero errors and **zero warnings originating in the module**
  (dependency warnings are pre-existing corpus noise).
- Zero `sorry` tokens in the module.
- `#print axioms` on all 8 headlines: exactly **{propext,
  Classical.choice, Quot.sound}** each — no `sorryAx`.
- Strict count by the house method (theorem/lemma at column 0,
  comment-stripped): **8**.

## What remains for hypothesis 6 after this landing

Per-pair inputs of item 6's assembly, status: the two dressed
integrabilities — **landed here, at the factor class**; the folded
gauge invariance `hInvFold` — landed (R2c); the cross identity
`hCross` — R2a (probe exhausted, no kill; build in flight in its own
lane); the folded cross identity `hCrossFold` — R2b (not yet built).
Over them sits `hMarg`, whose **re-pin** landed in R1
(`fiberAvgTop_marginal_of_integrable`, under its single integrability
side condition); whether that side condition discharges at P1's exact
internal use sites is R6's wiring question, not settled here.
`LayerKernelPos` remains a standing hypothesis of the assembly (P4),
neither proved nor refuted — untouched by this package.

**R6 (final assembly) is the only remaining brick**, gated on Jeff's
registered variant-entry decision: assemble hyp 6 (and feed hyp 4)
at the factor class — this module's entries, R2c's invariance, R1's
re-pin — or hold the frozen ∀-forms. This landing does not take that
decision.

**Hypothesis 4 beyond the regular case:** discharged at the factor
class by (7)/(8) above; the frozen ∀-form over arbitrary data remains
unproved — the seam named above, unchanged in kind.

W3 is **not closed** by this landing. **NO CLAIM; dials 0/4.**

## CEREMONY (parent integration, 2026-11-03)

Integrated from w3r2d-lane `20efe9a` onto main-tree HEAD
`a339fba` (W3 R1 ceremony; census 13,094 / 477, fence
155/155) — the lane's base `a339fba` IS that HEAD (the
lane correctly cut from current HEAD, not the brief's
stale `1a23a9a`), so no drift was possible; verified
anyway: the module and this dossier were copied
**byte-identical** (md5- and diff-verified) and no touch
of any kind was needed.

- **Build:** main-tree targeted build of
  `ThetLogos.Span3SeatSchurGateW3FactorInt` green
  (3675 jobs, matching the lane), zero sorrys, **module
  warning-clean** (every warning in the build belongs
  to a pre-existing dependency module; none names this
  module).
- **Recount:** module strict **8 + 0 defs**, exact lane
  match (counter re-validated in-run on spot modules:
  Span3SeatSchurGateMarg 7, PositivityPropagation 43,
  MeasuredClockMonotone 6, Span3SeatSchurGateW3InvFold
  1). Corpus census (FILES-TRUE, method of record):
  **13,094 / 477 → 13,102 strict / 478 modules**; README
  prose census and shields badge both updated to
  13,102 / 478, kept equal.
- **Fence: PASS 163/163** (155 → 163). The 8
  dossier-named headlines (`memLp_factor_pullback`,
  `memLp_mul_of_aestronglyMeasurable_bounded`,
  `integrable_pullTopKernel_mul_of_memLp_slots`,
  `integrable_dressed_marginal_of_memLp_factor`,
  `integrable_dressed_folded_of_memLp_factor`,
  `gate4c_hyp6_integrability_inputs_of_memLp_factor`,
  `hIntStage_of_memLp_factors`,
  `hIntStage_gramFactors`) admitted with
  `import ThetLogos.Span3SeatSchurGateW3FactorInt` in
  the same commit as the module; every headline on
  exactly {propext, Classical.choice, Quot.sound}, no
  sorryAx.
- **Ledger:** record `w3-r2dr3a-factorint` (standing,
  T3) — R2d+R3a FULL at the factor class; the seam on
  its face (the frozen ∀-forms of hyp 6 bare-φ′ and
  hyp 4 arbitrary-data are NOT proved; this is the
  factor-class variant entry per scoping correction 2;
  R6's assembly at this entry stays gated on Jeff's
  decision); `hρcont` carried throughout; hyp 6 NOT
  discharged; W3 OPEN. Validator PASS, 24 records.
- **Commit/push/CI:** recorded in the pipeline log
  (`~/workspace/launch-pipeline-2026-10-29.md`) per house pattern.

Verdict stands FULL at the factor class: **both dressed
integrabilities of hypothesis 6, and hypothesis 4 at the
factor class, are theorems on the public record** — and
the frozen ∀-forms stand unproved beside them, the seam
named. Hypothesis 6 is NOT discharged; W3 stays OPEN.
NO CLAIM; dials 0/4.
