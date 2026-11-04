# W3 REMAINDER R1 — `hMarg` (TOP FORM) LANDING DOSSIER — 2026-11-03

**Brick:** R1 of the W3 remainder package (scoping
dossier `w3-remainder-scoping-2026-11-03.md` §2, entry
R1; price M, est. strict 12–30). Fired under Jeff's
full-send grant. Built in the isolated worktree lane
`~/workspace/thet-logos-w3r1`, branch `w3r1-lane`, from
main-tree HEAD `b8419d5`; NOT integrated — the parent
runs the ceremony.

## VERDICT: PARTIAL (at full rank) — the pre-registered PARTIAL shape

The brick lands in exactly the disposition the scoping
dossier pre-registered for this outcome:

- **The banked ∀-form of `hMarg` (top) is FALSE as
  stated — K-W3-HMARG-FORM fires.** The failure is
  confined to the non-integrable junk regime (decisive
  write-up below).
- **The re-pinned `hMarg` — the same identity under
  the single side condition that the product integrand
  is integrable — is LANDED and proved in full** (T1),
  as a new registry entry. The admissible-class route
  the scoping dossier named survives intact.
- **K-W3-HMARG (the strong kill) does NOT fire:** there
  is no counterexample at a genuinely integrable pair,
  because on the integrable class the identity is the
  theorem below. The fiber route (item 6 P1, both hyp-6
  pairings) loses nothing on the admissible class.

Module: `lean/ThetLogos/Span3SeatSchurGateMarg.lean`
— **7 strict theorems + 3 defs, zero sorrys**; targeted
build green and **warning-clean** (no errors and no
warnings originating in this module; the only build
warnings are pre-existing ones in dependency modules);
`#print axioms` on the headlines returns exactly
`[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. Strict count is below the scoping estimate
(7 vs 12–30): the landed `splitEquiv` /
`integral_pi_restrict` stock in `LatticeCorrelations`
already carried the coordinate split the estimate
priced as new work. Per the gate-module house pattern
the module is not in the root import list; it is
verified by targeted build.

## The kill: K-W3-HMARG-FORM — the ∀-form is false in the junk regime

The banked statement (now named in-tree as the
definition `hMargTopStatement`, so the kill and the
consumers' hypothesis share one address) quantifies
over ALL observables `a` and layer functions `Ψ` with
no side conditions. It is false. The two sides'
Bochner junk conventions diverge off the integrable
class: the left side junk-kills the whole integral
when `a * (Ψ ∘ tauTop)` is non-integrable over the
strict-half product, while the right side first
averages over the fibers — where `a` can be honestly
integrable with cancellation — and the resulting layer
function can be honestly integrable with nonzero
integral.

**Counterexample (decisive write-up).** Take the
Circle seat (`G = Circle`, `μG` its Haar probability,
in the ambient variable package), any even `N`, a
frozen link `m₀` in the image of `embLayerTop`, and a
free strict-half link `m₁` outside that image (both
exist: the top embedding's image is the top-half layer
links only). Let `c : Circle → ℝ`, `c(x) = ‖x − 1‖⁻¹`
for `x ≠ 1`, `c(1) = 0` — Haar-nonintegrable, since
`‖e^{iθ} − 1‖ ≍ |θ|` and `∫ |θ|⁻¹ dθ` diverges at
`0`. Set

  `a z = c (z m₀) * (z m₁ : ℂ) + 1`,   `Ψ ≡ 1`.

- *Right side = 1.* In `fiberAvgTop a u`, the splice
  freezes coordinate `m₀` at `u`'s value, so the
  integrand is `c(u) * z m₁ + 1` with `c(u)` a finite
  constant; it is bounded, hence honestly integrable,
  and the free coordinate integrates to
  `∫ w, w ∂Haar = 0` (rotation invariance). So
  `fiberAvgTop a ≡ 1` and the right side is `1`.
- *Left side = 0.* By Tonelli through the coordinate
  split, `∫ ‖a‖ = ∫ (c ∘ eval m₀) = ∫ c = ∞`; so
  `a * (Ψ ∘ tauTop) = a` is not integrable over the
  strict-half product and the Bochner integral takes
  its junk value `0`.

`0 ≠ 1`: the ∀-form fails. Note the failure is
invisible to any finite-product model — there every
function is integrable and the ∀-form holds — which
is why the scoping dossier's prescribed finite audit
could not detect it; the audit's algebraic content
(splice = assembly, extraction = restriction) is
confirmed instead by the proof below. This kill is
**not** K-F2-2 (no certified negative pairing; the
dressed pairings are untouched) and not
K-W3-HMARG (no genuinely integrable counterexample).

## The re-pin: `fiberAvgTop_marginal_of_integrable` — LANDED (T1)

**Statement.** For every strict-half observable `a`
and layer function `Ψ` with

  `hInt : Integrable (fun z => a z * Ψ (tauTop hN z))`
  over the strict-half pi product,

  `∫ z, a z * Ψ (tauTop hN z)`
  `= ∫ u, fiberAvgTop μG hN a u * Ψ u`.

This is the conditional-expectation property of the
landed `fiberAvgTop` under the product pi measure, in
corpus vocabulary, at the dossier's generality (every
even `N`, every `β`-free — `hMarg` carries no `β` —
every ambient `(G, μG)` of the gate package).

**Proof route** (the scoping dossier's route, as
landed): split the strict-half links into the image
of `embLayerTop` (`layerTopFinset`, `assembleTop`) —
the splice inside `fiberAvgTop` is assembly across
this split (`spliceTop_eq_assembleTop`), so the fiber
average is the complementary marginal with **no
hypotheses** (`fiberAvgTop_eq_integral_compl`, via the
landed `integral_pi_restrict`); transport the left
side across the landed `splitEquiv`; take the single
Fubini step (`integral_prod`) under `hInt`; transport
back along the embedding (`integral_comp_emb`). Every
step except the one Fubini step is junk-safe, which is
exactly why the side condition is one integrability
hypothesis and nothing else (no measurability or
boundedness side conditions are needed: they are
absorbed by the transported `Integrable`).

## What it unblocks

Item 6's P1 and both hyp-6 pairings consume `hMarg`;
the R6 assembly (`seatSchurProductStepOpen_discharge_gate4`)
can now be fed the re-pinned entry in place of the
banked hypothesis, discharging the side condition
`Integrable (fun z => a z * Ψ (tauTop hN z))` at each
consumption site from the consumers' own product
integrability inputs. Whether those discharges go
through at P1's exact internal use sites (its `Ψ` are
`layerKernel` sections at fixed configurations) is
R6's wiring question and is **not** settled here —
this brick lands the input, not the assembly.

## Fences (unchanged, restated)

- The bottom form of `hMarg` is NOT built (scoping
  correction 1: it completes GATE-2's G2b re-pin but
  feeds nothing on W3's critical path; optional extra,
  off-path).
- Frozen statements elsewhere — `hMarg` as carried by
  GATE-2's `Span3SeatSchurGateFiber` theorems and item
  6's `Span3SeatSchurGateItem6` theorems — are NOT
  edited. This module is a new entry; substitution is
  R6's.
- W3 is NOT closed by this brick. `LayerKernelPos`,
  FACT, `𝒜 ⪰ 0`, clause (a), and uniformity are
  untouched by it (K-F2-4): the theorem is a
  disintegration identity, nothing more.
- NO CLAIM — parts of any official Millennium
  statement closed by this landing: 0. Dials: 0/4.

## Verification record

- Worktree `~/workspace/thet-logos-w3r1`, branch
  `w3r1-lane`, base `b8419d5` (census 13,086 strict /
  475 modules, fence 149/149).
- `lake build ThetLogos.Span3SeatSchurGateMarg`:
  green; zero errors; **zero warnings originating in
  this module** (warning-clean on the first shipped
  version — two cosmetic episodes during construction,
  deprecated `dif_pos`/`dif_neg` names and unused
  section variables, were fixed in-lane by
  restructuring the variable sections, not shipped).
- Strict count (theorem/lemma at column 0,
  comment-stripped): **7**, plus 3 defs (`layerTopFinset`
  abbrev, `assembleTop`, `hMargTopStatement`). Zero
  `sorry` tokens in the file.
- `#print axioms`: `fiberAvgTop_marginal_of_integrable`,
  `fiberAvgTop_eq_integral_compl`,
  `spliceTop_eq_assembleTop`,
  `assembleTop_restrict_self`,
  `restrictTop_comp_embEquiv` — each exactly
  `[propext, Classical.choice, Quot.sound]`.
- NO CLAIM. Dials 0/4. Nothing public shipped from
  this lane.

## CEREMONY (parent integration, 2026-11-03)

Integrated from w3r1-lane `0501206` onto main-tree HEAD
`1a23a9a` (W3 R2c ceremony; census 13,087 / 476, fence
150/150) — the lane's base `b8419d5` is one ceremony
behind; the module is new and its dependencies were
untouched by the intervening R2c ceremony, so no drift
was expected; verified anyway: the module and this
dossier were copied **byte-identical** (md5- and
diff-verified) and no touch of any kind was needed.

- **Build:** main-tree targeted build of
  `ThetLogos.Span3SeatSchurGateMarg` green (3646 jobs),
  zero sorrys, **module warning-clean** (every warning
  in the build belongs to a pre-existing dependency
  module; none names this module).
- **Recount:** module strict **7 + 3 defs**, exact lane
  match (counter re-validated in-run on spot modules:
  MeasuredClockMonotone 6, PositivityPropagation 43,
  Span3SeatSchurPosBridge 29, Span3SeatSchurGateW3InvFold
  1). Corpus census (FILES-TRUE, method of record):
  **13,087 / 476 → 13,094 strict / 477 modules**; README
  prose census and shields badge both updated to
  13,094 / 477, kept equal.
- **Fence: PASS 155/155** (150 → 155). The 5
  dossier-named headlines
  (`fiberAvgTop_marginal_of_integrable`,
  `fiberAvgTop_eq_integral_compl`,
  `spliceTop_eq_assembleTop`,
  `assembleTop_restrict_self`,
  `restrictTop_comp_embEquiv`) admitted with
  `import ThetLogos.Span3SeatSchurGateMarg` in the same
  commit as the module; every headline on exactly
  {propext, Classical.choice, Quot.sound}, no sorryAx.
- **Ledger:** record `w3-r1-hmarg` (standing, T3) — R1
  PARTIAL at the pre-registered shape; K-W3-HMARG-FORM
  fired (banked ∀-form false only in the junk regime,
  counterexample on this dossier's face); the re-pin
  proved under the integrability side condition;
  K-W3-HMARG did not fire; bottom form not built,
  off-path; R6 consumes the re-pin, discharging the
  side condition at use sites is R6's wiring question;
  hyp 6 NOT discharged, W3 OPEN — all on its face.
  Validator PASS, 23 records.
- **Commit/push/CI:** recorded in the pipeline log
  (`~/workspace/launch-pipeline-2026-10-29.md`) per house pattern.

Verdict stands PARTIAL at full rank: **K-W3-HMARG-FORM
fired — the banked ∀-form of `hMarg` (top) is false in
the non-integrable junk regime — and the re-pin
`fiberAvgTop_marginal_of_integrable` is a theorem on
the public record** under the single integrability
side condition. K-W3-HMARG did not fire. Hypothesis 6
is NOT discharged; W3 stays OPEN. NO CLAIM; dials 0/4.
