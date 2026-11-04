# Positivity Propagation — Landing Dossier (2026-11-03)

Lane: `prop-lane` worktree `~/workspace/thet-logos-prop`, from main-tree HEAD
**30eec70** (local) / remote **6562cda3**. Scoping of record:
`~/workspace/your_files/positivity-propagation-scoping-2026-11-03.md`.
Jeff's order 2026-11-03: "run it." NO ceremony, no push — the parent runs
the ceremony after the bridge lane's state is known.

**Headline: PROP-0 LANDED (T1), PROP-1A LANDED (T1, conditional),
K-PROP-FORM FIRED at the probe seat (T2). NO CLAIM; dials 0/4; parts
closed 0.**

---

## 1. The three probes (T2, RG-1 exact-arithmetic idiom)

Script: `~/workspace/your_files/positivity-propagation-probes-2026-11-03.py`
Output: `~/workspace/your_files/positivity-propagation-probes-2026-11-03.txt`

Seat: G = Multiplicative (ZMod 2), sign character (d = 1, density ∈ {0, 2}),
uniform probability measure, layer N = 2 (8 sites, 24 links),
β ∈ {−1, 0.5, 1, 2}. With A′(β) = (1 + e^{−2β})/2, B′(β) = (1 − e^{−2β})/2.

Grounding checks (all passed): independent `layerConfig` plaquette
recomputed as a one-layer word on 200 random configurations; per-link
character transform table exact at all β (M⁰⁰ = 4A′, M¹¹(d) = 4B′(−1)^d,
off-diagonals 0); cycle space dimension 17; all Eulerian weights even
(bipartite); α-parity factor = 1 on 400 sampled Eulerian sets × 256 α;
1D mini-layer brute force matches closed form to ~1e-15.

### PROP-1B-PROBE (fine half) — `LayerKernelPos` HOLDS at the fine seat

The pairing is diagonal on invariant characters with eigenvalues
λ_S = A′^(24−|S|) B′^|S| ≥ 0 for all 131,072 Eulerian subsets S at every
sampled β; by the sign argument (A′ > 0, |S| even) this holds for all
real β at this seat.

### Blocked kernel, closed form (brute-force verified to 1.6e-15)

𝒜^{[2]}(U, U′) = ∏_{ν=1..3} (A′⁸ + (−1)^{U_ν+U′_ν} B′⁸) at the coarse
seat N′ = 1 (coarse gauge action trivial there; abelian seat, so the
invariant class is all observables).

### PROP-2-PROBE — **K-PROP-FORM FIRED (T2, at the seat)**

𝒜^{[2]}(U, U) = (A′⁸ + B′⁸)³ ≠ 1 at every sampled β ≠ 0
(β = 0.5: 1.104421e-04; β = 1: 1.729662e-06; β = 2: 4.904120e-07;
β = −1: 1.213658e+15), while every Wilson layer kernel at the coarse seat
has diagonal exactly 1 for every coarse datum. The fiber-integrated
blocked kernel is therefore **not of Wilson layer form at any coarse
datum** at this seat. At β = 0 both sides are ≡ 1 (the Stage-2 fixed
point, T1 in-tree). This confirms, at kernel level and at T2, the kill
the scoping registered as expected: the blocked object is a new kernel
species, and PROP-0 defines it as such rather than forcing it into the
layer-kernel mould.

### PROP-1B-PROBE (blocked half) — K-PROP-INV NOT fired

𝒜^{[2]} is positive semi-definite as a pairing operator at all sampled β
(minimum eigenvalues: β = −1: 1.275736e+12; β = 0.5: 9.873658e-13;
β = 1: 1.818134e-09; β = 2: 3.824768e-08). Propagation survives the
miniature; no invariant-class obstruction seen at this seat.

### PROP-3-PROBE — K-PROP-MARGIN NOT fired

margin₁ (fine, invariant class) = margin₂ (blocked) **exactly** at all
sampled β; ratio = 1.000000. The extremal character is the full-product
character, a blocking pullback, so its eigenvalue is preserved exactly.
Seat atmosphere only (abelian, d = 1, N = 2 → 1; a two-step chain
degenerates since ZMod 1 has no factor-2 blocking): this is evidence
about the *shape* a margin theorem would need, not about general
(G, ρ), and is reported at T2 as such. (The fine margin itself degrades
in system size — a size statement, not a step statement.)

---

## 2. PROP-0 — LANDED (T1)

Module: `lean/ThetLogos/PositivityPropagation.lean`, building green
(`lake build ThetLogos.PositivityPropagation`, 3675 jobs), zero sorrys,
no `native_decide`.

Definitions landed, in corpus vocabulary:

- **Octet decomposition** (§1): `LayerLink N ≃ LayerLink (N / 2) × Fin 8`
  — a coarse link (Y, ν) corresponds to the 8 fine links of direction ν
  based at the 8 fine sites of Y's 2×2×2 spatial block; the block value
  is the ordered octet product (List products; G is a general group, so
  no `Finset.prod`), distinguished element at offset 0.
- **Blocked layer datum** (§2): the assembly `layerBlockAsm (U, w)`
  (coarse configuration + fiber coordinates ↦ fine configuration, with
  the head coordinate right-corrected so the block map is a left inverse
  on the nose: `layerBlockMap hN (layerBlockAsm hN U w) = U`) and the
  block map `layerBlockMap`.
- **Transport** (§3): assembly and block map are measure-preserving for
  the pi Haar measures (`measurePreserving_layerBlockAsm`,
  `measurePreserving_layerBlockMap`), through the octet assembly/split
  rectangle computations and the middle-exchange regrouping
  (`layerBlockProdComm`, also measure-preserving, §4).
- **Fiber-integrated blocked kernel** (§4): `blockedLayerKernel hN β U U′`
  = the integral of the fine layer kernel over the **product** fiber
  measure ∂(μW.prod μW); `blockedLayerKernelFun` its kernel function;
  `blockedLayerKernelFun_memLp` — the MemLp datum (domination by
  C = exp(|β| · layerBoundConst N), the corpus's own kernel bound).
- **Pullback-pairing identity** (§5): `blockedLayerPairing_eq` — the
  blocked pairing of a coarse observable F′ against the blocked kernel
  equals the fine pairing of the block pullback
  `F′.compMeasurePreserving (layerBlockMap hN) MP` against the fine
  layer kernel.

Strict count: **43 theorems** for the package (§1: 8, §2: 5, §3: 15,
§4: 10, §5: 5), against the scoping estimate of 12–28 for PROP-0 +
PROP-1A combined. The overshoot is transport infrastructure: the octet
assembly/split, currying, and regrouping measure-preservation chain had
no corpus precedent and is priced here on the face.

Axiom check (`#print axioms`): every headline checked —
`blockedLayerKernelFun_memLp`, `blockedLayerPairing_eq`,
`blockedLayerKernelFun_posKernel_of_layerKernelPosAll`,
`measurePreserving_layerBlockAsm`, `measurePreserving_layerBlockMap`,
`measurePreserving_layerBlockProdComm`,
`blockedLayerKernelPullback_integrable` — depends on **exactly**
{propext, Classical.choice, Quot.sound}. Fence trio only.

## 3. PROP-1A — LANDED (T1, conditional)

`blockedLayerKernelFun_posKernel_of_layerKernelPosAll`: GIVEN
`LayerKernelPosAll μG ρ hρcont β` (the all-of-L² positivity of the fine
layer kernel — **the hypothesis is named on the face, not discharged in
this lane**), the blocked layer kernel is positive at the `PosKernel`
level, by one application of `blockedLayerPairing_eq`. This is the
trivial (pullback) direction of propagation, landed as bookkeeping
infrastructure — K-PROP-VAC is noted against it on the module's face:
it transports positivity across one blocking step for `PosKernel`-level
statements and says nothing about the gauge-invariant class
(`LayerKernelPos`), margins, or iteration.

State note: since this lane branched (30eec70), the positivity bridge
lane has landed in the main tree (BRIDGE-MAIN:
`LayerKernelPos + hρcont ⇒ LayerKernelPosAll`; census 13,037 strict /
473 modules, fence 136/136, CI green on 0db8f428), so on the main tree
the hypothesis above is now discharged modulo `LayerKernelPos` itself —
which remains neither proved nor refuted. Whether and how PROP-1A is
composed with the bridge is the parent ceremony's decision; this lane
keeps the hypothesis named, per its scope.

## 4. Kills register

- **K-PROP-FORM — FIRED (T2, probe seat).** See §1: the blocked kernel
  is not of Wilson layer form; PROP-0 defines the new species instead.
- **K-PROP-INV — not fired.** Blocked pairing PSD at every sampled β.
- **K-PROP-MARGIN — not fired.** Margin ratio exactly 1 at the seat.
- **K-PROP-VAC — armed.** Guard against vacuous all-of-L² restatements;
  PROP-1A is labeled bookkeeping-grade on its face for this reason.

Not in this run, per scope: PROP-1B as a build (dominated by the
bridge), PROP-2 as a build (false — probe only), PROP-3 as a build
(Stage 3c, research-scale).

## 5. Ceiling

One-step propagation at the `PosKernel` level is **infrastructure for
an attack on Stage 3c, not the attack**: nothing here addresses
positivity on the gauge-invariant class under blocking (the bridge's
and W3's territory), margin floors under iteration, or any continuum
statement. **NO CLAIM on any Millennium Problem; parts closed 0;
dials 0/4.**

## 6. Ceremony cleanup note (2026-11-04)

The first ceremony attempt stopped at its build step: the main-tree
build was green (3675 jobs, zero sorrys, recount 43 exact) but the
module was **not warning-clean** — 26 linter warnings (15 unused
section variables, 4 unreferenced variable names, 3 deprecations
`if_pos`/`if_neg`, 2 unused simp arguments, 2 `haveI` style
suggestions). The copied files were removed from the main tree
untracked (tree restored to ba2f6db clean; nothing was committed or
pushed), and the module was cleaned **in this lane** under the house
standard (SP-5 and the positivity bridge both shipped warning-clean).

Cleanup, cosmetic only — every theorem statement byte-identical;
proof terms changed only where a warning fix required it:
`omit … in` for the unused section variables (in this Mathlib pin
`omit` must precede the doc comment, not follow it — eight sites
needed that ordering); the `omit` fixes cascade one dependency layer
at a time (a callee's dropped instance arguments make the caller's
copies unused), so the final omit set covers 25 theorems;
`if_pos`/`if_neg` renamed to their non-deprecated forms
`ite_eq_left`/`ite_eq_right`; unreferenced binders underscored
(`_z`, `_v`, `_q`, `_r`); the two unused simp arguments dropped;
`haveI` → `have` at the two style-flagged sites.

Re-verification in the lane after cleanup: module build green
(3675 jobs), **zero warnings for the module**, zero errors, zero
sorrys; strict recount **43 theorems** (unchanged); `#print axioms`
on all seven headlines (§2) — exactly
{propext, Classical.choice, Quot.sound}. The cleanup lands as a
separate lane commit on top of ec5b58b; the ceremony resumes from
the copy step against the cleaned module.

## CEREMONY (parent, resumed 2026-11-03)

Integrated into the main tree from `prop-lane` — the lane's
landing commit `ec5b58b` plus its cleanup commit `c76ba2a`
(§6) — onto main HEAD `ba2f6db` (positivity bridge ceremony);
module and this dossier copied **byte-identical** to the
cleaned lane commit (diff-verified against `c76ba2a`). The
lane was based on `30eec70`; the base advanced under it (the
bridge landed meanwhile), and the integration is onto the
advanced HEAD with no name drift — no touch to the module
was needed, not even an import line.

- **First attempt, on the record:** the ceremony stopped at
  its build step. That build was green (3675 jobs, zero
  sorrys, recount 43 exact) but the module carried 26
  cosmetic linter warnings. The copied files were removed
  untracked, the main tree restored to `ba2f6db` clean
  (nothing committed or pushed), and the module was cleaned
  in the lane under the house warning-clean standard
  (parent decision, option (a)) — §6 has the full episode.
- **Build (resumed):** main-tree targeted build
  `lake build ThetLogos.PositivityPropagation` green,
  3675 jobs (matching the lane exactly); zero sorrys;
  module warning-clean (zero warnings for the module;
  pre-existing dependency warnings only).
- **Recount:** module 43 strict — exact match with the
  lane. Corpus census (FILES-TRUE, method of record:
  whole-tree recount 13,749 strict over 489 files, counter
  re-validated in-run against TritGrading 27,
  MirrorTwentyOneTriplets 32, GateItem6 15, OneKernel 20,
  OddRing 15, AxiomTetPartnerIso 13, PosBridge 29; minus
  the frozen pre-ledger remainder 669 strict / 15 files):
  **13,080 strict / 474 modules** (13,037/473 → +43/+1).
  README prose census and shields badge both updated to
  13,080 / 474, kept equal.
- **Fence:** the 7 dossier-named headlines admitted
  (`blockedLayerKernelFun_memLp`, `blockedLayerPairing_eq`,
  `blockedLayerKernelFun_posKernel_of_layerKernelPosAll`,
  `measurePreserving_layerBlockAsm`,
  `measurePreserving_layerBlockMap`,
  `measurePreserving_layerBlockProdComm`,
  `blockedLayerKernelPullback_integrable`) WITH the
  `import ThetLogos.PositivityPropagation` line in the same
  commit as the module (CI lesson) — **FENCE PASS 143/143**,
  every headline on exactly
  {propext, Classical.choice, Quot.sound}, no sorryAx.
- **Ledger:** record `positivity-propagation` (standing,
  T3) — PROP-0 FULL + PROP-1A FULL-conditional at T1;
  K-PROP-FORM fired at T2 at the probe seat (its T1 sibling
  is RG-1 at the measure level); K-PROP-INV / K-PROP-MARGIN
  not fired (margin probe ratio exactly 1.0, atmosphere);
  the BRIDGE-MAIN composition reading on its face (with
  BRIDGE-MAIN in the tree, PROP-1A's named hypothesis
  LayerKernelPosAll is discharged modulo LayerKernelPos +
  hρcont, so blocked-kernel PosKernel positivity holds
  modulo LayerKernelPos — a reading of two landed theorems,
  no new Lean content); the cleanup episode on its face.
  Validator PASS, 20 records.
- **Ceiling restated:** one-step `PosKernel`-level
  propagation is infrastructure for an attack on Stage 3c,
  not the attack. **NO CLAIM; dials 0/4.**
