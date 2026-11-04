# W3 REMAINDER R6 — THE FINAL ASSEMBLY AT THE FACTOR CLASS: LANDED **FULL**

**Date:** 2026-11-04. **Lane:** `w3r6-lane` (worktree `~/workspace/thet-logos-r6`), cut from main HEAD `8eaf57d` (census 13,117 strict / 480 modules; fence 175/175). **Module:** `lean/ThetLogos/Span3SeatSchurGateW3Assembly.lean`. **Lane commit only — NO integration, NO push** (integration is the parent's sequence).

## Outcome vs the pre-registered shapes

**FULL** — the primary shape, no narrowing. The assembly and the headline landed at the factor class exactly as registered under Jeff's decisions of 2026-11-03 (23:11 "R6 enters at the factor class"; 23:14 "open it"). No PARTIAL residue; the KILL shape did not arise: every consumption shape of item 6's assembly was fed at the factor class in its exact form.

## What landed (strict 16 + 1 def, measured)

Targeted build green (3680 jobs), **zero sorrys**, **warning-clean**, no `native_decide`. One style knob in-tree-precedented: `set_option maxHeartbeats 1600000 in` on the P1-variant only (its Fubini chain is heartbeat-heavy at the default limit; same value as `BosonicInteraction.lean`).

Headline results:

| Result | Content |
|---|---|
| `seatPairing_pullTop_eq_layerPairing₂_fiberAvg_factor` | **P1 at the factor class** — item 6 P1's off-diagonal fiber identity with the banked `hMarg` replaced by R1's re-pin, side condition discharged at the use sites (below). |
| `seatPairing_dressed_marginal_nonneg_factor` | P2-variant: marginal dressed pairing ≥ 0 at the factor class. |
| `seatPairing_dressed_folded_nonneg_factor` | P3-variant: folded dressed pairing ≥ 0 at the factor class (takes `4 ≤ N`, inherited from R2c's invariance headline). |
| `gate4c_hyp6_at_factor_class` | **Hypothesis 6 at the factor class**: GATE-4C hyp 6's verbatim conclusion ∀ f (hyp-6 prefix) ∀ φ' ∈ factor class (`MemLp 2` on the layer pi measure), at `4 ≤ N`, modulo `LayerKernelPos` + `hρcont`. |
| `seatSchurTarget_of_approxProductStep_factor` | The GATE-4C conditional as a variant entry: hyp 6 required **only at the expansion's factors** (with `hφMem` carried on the data); hyps 4/5 verbatim. |
| `seatSchurProductStepOpen_discharge_gate4_factor` | **The W3 headline at the factor class**: `∀ hN hN4 β, 0 < d → Continuous repMatrix → seatSchurProductStepOpen μG ρ hN β`, the target's own hypotheses (`0 ≤ β`, `LayerKernelPos`) consumed in their registered slots. |

Supporting lemmas (10): kernel-slice measurability ×2 (`aestronglyMeasurable_layerKernel_tauTop_right/left`, via the kernel's site-integral form and partial integrals — Item6's own technique), use-site integrabilities ×2 (`integrable_mul_layerKernel_tauTop_right`, `integrable_conj_mul_layerKernel_pullTop`), the assemble transport (`splitEquiv_assembleTop`, `assembleTransport` [the 1 def], `assembleTransport_apply`, `measurePreserving_assembleTransport`), fiber-average regularity ×2 (`aestronglyMeasurable_fiberAvgTop_of_memLp`, `integrable_fiberAvgTop_of_memLp` — fiber averaging is an L¹ contraction on `MemLp 2` data), and the seat×layer kernel measurability (`aestronglyMeasurable_layerKernel_layer_tauTop`).

**Axioms** (`#print axioms`, scratch check, not shipped): all six headline results on exactly **{propext, Classical.choice, Quot.sound}** — inside the fence.

## The use-site discharge route (R6's core wiring)

R1's re-pin `fiberAvgTop_marginal_of_integrable` is consumed at the three sites inside P1 where the banked `hMarg` was applied, each time with its integrability side condition discharged from the factor-class data:

1. **Inner site** (Ψ = layer-kernel slice at the pulled left configuration `tauTop z`): side condition `Integrable (fun z' => a z' * layerKernel (tauTop z) (tauTop z'))` — `Integrable.mul_bdd`: `a ∈ L¹` (from `MemLp 2`, finite measure) times the slice, a.e. strongly measurable by the site-integral/partial-integral route and uniformly bounded by `layerKernel_norm_le`.
2. **Outer site** (Ψ = the inner layer pairing against `fiberAvgTop a`): the single seat integrability of `conj (b z) * Ψ (tauTop z)` is proved by a two-sided Fubini chain on the seat×seat and seat×layer products — product integrabilities from the factor-class Cauchy–Schwarz core (`integrable_pullTopKernel_mul_of_memLp_slots`, slots `(conj∘b, a)`) and from `L¹ × L¹` (`Integrable.mul_prod`) times the bounded pulled kernel — with the marginal identity itself re-applied at the conjugate slot (side condition = the two-sided pulled-slice integrability) and at the final layer site (side condition = site 1's lemma at the layer configuration).
3. **Product integrability** (`hInt`, P1's own hypothesis in item 6): discharged inside the P1-variant by the same slots core at `(a, conj∘b)`.

The dressed integrabilities (item 6 P4's `hInt`/`hIntFold` inputs) are consumed in their exact shapes inside the P2/P3 variants: the dressed observables are `MemLp 2` by R2d+R3a's `memLp_factor_pullback` + `memLp_mul_of_aestronglyMeasurable_bounded` (twirl AESM + twirl bounds; folded side also the half-action weight bound `norm_exp_neg_halfActionP_le`), and the pairing integrability is then the slots core at the dressed slots. R2d+R3a's packaged `gate4c_hyp6_integrability_inputs_of_memLp_factor` stands as an independent discharge of the same two shapes (not separately consumed). Cross inputs: R2b's `fiberAvgTop_dressed_folded_cross_proved` (headline) and `fiberAvgTop_dressed_marginal_cross_proved` (corollary) — consumption credit with R2b, per the standing disposition; R2a's independent proof not consumed. Folded invariance: R2c's `fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved`. Marginal invariance: G2c's discharged `.1`. Hypothesis 4 at the headline: R2d+R3a's `hIntStage_gramFactors` (the data's own entry). Hypothesis 5: item 6 P5 `hIntLim_of_continuous_repMatrix` (regular case). Expansion data: item 5's compression re-derived in Gram form (`exists_seq_tendsto` at `LayerKernelPosAll` from the positivity bridge `layerKernelPosAll_of_layerKernelPos`; `seat_stage_memLp`, `seat_stage_eLpNorm`; factors' membership by `Lp.memLp`).

## Scope fences (unchanged, on every face)

- Hypothesis 6 closes **AT THE FACTOR CLASS ONLY**. The frozen ∀-form over bare `φ'` is NOT proved and NOT claimed.
- The frozen GATE-4C conditional `seatSchurTarget_of_approxProductStep_gate4c` is NOT proved (its hyp 6 is the ∀-form); the frozen Repin headline `seatSchurProductStepOpen_discharge_gate4` is NOT proved (it carries neither `0 < d` nor `hρcont` — the factor-class headline takes both).
- Hypothesis 4 is consumed at the factor class and (elsewhere) in item 6 P6's regular case; arbitrary data is covered by neither — **W3's remaining item (hyps 4/5 beyond their landed scopes) stands open**, untouched except as the assembly states.
- `LayerKernelPos` and `hρcont` remain standing hypotheses, discharged nowhere here. `LayerKernelPos` enters the headline only through `SeatSchurTarget`'s own hypothesis slot.
- GATE-3 untouched. All frozen statements in the input modules UNEDITED — the assembly lives entirely in the new module.
- **NO CLAIM; dials 0/4.** Nothing here proves FACT, clause (a), `𝒜 ⪰ 0`, or any uniformity/continuum statement.

## Residues named

None inside the registered scope. The standing residues outside it are the frozen ∀-forms of hyps 4/6 and W3's remaining item, as fenced above — pre-registered, not new.

## For the parent's integration (not done in this lane)

- New module only: `lean/ThetLogos/Span3SeatSchurGateW3Assembly.lean` (+ this dossier). Nothing else in the tree was modified (the lane's `.lake` was copied from the main tree at lane creation).
- Census delta if integrated as-is: **+16 strict, +1 def, +1 module** (recount at integration, per standing discipline).
- Fence admissions (dossier-named): the six headline results in the table — all on {propext, Classical.choice, Quot.sound}.
- Suggested ledger wording: "W3 hyp 6 CLOSED AT THE FACTOR CLASS modulo LayerKernelPos + hρcont (R6 assembly); the W3 expansion headline stands at the factor class (`seatSchurProductStepOpen_discharge_gate4_factor`, with `0 < d` + `hρcont`); frozen ∀-forms of hyps 4/6 and the Repin headline remain open; W3's remaining item (hyps 4/5 beyond landed scopes) open."

## INTEGRATION — 2026-11-04 — parent integration into the main tree

Integrated from lane commit `61601de` onto current
main-tree HEAD `699b926` (the Universal Bridge integration;
the lane was cut from `8eaf57d`). Step 1: main tree tracked
files clean (untracked `SweepAll.lean` + old whitepaper
drafts left alone), module + dossier new files, and the
declaration-level collision scan of all 17
`Span3SeatSchurGateW3Assembly` names against the main tree
found ZERO collisions. No drift in the module's
dependencies: the intervening main-tree commits touch none
of its inputs — the Marg / FactorInt / InvFold / CrossFold
/ item-6 / GATE-4C modules were all integrated before the
lane was cut. Module + dossier copied BYTE-IDENTICAL
(md5-verified: module `12539021f9aa13eb3ed512706bdaa3cf`,
dossier pre-integration
`ae6bcd50b9b8a9b13816c19aff7fa620`). Main-tree targeted
build `lake build ThetLogos.Span3SeatSchurGateW3Assembly`
green (3,680 jobs, matching the lane), zero sorrys, module
WARNING-CLEAN (no build warning names
`Span3SeatSchurGateW3Assembly.lean`). Recount: module
strict 16 + 1 def exact; census FILES-TRUE 13,164/482 →
**13,180 strict / 483 modules** (whole-tree 13,849/498
minus frozen remainder 669/15); README prose + badge both
13,180/483, kept equal. Fence: the six dossier-named
headline results admitted WITH
`import ThetLogos.Span3SeatSchurGateW3Assembly` in the same
commit as the module — FENCE PASS **213/213**, every new
headline on exactly
`{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
Ledger record `w3-r6-assembly` (standing, T3), validator
PASS 29 records. Verdict face unchanged: **THE FINAL
ASSEMBLY AT THE FACTOR CLASS — hypothesis 6 CLOSED AT THE
FACTOR CLASS modulo LayerKernelPos + hρcont** (P1-variant
consumes R1's re-pin with its integrability side condition
discharged at all three internal use sites; cross pair
consumed from R2b with credit staying with R2b; folded
invariance from R2c); headline
`seatSchurProductStepOpen_discharge_gate4_factor`
(`seatSchurProductStepOpen` at every `4 ≤ N`, every β,
`0 < d`, under `hρcont`; hyp 4 via R2d+R3a's gram-factor
entry, hyp 5 via item 6 P5). SCOPE FENCES: frozen ∀-forms
of hyps 4/6 NOT proved; frozen GATE-4C conditional and
frozen Repin headline NOT proved (the factor-class headline
carries `0 < d` and `hρcont`, which the Repin headline does
not); `LayerKernelPos` and `hρcont` REMAIN standing
hypotheses; W3's remaining item (hyps 4/5 beyond landed
scopes) OPEN; GATE-3 untouched. **NO CLAIM; dials 0/4.**
