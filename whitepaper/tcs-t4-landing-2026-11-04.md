# TCS T4 — K-PROP-FORM promoted to a theorem

## VERDICT: FULL — the measured-configuration statement lands as a theorem (T2 → T1 promotion complete), at full strength

Module: `lean/ThetLogos/BlockedKernelDiagNotOne.lean` (NEW module; no
landed module edited). Lane: `tcs-t4-lane`, cut from main HEAD
`d6f17cf` (census 13,248 strict / 488 modules; fence 286/286).
Targeted build green (3,676 jobs), ZERO sorrys, module WARNING-CLEAN
(no build warning names the module), no `native_decide`. Measured
strict count: **23** (23 theorems, 10 defs, 3 instances) — the priced
band was 10–20, EXCEEDED by 3; itemized below. NO integration, NO
push — lane commit only. NO CLAIM; dials 0/4.

## What landed

**Headline** (`blockedKernelDiag_seat_ne_one`): at the PROP-2-PROBE
seat — `N = 2`, `G = Multiplicative (ZMod 2)`, the sign character
`flowSignRep`, the uniform probability measure `μG₀` — for **every**
coarse configuration `U` and **every** `β ≠ 0`,

```
blockedLayerKernel μG₀ flowSignRep blockedSeatH β U U ≠ 1
```

about the landed `blockedLayerKernel` definition itself.
`blockedKernelDiag_seat_one_ne_one` is the `β = 1` measured point.
This is stronger than the registered shape (one configuration, one
`β`): the whole `β ≠ 0` range at every coarse datum at the seat is
separated from `1`. The pre-registered grades: FULL = the
measured-configuration statement lands as a theorem — met.
**K-TCS-SCALE did NOT fire** (no `β ≠ 0` in the range returns
diagonal `= 1`; the KILL branch — closed form evaluating TO 1 at
the configuration — is refuted by the theorem, not triggered).

| Declaration | Content |
|---|---|
| `blockedSeatH` | the evenness datum `Even 2` for the seat (axiom-free) |
| `blockedSeatSite_apply` / `blockedSeatSite'_apply` | coordinates of the distinguished site `(1,0,0)` and its direction-2 shift `(1,1,0)` |
| `blockedSeatSite'_ne` | the shift is a different site |
| `blockedSeatLink_octet` | the distinguished link has octet index `1` (first tail offset) |
| `blockedSeatAsm_apply` | at the distinguished link the assembly reads the fiber's first tail coordinate, for every `U` |
| `blockedSeatPlaquette_word` | the distinguished plaquette word `α c * v' ℓ * (α c')⁻¹ * (v ℓ)⁻¹` read off `layerConfig` |
| `blockedSeatDensity_mem` | every seat plaquette density lies in `[0, 2]` |
| `blockedSeatDensitySum_nonneg` / `blockedSeatDensitySum_ge` | the action's density sum is nonnegative and dominates the distinguished density |
| `blockedSeatDensity_eq_two` | on the pinned data the distinguished density is exactly `2` (word = nonidentity element) |
| `blockedSeatBoltzmann_bounds_pos` / `_neg` | for `β ≥ 0` the Boltzmann factor is `≤ 1`, and `≤ exp (−2β)` when frustrated; mirrored for `β ≤ 0` |
| `blockedSeatJ_integrable` | the Boltzmann factor is integrable on the merged fiber × fiber × stratum probability space |
| `blockedKernelDiag_seat_ofReal` | the blocked diagonal at the seat is the coercion of the real average `blockedSeatJ β U` |
| `blockedSeatBadSet_measurable` / `blockedSeatBadSet_measure` | the bad rectangle is measurable with measure `(1/2)⁴`, real measure `1/16` |
| `blockedSeatBadAvg` | the comparison function `1 + (exp (−2β) − 1)·1_B` integrates to `1 + (exp (−2β) − 1)/16` |
| `blockedSeatDensity_two_of_mem` | on the bad rectangle the distinguished plaquette is fully frustrated, for every `U` |
| `blockedSeatJ_lt_one` / `blockedSeatJ_gt_one` | `J(β) < 1` for `β > 0`; `J(β) > 1` for `β < 0` |
| `blockedKernelDiag_seat_ne_one` | HEADLINE: diagonal `≠ 1` at every `β ≠ 0`, every `U` |
| `blockedKernelDiag_seat_one_ne_one` | the `β = 1` measured point |

Axiom audit (`#print axioms` on all 23): the 22 proof theorems
depend on exactly `{propext, Classical.choice, Quot.sound}` —
no `sorryAx`, nothing outside the standard trio; `blockedSeatH`
depends on no axioms. Declaration-collision scan of all 33 new
names against the main tree at HEAD `d6f17cf`: ZERO collisions.

## Route: the bound route, NOT the closed form — and the discrepancy, on the face

The firing brief directed a proof via a closed-form diagonal
formula in a module `Span3BlockDiagClosedForm.lean` (declarations
`exppoly`, `blockDiagExp`, `block_kernel_diag_eq`,
`diagKernelDiag`) and quoted measured values (blocked diagonal
`0.48456790192851827` at `β = 1`; K-side values
`0.9305071207660656 / 0.9106595539283076`; trace
`5.7785505194669195`; jump gap `0.019847566837758`). **None of that
module, those declarations, or those numbers exists anywhere in
the repository or workspace** (tree-wide grep over `lean/`,
`whitepaper/`, and `~/workspace/your_files/`, excluding `.lake` /
`.git`: zero hits outside this lane's own header note). The
verifiable record of K-PROP-FORM is PROP-2-PROBE in
`positivity-propagation-landing-2026-11-03.md` §1 and its probe
output `~/workspace/your_files/positivity-propagation-probes-2026-11-03.txt`:
closed form `𝒜^{[2]}(U,U) = (A′⁸ + B′⁸)³` with
`A′ = (1+e^{−2β})/2`, `B′ = (1−e^{−2β})/2`; sampled diagonals
`{1.213658e+15, 1.104421e-04, 1.729662e-06, 4.904120e-07}` at
`β ∈ {−1, 0.5, 1, 2}` — the `β = 1` value is `1.729662e-06`, not
`0.4846`. This build therefore promotes the scoping's registered
T4 statement against the objects that exist: the landed
`blockedLayerKernel` at the probe's explicit seat data. If a
second measured configuration was intended, it is not in the tree
and would need pinning.

The fiber character sum `(A′⁸ + B′⁸)³` is not reproduced. Instead
the diagonal is proved to be a positive real average `J(β)` of
Boltzmann factors over the merged probability space, strictly
separated from `1` by a rectangle argument: every factor is on one
side of `1` (density sum `≥ 0`), and on an explicit rectangle of
measure `1/16` — one fiber coordinate on each side and two stratum
coordinates pinned so the assembly at the distinguished link reads
the pinned fiber value — the distinguished plaquette is fully
frustrated (density exactly `2`), pushing the factor past
`exp (−2β)`. Integrating the comparison function gives
`J(β) ≤ 1 − (1 − exp (−2β))/16 < 1` for `β > 0` and the mirror
bound for `β < 0`. No floating-point decision anywhere; no
`native_decide`; the only `decide` uses are closed `Fin`/`ZMod`
coordinate facts.

## Strict count vs the priced band (flagged)

Priced band (TCS scoping §3-T4): strict 10–20. Landed: **23**.
Composition: the planned 19, plus four load-bearing additions —
`blockedSeatSite'_apply` (coordinate computation feeding
`blockedSeatSite'_ne`), `blockedSeatBadAvg` (the comparison
integral both separation proofs consume), `blockedSeatDensity_two_of_mem`
(the transfer from rectangle membership to plaquette frustration),
and `blockedSeatH`, planned as a `def` (count-neutral) but landed
as a `theorem` because this pin's `linter.defProp` requires
proposition-valued definitions to be theorems (+1 strict).

## Pin findings recorded during the build

- `Measurable.comp` against a `layerBlockAsm`-headed function at
  the *concrete* seat times out at `whnf` (200k heartbeats) during
  the projected-application defeq `(f z).1 =?= U`; at generic `N`
  (the corpus's own uses) it does not arise. Keeping every
  intermediate measurability in `∘`-form (comp-shaped types, never
  a projected application) avoids the defeq entirely — the
  measurability chain in §3 is written that way deliberately.
- In this pin the preimage lemma is `measurableSet_preimage`;
  `Measurable.measurableSet` does not exist, and dot notation
  `.measurableSet` on a `Measurable` term resolves unstably.
  `measurable_pi_apply` at a *concrete* subtype site likewise
  needs the `Measurable` type fully annotated (the hfiber pattern)
  before application.
- `Measure.real_univ` does not exist in this pin; `μ.real univ = 1`
  is proved through `measure_univ` + `ENNReal.toReal_one` under a
  definitional `show`. `integral_ofReal` rewrites fail on the
  corpus's coercion form but close by `exact` (defeq).
- `if_pos` / `if_neg` and `Set.mem_setOf_eq` are deprecated in
  this pin (`ite_eq_left` / `ite_eq_right`, `Set.mem_ofPred_eq`).

## Standing

NO CLAIM on any Millennium Problem; parts closed 0; dials 0/4.
This is a finite, fully explicit seat statement about a landed
finite blocking definition — it closes the T4 line of the TCS
scoping (T1 and the equivalence/division pins remain as registered
there, Jeff's hand). Integration is the parent's step.

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from tcs-t4-lane commit `6cfebe3` (lane base `d6f17cf`)
onto main-tree HEAD `7567e28` (SHADOW-TEST-1 integration). Module +
this dossier copied **byte-identical** (md5 `85707bdf…`
BlockedKernelDiagNotOne, `08238bc6…` dossier; diff-verified).
Declaration-level collision scan of all 33 T4 declaration names
plus the module name against the main tree at HEAD found **zero
collisions**; module + dossier are new files.

- Main-tree targeted build green (**3676 jobs**, matching the
  lane), zero sorrys (zero-sorry source gate PASS, 506 files),
  **module warning-clean** (no build warning names the module).
- Recount exact: BlockedKernelDiagNotOne **strict 23 + 10 defs +
  3 instances** (whole-tree 13,976/506 minus frozen remainder
  669/15).
- Fence admissions: all **23 strict theorems** with
  `import ThetLogos.BlockedKernelDiagNotOne` in the **same
  commit** as the module — **FENCE PASS 345/345** (322 → 345).
  The 22 proof theorems sit on exactly {propext, Classical.choice,
  Quot.sound}; `blockedSeatH` was admitted with an **empty axiom
  set**, per the registry's reduced-axiom precedent (cf. U-3b's
  no-axiom admissions); no `sorryAx` anywhere.
- Ledger record `tcs-t4-blocked-kernel-diag-not-one` (standing,
  T3, kill_id null — K-TCS-SCALE did not fire; the kill branch is
  refuted by the headline theorem itself); validator PASS,
  37 records.
- Census (FILES-TRUE, method of record): **13,284/490 →
  13,307 strict / 491 modules**; README prose census and badge
  both 13,307 / 491, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`) and in the commit
  message's own record chain. NO CLAIM; dials 0/4.

### ERRATUM — the firing brief's phantom data (recorded discrepancy)

The T4 firing brief quoted a module `Span3BlockDiagClosedForm.lean`
(declarations `exppoly`, `blockDiagExp`, `block_kernel_diag_eq`,
`diagKernelDiag`) and measured values (blocked diagonal
`0.48456790192851827` at `β = 1`; K-side values
`0.9305071207660656 / 0.9106595539283076`; trace
`5.7785505194669195`; jump gap `0.019847566837758`). At integration
the main tree was grep-searched for every one of these identifiers
and numbers (`git grep` over tracked `whitepaper/` + `lean/`, plus
a working-tree pass over the untracked files): **zero hits,
everywhere** — the phantom data exists in no file in the main
tree, and in particular **no landed dossier or other public face
carries it** (the PROP landing dossier,
`positivity-propagation-landing-2026-11-03.md`, records
PROP-2-PROBE, not the phantom figures), so no other dossier
required an erratum append; this block and the ledger record are
the correction's home. **The verifiable record is PROP-2-PROBE**
(`positivity-propagation-landing-2026-11-03.md` §1): closed form
`𝒜^[2](U,U) = (A′⁸ + B′⁸)³`, `A′ = (1+e^{−2β})/2`,
`B′ = (1−e^{−2β})/2`; sampled diagonals `{1.213658e+15,
1.104421e-04, 1.729662e-06, 4.904120e-07}` at
`β ∈ {−1, 0.5, 1, 2}` — the `β = 1` diagonal is `1.729662e-06`.
(One name-collision nuance for the record: an unrelated `exppoly`
family genuinely exists in `GibbsSpanLattice.lean` /
`KMSModularDoubling.lean`; it is not the brief's closed-form
module and carries none of the phantom values.) The promotion
above was proved against the landed `blockedLayerKernel` at the
probe's explicit seat data, by the bound route — see the Route
section of this dossier.
