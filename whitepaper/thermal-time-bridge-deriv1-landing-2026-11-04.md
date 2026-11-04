# DERIV-1 — the thermal-time bridge's twelfth clause, landed

## VERDICT: FULL — the derivative clause lands as the bridge dossier states it; the bridge is complete at twelve clauses

Module: `lean/ThetLogos/ThermalTimeBridgeDeriv.lean` (NEW module; no
landed module edited). Lane: `deriv1-lane`, cut from main HEAD `7e2b5f5`
(census 13,243 strict / 487 modules; fence 281/281). Targeted build
green (3,587 jobs), ZERO sorrys, module WARNING-CLEAN (no build warning
names the module), no `native_decide`. Measured strict count: **5**
(5 theorems, 0 defs) — inside the priced S–M band of 4–10, not
exceeded. NO integration, NO push — lane commit only.

## What landed

| Declaration | Content |
|---|---|
| `modularFlow_exp_arg_pos` | `(Complex.I * (s:ℂ)) • K = s • (Complex.I • K)` — the flow's positive exponential argument as a real scalar multiple of the generator line |
| `modularFlow_exp_arg_neg` | `(-(Complex.I * (s:ℂ))) • K = s • (-(Complex.I • K))` — the negative argument likewise |
| `modularFlow_hasDerivAt_zero` | `HasDerivAt (fun s : ℝ => modularFlow K s A) (modularFlux K A) 0` — DERIV-1 at the `modularFlow` seat |
| `GibbsClock.flow_hasDerivAt_zero` | `HasDerivAt (fun s : ℝ => G.flow s A) (modularFlux G.generator A) 0` — DERIV-1 in the exact shape the bridge dossier's residue names |
| `GibbsClock.thermal_time_bridge_complete` | the conjunction of the eleven landed clauses of `GibbsClock.thermal_time_bridge` (consumed unedited) with the twelfth clause `(∀ A, HasDerivAt (fun s => G.flow s A) (modularFlux G.generator A) 0)` |

Axiom audit (`#print axioms`, in-module): every one of the five
declarations depends on exactly `{propext, Classical.choice,
Quot.sound}` — no `sorryAx`, nothing outside the standard trio.

The proof is the dossier's registered skeleton, repaired: each
exponential factor's real-line derivative comes from
`hasDerivAt_exp_smul_const` at field `ℝ`
(`hasFDerivAt`/`hasDerivAt_exp_smul_const` of
`Mathlib/Analysis/SpecialFunctions/Exponential.lean`), the factors are
assembled by `HasDerivAt.mul_const` and `HasDerivAt.mul`, the value at
`0` reduces by `exp_zero`, and the resulting
`(Complex.I • K) * A + A * (-(Complex.I • K))` is identified with
`modularFlux K A` by smul algebra. The assembled statement is then
transported from the generator-line form to `modularFlow`'s own form
by `HasDerivAt.congr_of_eventuallyEq` over the two argument identities
above (equality of functions everywhere, not merely eventually).

## Route taken: A (scoped Frobenius norms) — and the obstruction, re-verified and refined

Route B (entrywise / diagonal dialect) was NOT needed.

The bridge dossier's obstruction re-verifies in the pin: with the
corpus's own import context, matrices carry no canonical `NormedRing`
instance (all normed-ring instances in
`Mathlib/Analysis/Matrix/Normed.lean` are scoped opt-ins), so the
clause cannot be formed there. Two refinements the lane established
against the pinned Mathlib source:

1. **The exponential-agreement step collapses.** The dossier's Route A
   asked to "prove the normed exponential agrees with the corpus's
   topological `modularFlow`." In this pin there is nothing to prove:
   `NormedSpace.exp` is a single `irreducible_def`
   (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`) defined as the
   sum of `expSeries ℚ 𝔸`; it takes no field argument and does not
   depend on any norm instance. The exponential differentiated in this
   module is definitionally the same constant as the one
   `modularFlow` is built from. What the Frobenius scope changes is
   only the instance arguments carried inside the `HasDerivAt` *type*
   (the normed-group / normed-space / topology data the derivative
   predicate quantifies over) — which is exactly the dialect the
   dossier registers for this route. The clause is therefore stated,
   honestly, **in the Frobenius dialect**: every norm-sensitive
   declaration above is elaborated under a per-declaration
   `open scoped Matrix.Norms.Frobenius in`, the instances are local to
   those declarations, and nothing leaks into the ambient instance
   context (no global instance changes; `ThermalTimeBridge.lean` and
   every other landed module untouched).

2. **The instance discipline is load-bearing.** The `HasDerivAt` type
   carries its `TopologicalSpace` argument separately from its
   normed-group argument, and the two are synthesized by different
   paths: a statement signature elaborated without the scope fills the
   topology slot with the canonical Pi instance, while the
   exp-calculus lemmas produce the Frobenius-metric projection chain —
   two genuinely different terms, and `exact`/`simpa` fail on the
   mismatch (verified in-lane probes). Keeping the per-declaration
   `open scoped … in` form for BOTH the statements and every lemma
   application makes all synthesis paths agree; section-level
   `attribute [local instance]` on the Frobenius defs does NOT
   reproduce this agreement (also verified in-lane). This is the same
   pattern Mathlib itself uses in
   `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
   ("attribute [local instance], then the usual lemmas about
   NormedSpace.exp are fine").

Also recorded: `HasDerivAt.comp_ofReal` in this pin is stated only for
`ℂ → ℂ` functions, which is why the bridge lane's original attempt
(`hasDerivAt_exp_smul_const'` + `comp_ofReal`) could not reach the
matrix-valued flow; the ℝ-field form of `hasDerivAt_exp_smul_const`
needs no real/complex composition at all, since `NormedAlgebra ℝ
(Matrix … ℂ)` synthesizes under the Frobenius scope. The failed
attempt's product-rule skeleton was otherwise sound and is the one
used here.

## Grade against the pre-registered shapes

**FULL.** The clause lands in the dossier's named shape —
`HasDerivAt (fun s => G.flow s A) (modularFlux G.generator A) 0` —
and the completion corollary closes the bridge: all twelve clauses of
the finite thermal-time bridge now stand in one conjunction, the
first eleven consumed from the integrated
`GibbsClock.thermal_time_bridge` unedited. The one dialect
qualification is the one Route A pre-registers: the twelfth clause's
`HasDerivAt` is formed under the scoped Frobenius instances (see
refinement 1). No statement elsewhere was restated, weakened, or
edited; the frozen bridge module stands exactly as integrated.

## Honesty fence

Finite thermal-time structure only: finite matrices, a packaged finite
Gibbs state, its own modular flow, and now its infinitesimal generator
at time zero. This landing asserts NOTHING about physical time in
general, quasars, the solar clock, cosmology, or Δ. NO CLAIM; dials
0/4. Millennium parts closed: 0.

## INTEGRATION (parent, 2026-11-04)

Integrated from deriv1-lane commit `4955f54` (module + dossier
byte-identical, md5-verified: module `f48032b5…`, dossier `5d1aff0c…`;
lane base `7e2b5f5` = current main-tree HEAD at integration). State
check: main tree tracked files clean; module + dossier new files.
DECLARATION-COLLISION SCAN RUN FIRST (house lesson): all five
declaration names (`modularFlow_exp_arg_pos`, `modularFlow_exp_arg_neg`,
`modularFlow_hasDerivAt_zero`, `GibbsClock.flow_hasDerivAt_zero`,
`GibbsClock.thermal_time_bridge_complete`) and the module name itself
grep to ZERO occurrences in the main tree at HEAD — no collisions.

Main-tree targeted build green (3,587 jobs, matching the lane), zero
sorrys (zero-sorry gate PASS, 503 files), module WARNING-CLEAN (no
build warning names the module). Independent recount: module strict
5 + 0 defs exact; whole-tree 13,917/503 minus frozen remainder 669/15.
FENCE PASS 286/286 (281 → 286): all five headlines admitted with the
`import ThetLogos.ThermalTimeBridgeDeriv` line in
`lean/scripts/axiom-fence.txt` IN THIS SAME COMMIT as the module; every
one of the five on exactly {propext, Classical.choice, Quot.sound},
no sorryAx. Ledger record `thermal-time-bridge-deriv1` (standing, T3,
kill_id null) — validator PASS, 34 records. Census (FILES-TRUE, method
of record) 13,243/487 → 13,248 strict / 488 modules; README prose
census and badge both updated to 13,248 / 488 (kept equal).

VERDICT CARRIED AT FULL RANK: DERIV-1 FULL via Route A; the finite
thermal-time bridge is COMPLETE AT TWELVE CLAUSES — the
`thermal-time-bridge` record's PARTIAL grade closes to FULL by this
module, the DERIV-1 residue discharged in the Frobenius dialect Route
A pre-registered. NO CLAIM; dials 0/4.
