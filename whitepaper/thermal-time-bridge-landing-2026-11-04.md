# UNIVERSAL BRIDGE — FINITE THERMAL-TIME BRIDGE — LANDING DOSSIER — 2026-11-04

## VERDICT: PARTIAL — pinned bridge landed at every clause but one; the derivative clause is the named residue DERIV-1

Fired by Jeff's word 2026-11-04 ("build that universal bridge").
Bounded reading executed exactly: a single finite-level theorem-module
stating that a thermal (Gibbs) state generates its own time — the
modular flow of the state is its clock — assembled and proved from the
corpus's owned parts, in the spirit of U-1 ONE KERNEL (a
dictionary/assembly at exact equality is a legitimate landing; only
what the assembly proves is claimed). NOT in scope, and appearing
nowhere in the module or this dossier except this fence line: quasars,
the solar clock, cosmology — Jeff's T5 color from the firing night's
chat; they are not content. NO CLAIM; dials 0/4.

Module: `lean/ThetLogos/ThermalTimeBridge.lean`
(**strict 17 theorems + 1 def**, zero sorrys, module warning-clean;
targeted lane build green, 3,586 jobs). Lane: worktree
`~/workspace/thet-logos-bridge`, branch `thermal-time-bridge-lane`,
base = main-tree HEAD `8eaf57d` (remote `ac5b416a`; census 13,117/480,
fence 175/175, verified at cut). LANE COMMIT ONLY — NOT integrated,
NOT pushed; the parent runs the integration.

## STEP 1 — Audit (what the corpus already owned, graded)

| Piece | Where | Grade |
|---|---|---|
| Normalized matrix Gibbs state `gibbsState K β = (gibbsZ K β)⁻¹ • gibbsWeight K β`; finite KMS relation `gibbs_kms`; unnormalized-weight stationarity | `KMSBridge` | owned |
| Packaged `GibbsClock` (Hermitian `K`, `beta`, `beta_pos`); state = `gibbsState G.K G.beta`; non-scalar generator `(G.beta:ℂ) • G.K`; flow = `modularFlow G.generator`; group law `GibbsClock.flow_add`; own-β KMS `GibbsClock.kms`; conversion `GibbsClock.conversion` (thermal time s = laboratory flow at β·s); laboratory weight stationarity `GibbsClock.weight_stationary`; scalar-shift invariance `modularFlow_add_smul_one` | `ThermalClock` | owned |
| Matrix modular flow = built Heisenberg evolution `modularFlow_eq_heisenbergFlow`; built unitary `evolutionUnitary` + `evolutionUnitary_isUnitary`; Schrödinger-picture Gibbs stationarity `gibbsState_densityFlow_stationary`; diagonal `K = −ln ρ` form `diagModularK_gibbsWeightsE` (K = β • diagonal E + logZ • 1) | `GibbsSpan` | owned |
| `modularFlux K A = Complex.I • (K * A − A * K)`; `modularFlux_selfAdjoint`; diagonal `diagFlow` group law; `eigenvalue_rigidity` | `ModularTime` | owned — with an explicit gap on its own face: the derivative identity d/ds‖₀ σ_s(D) = φ is NOT machine-checked there |
| `*-automorphism package for the GibbsClock flow (mul/one/add/smul/star as theorems about `G.flow`) | — | **absent** (the pieces existed only for `twistConj` on the `Fin 32` seat in `TwistedTriple`/`FlowKernel`) |
| State stationarity under the clock's OWN flow (owned form was unnormalized-weight stationarity under the LABORATORY flow) | — | **partial** — one conversion step away |
| Thermal-expectation invariance `Tr(ρ σ_s(A)) = Tr(ρ A)` as a stated theorem | — | **absent** |
| Literal `−ln ρ` operator identity for an arbitrary matrix Gibbs state | — | **partial** — diagonal case owned (`GibbsSpan`); matrix case owns only the scalar-shift invariance that makes the scalar part of the generator invisible to the flow. Stated as such; not inflated. |
| Modular-flow derivative identity | — | **absent** — became residue DERIV-1 (see below) |
| `TomitaTakesakiWindow` | — | T5 priced window (`Prop := True`), NOT a theorem; not used |
| `ThermalKMS` abstract `ModularData` group law (fixed 32-seat); `SpectralClock` / measured-clock modules | — | not content: abstract seat law / finite clock readings, not a Gibbs-state modular flow; not used |

## STEP 2 — Pinned statement

For a packaged `GibbsClock G` (state `gibbsState G.K G.beta`, generator
`(G.beta:ℂ) • G.K`, flow `modularFlow G.generator`): the flow is a
one-parameter group of *-automorphisms, fixes `G.state`, preserves the
thermal trace expectation `Tr(ρ A)`, satisfies KMS at the clock's own
β, converts to the laboratory flow at physical time β·s, and is
unchanged by any scalar shift of the generator. The bridge is stated
in the `GibbsClock` dialect or not at all; no continuum
Tomita–Takesaki claim; no claim that physical time in general IS
thermal time.

## STEP 3 — What landed (17 strict + 1 def)

Headline: **`GibbsClock.thermal_time_bridge`** — the 12-clause
conjunction of the pinned statement (group law, identity at 0,
multiplicativity, additivity, scalar homogeneity, one-preservation,
*-law, state stationarity, expectation invariance, KMS at own β,
conversion at rate β, scalar-shift invariance of the clock).

Supporting theorems (all assembly/application of owned theorems,
labeled as such per the U-1 precedent): `GibbsClock.expectation`
(def, `Tr (G.state * A)`), `GibbsClock.generator_isHermitian`,
`GibbsClock.flow_zero`, `GibbsClock.flow_eq_heisenbergFlow`,
`GibbsClock.flow_eq_twistConj`, `GibbsClock.flow_mul`,
`GibbsClock.flow_add_apply`, `GibbsClock.flow_smul`,
`GibbsClock.flow_one`, `GibbsClock.flow_conjTranspose`,
`GibbsClock.flow_neg_flow`, `GibbsClock.flow_flow_neg`,
`GibbsClock.flow_weight_stationary` (owned laboratory stationarity
transported through the owned conversion),
`GibbsClock.flow_state_stationary`,
`GibbsClock.flow_trace` (unitary cyclicity),
`GibbsClock.expectation_flow`,
`GibbsClock.flow_generator_add_smul_one`.

**Axiom sets (measured, `#print axioms` on all 17 theorems):** every
theorem, including the headline, on exactly
{propext, Classical.choice, Quot.sound}. No `sorryAx`, no
`native_decide`.

## The residue — DERIV-1 (why PARTIAL, at exactly one clause)

The pinned bridge also asked for the infinitesimal-generator clause:
d/ds‖₀ `G.flow s A` = `modularFlux G.generator A`. It was attempted
(product rule on the two exponential factors via
`hasDerivAt_exp_smul_const'` + `comp_ofReal`) and it fails for a
corpus-level reason, now proved by `#synth` checks in-lane:

- In the pinned Mathlib (v4.35.0-rc3), `NormedSpace.exp` on matrices
  is the **norm-free topological exponential**: its signature needs
  only `Ring`, `TopologicalSpace`, `IsTopologicalRing`. That is the
  exponential the corpus's `modularFlow` is built from.
- Matrices carry **no canonical `NormedRing`** instance in this pin —
  nor even `SeminormedAddCommGroup` (`#synth` fails with the corpus's
  own import set). Every normed-ring instance in
  `Mathlib/Analysis/Matrix/Normed.lean` is a scoped opt-in (elementwise
  / Frobenius / operator / L2-operator).
- Therefore a `HasDerivAt` statement about the matrix flow cannot
  even be *formed* in the corpus's instance context. Landing it
  requires (a) choosing a matrix norm (the Frobenius scoped instances
  are the natural candidate), and (b) proving the normed exponential
  under that norm agrees with the corpus's topological `modularFlow`.
  Neither step is an assembly step; both are new work.

**DERIV-1, priced as its own brick: S–M, est. strict 4–10.** Two
registered shapes: (i) Frobenius-norm route — scoped instances,
exp-agreement lemma, then the product-rule proof (the proof skeleton
exists from the failed attempt and is sound wherever a `NormedRing`
instance is present); (ii) entrywise/diagonal route — the derivative
stated entry-by-entry for the diagonal `diagFlow` dialect of
`ModularTime`, where the flow is scalar `cpowI` conjugation and no
matrix norm is needed, at the cost of living in the eigenbasis dialect
rather than the `GibbsClock` dialect. Not built here; no new program
was built to fill the clause, per the pre-registration.

## Honesty fence

Finite thermal-time structure only: finite matrices, a packaged
finite Gibbs state, its own modular flow. This landing asserts
NOTHING about physical time in general, quasars, the solar clock,
cosmology, or Δ. NO CLAIM; dials 0/4. Millennium parts closed: 0.

## INTEGRATION — 2026-11-04 — parent integration into the main tree

Integrated from lane commit `f3dbf8e` onto current
main-tree HEAD `5050bb2` (the duct integration; the lane
was cut from `8eaf57d`). Step 1: main tree tracked files
clean (untracked `SweepAll.lean` + old whitepaper drafts
left alone), module + dossier new files, and the
declaration-level collision scan of all 18
`ThermalTimeBridge` names against the main tree found
ZERO collisions. Module + dossier copied BYTE-IDENTICAL
(md5-verified: module `c2f5f7764de2450aa103567fa94c0b3b`,
dossier pre-integration
`d1cb61b0238c3b2e62e7dc8a1d904a2b`). Main-tree targeted
build `lake build ThetLogos.ThermalTimeBridge` green
(3,586 jobs, matching the lane), zero sorrys, module
WARNING-CLEAN (no build warning names
`ThermalTimeBridge.lean`). Recount: module strict 17 +
1 def exact; census FILES-TRUE 13,147/481 →
**13,164 strict / 482 modules** (whole-tree 13,833/497
minus frozen remainder 669/15); README prose + badge
both 13,164/482, kept equal. Fence: the 17 audited
theorems admitted WITH `import ThetLogos.ThermalTimeBridge`
in the same commit as the module — FENCE PASS **207/207**,
every new theorem on exactly
`{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
Ledger record `thermal-time-bridge` (partial, T3),
validator PASS 28 records. Verdict face unchanged:
bridge PARTIAL at exactly the DERIV-1 residue (priced
S–M / strict 4–10), assembly labeled as assembly,
finite matrices only, nothing about physical time,
quasars, cosmology, or Δ. **NO CLAIM; dials 0/4.**
