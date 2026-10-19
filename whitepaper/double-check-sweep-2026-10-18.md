# Double-Check Sweep — 2026-10-18

Ordered by Jeff, 2026-10-18: "un park the fleet and run everything and
double check everything twice." This sweep re-derives, from the
current sources, every number the program publishes, and rebuilds the
whole corpus from a clean tree. Method of record: strict line-initial
count (`^(theorem|lemma) ` on comment-stripped source; stripping is
nesting-aware for Lean block comments and string-aware), the
attribute-inclusive parallel count, a comment-stripped
`sorry`/`admit` census, `#print axioms` spot checks, and a
public-surfaces audit. Pinned toolchain: Mathlib v4.35.0-rc3.

## Verdicts

| Check | Verdict |
|---|---|
| 1 — Full-corpus rebuild (`lake clean` + `lake build`) | **PASS** — 9,106 jobs, exit 0, zero errors |
| 2 — Recount, two methods | **PARTIAL** — strict totals reconcile exactly; the published attribute-inclusive figure does not (Discrepancy D2) |
| 3 — sorry/admit census | **PASS** — exactly the seven labeled sorrys, zero admits |
| 4 — Axiom audit | **PASS** — all nine headlines on the standard three axioms only |
| 5 — Public numbers vs ledger | **PARTIAL** — headline and GitHub description correct; README carries three stale figures (Discrepancies D1–D3) |

## Check 1 — Full-corpus rebuild

**PASS.** `lake clean` was executed first (in this Lake version it
clears the whole workspace build, including the vendored Mathlib
artifacts — so the rebuild below recompiled essentially the full
pinned Mathlib closure as well as the corpus). The build then ran in
two target scopes:

- `lake build` (the root library target): **Build completed
  successfully (3,325 jobs), exit 0.** The root module imports 15
  corpus modules directly; its closure covers 19 corpus modules plus
  the root — it does not by itself reach the other 112 modules.
- `lake build` with all 131 module targets named explicitly:
  **Build completed successfully (9,106 jobs), exit 0.** All 131
  corpus `.olean` files are present afterward, and a whole-log scan
  finds **zero errors**.

Warnings of substance: only the seven `declaration uses 'sorry'`
warnings, at exactly the census sites of Check 3 (declaration lines:
BlockedQuestions.lean 72/106/138/190/271, ModularTime.lean 201,
XYZTripotents.lean 488), plus routine linter notes on a handful of
modules (unused simp args, unused variables, style). The heaviest
modules: EdgeSignature.lean 2,235 s, LatticeTransfer.lean 752 s,
LatticePositivity.lean 651 s, MassGapDossier.lean 440 s.

Execution note, recorded rather than hidden: the environment's tool
service restarted repeatedly during the sweep, killing the in-flight
build process nine times across the two phases. After each restart
the build was resumed; Lake's per-module cache made every resume
incremental, no artifact was restored or placed by hand, and the
final state was produced entirely by `lake build` from the cleaned
tree.

## Check 2 — Recount, two methods

Whole corpus (all 131 files in `lean/ThetLogos/`):

- **Strict: 3,984** — matches the expected anchor exactly.
- **Attribute-inclusive (same-line `@[simp]`-prefixed): 4,024** —
  the corpus carries **40** same-line `@[simp]`-prefixed
  theorem/lemma declarations. (Every same-line attribute prefix on a
  theorem/lemma in the corpus is exactly `@[simp]`; an
  any-attribute regex and a `@[simp]`-only regex return the same 40.
  A further 11 declarations carry an attribute on its own line with
  the declaration following — FermionicLimitOps 1, LatticeGauge 3,
  LatticeReflection 2, MassShellMeasure 1, PoincareAction 2,
  Renormalization 1, Scaffold32 1 — which no published house figure
  counts.)

Program total (the counted chain of the papers' §0 decompositions):

- **Strict: 3,315** — matches the expected anchor exactly
  (3,276 at the Paper v4 freeze + DiffusionDefect 12 +
  SpectralClock 14 + ThermalKernel 13).
- **Attribute-inclusive: 3,355 by uniform recount** — the published
  parallel figure is 3,330; see Discrepancy D2. All 40 `@[simp]`
  declarations sit in program modules (the remainder files carry
  none), so the program's attribute-inclusive count is
  3,315 + 40 = 3,355 under the same rule that gives 4,024 for the
  whole tree.

### The non-chain remainder (whole corpus minus program = 669 strict)

The papers define the program total by decomposed increments
(Papers v1–v4, §0); the complement is the pre-ladder / non-chain
remainder. By that arithmetic the chain comprises **116 files** and
the remainder **15 files**, summing to exactly 669 strict:

Documented core (Paper v1, §0: "earlier exploratory campaigns — the
CF-kernel arc, exotic sectors, chromatic and related work"; Paper v3,
§0: TritGrading "carries no separate increment in this chain";
FockCoImport appears in no decomposition):

| File | Strict |
|---|---|
| CFKernelRetarget.lean | 474 |
| CFKernel22.lean | 75 |
| ExoticSectors.lean | 78 |
| CFKernelBase.lean | 6 |
| CFKernel.lean | 5 |
| CFKernel22Dim.lean | 0 |
| Chromatic.lean | 1 |
| TritGrading.lean | 27 |
| FockCoImport.lean | 0 |
| **Core subtotal** | **666** |

One forced consequence of the arithmetic: `CFKernelClassification.lean`
(4) cannot belong to the remainder — with it, the documented core
alone overshoots 669. It is counted in the program (consistent with
its being the W22 classification file behind the Digital Standard
Model paper).

The remaining 3 declarations sit in a six-file tail whose membership
is **ambiguous** — the decompositions do not decide it, and this
sweep does not guess. Every solution consistent with the totals
contains the four zero-theorem files `Axioms.lean`,
`HaagKastler.lean`, `OsterwalderSchrader.lean`, `WightmanTargets.lean`
(all 0), plus exactly one of {`ThermalKMS.lean` (1),
`WightmanAxioms.lean` (1)} and exactly one of {`CausalProduct.lean`
(2), `OrderOne.lean` (2)} — four combinations, each summing to 3.
Two documentary hints pull against each other (Paper v1 §0 discusses
`CausalProduct`'s file-level axioms among the program's spot-checked
results, suggesting it is program; the same paper classes the intake
files as program, suggesting `WightmanAxioms.lean` is program) and no
combination satisfies both, so the tail is recorded as ambiguous.
The ambiguity moves no total: all four combinations sum identically,
and the program and whole-corpus figures above are the same under
every solution.

### Per-module counts (strict / attribute-inclusive)

| Module | Strict | Incl. | Module | Strict | Incl. |
|---|---:|---:|---|---:|---:|
| ActiveFlux.lean | 5 | 5 | LatticeTransfer.lean | 58 | 58 |
| AnalyticTriple.lean | 17 | 17 | LorentzContinuity.lean | 28 | 28 |
| Axioms.lean | 0 | 0 | MartinettiRep.lean | 159 | 159 |
| BRSTFinite.lean | 24 | 24 | MassGapDossier.lean | 1 | 1 |
| BlockedQuestions.lean | 7 | 7 | MassShellBoost.lean | 80 | 86 |
| BosonicAssembly.lean | 31 | 31 | MassShellMeasure.lean | 57 | 63 |
| BosonicESA.lean | 17 | 17 | Mod9Triad.lean | 10 | 10 |
| BosonicESABeta.lean | 16 | 16 | ModularFlux.lean | 13 | 13 |
| BosonicFock.lean | 25 | 25 | ModularTime.lean | 12 | 12 |
| BosonicGamma.lean | 6 | 6 | N0Uniqueness.lean | 5 | 5 |
| BosonicGammaFunctor.lean | 42 | 42 | OSRepin.lean | 15 | 15 |
| BosonicInteraction.lean | 69 | 69 | OneModeFermion.lean | 37 | 37 |
| BosonicLimit.lean | 27 | 29 | OperatorWick.lean | 70 | 70 |
| BosonicLimitOps.lean | 48 | 48 | OrderOne.lean | 2 | 2 |
| BosonicSecondQuant.lean | 25 | 25 | OrderOneFull.lean | 14 | 14 |
| BoundedTriple.lean | 6 | 6 | OsterwalderSchrader.lean | 0 | 0 |
| BridgeCompletion.lean | 60 | 60 | PoincareAction.lean | 11 | 20 |
| BridgeLaplacian.lean | 29 | 29 | PreCompensation.lean | 28 | 28 |
| CCMAlgebraClassification.lean | 7 | 7 | ProductTriple.lean | 63 | 63 |
| CFKernel.lean | 5 | 5 | RationalPivot.lean | 4 | 4 |
| CFKernel22.lean | 75 | 75 | Renormalization.lean | 60 | 61 |
| CFKernel22Dim.lean | 0 | 0 | ResonanceSpectrum.lean | 15 | 15 |
| CFKernelBase.lean | 6 | 6 | Rung5W1.lean | 2 | 2 |
| CFKernelClassification.lean | 4 | 4 | Rung5W2.lean | 13 | 13 |
| CFKernelRetarget.lean | 474 | 474 | Rung5W3.lean | 1 | 1 |
| CausalProduct.lean | 2 | 2 | Rung5W4.lean | 2 | 2 |
| Chromatic.lean | 1 | 1 | Rung5W5.lean | 12 | 12 |
| ClassicalYangMills.lean | 16 | 16 | Rung5W6.lean | 7 | 7 |
| ClayStatement.lean | 7 | 7 | SMFermions.lean | 23 | 23 |
| ConcreteBoundedTriple.lean | 4 | 4 | SMGaugeAlgebra.lean | 11 | 11 |
| ConcreteFiniteModel.lean | 42 | 42 | SMHiggsBreaking.lean | 42 | 42 |
| ConcreteHilbertRep.lean | 10 | 10 | SMLagrangian.lean | 19 | 19 |
| ConcreteStar.lean | 8 | 8 | Scaffold32.lean | 8 | 11 |
| DecoherenceToy.lean | 37 | 37 | SchrodingerDynamics.lean | 49 | 49 |
| DiffusionDefect.lean | 12 | 12 | SchrodingerSmalls.lean | 24 | 24 |
| DixmierTrace.lean | 24 | 24 | SchwartzComplete.lean | 2 | 2 |
| EdgeSignature.lean | 21 | 21 | SchwartzSpace.lean | 14 | 14 |
| ExoticSectors.lean | 78 | 78 | SecondQuantDGamma.lean | 18 | 18 |
| FactorOrderOne.lean | 4 | 4 | SecondQuantGamma.lean | 32 | 33 |
| FermionicFock.lean | 43 | 49 | SexagesimalClock.lean | 31 | 31 |
| FermionicInteraction.lean | 58 | 58 | SpectralAction.lean | 2 | 2 |
| FermionicLimit.lean | 24 | 26 | SpectralActionBridge.lean | 12 | 12 |
| FermionicLimitOps.lean | 32 | 32 | SpectralActionFinite.lean | 55 | 55 |
| FieldOperators.lean | 14 | 14 | SpectralClock.lean | 14 | 14 |
| FiniteSpectralTriple.lean | 14 | 14 | SpectralFrontier.lean | 16 | 16 |
| FlowKernel.lean | 8 | 8 | StoneFiniteDim.lean | 4 | 4 |
| FluxTwist.lean | 38 | 38 | StoneFiniteDim2.lean | 3 | 3 |
| FockCoImport.lean | 0 | 0 | TRO.lean | 6 | 6 |
| FockLimit.lean | 6 | 6 | ThermalClock.lean | 33 | 33 |
| FockLorentzBos.lean | 7 | 7 | ThermalKMS.lean | 1 | 1 |
| FockLorentzFerm.lean | 7 | 7 | ThermalKernel.lean | 13 | 13 |
| FockPackaging.lean | 38 | 38 | ThreeGen.lean | 20 | 20 |
| FockPackagingBos.lean | 99 | 99 | TranslationContinuity.lean | 10 | 10 |
| FockPackagingFerm.lean | 78 | 78 | TriadicPin.lean | 0 | 0 |
| FreeField.lean | 14 | 14 | TriadicScreening.lean | 19 | 19 |
| HaagKastler.lean | 0 | 0 | TritGrading.lean | 27 | 27 |
| HaagKastlerFree.lean | 14 | 14 | TwistedTriple.lean | 93 | 93 |
| InnerFluctuations.lean | 39 | 39 | UltimateReduction.lean | 6 | 6 |
| KMSBridge.lean | 10 | 10 | WeldDuality.lean | 73 | 73 |
| LatticeAnalyticity.lean | 87 | 87 | WickSigns.lean | 31 | 31 |
| LatticeBlocking.lean | 60 | 60 | WightmanAxioms.lean | 1 | 1 |
| LatticeCorrelations.lean | 68 | 68 | WightmanRepin.lean | 14 | 14 |
| LatticeGauge.lean | 68 | 72 | WightmanTargets.lean | 0 | 0 |
| LatticeOSSpace.lean | 42 | 42 | XYZTripotents.lean | 90 | 90 |
| LatticePositivity.lean | 44 | 44 | YukawaInteraction.lean | 119 | 119 |
| LatticeReflection.lean | 67 | 67 | | | |
| **Whole corpus (131 files)** | **3984** | **4024** | | | |

## Check 3 — sorry/admit census

Comment-stripped sweep of all 131 files for `\b(sorry|admit)\b`:

| File | Line | Token |
|---|---|---|
| BlockedQuestions.lean | 76 | sorry |
| BlockedQuestions.lean | 108 | sorry |
| BlockedQuestions.lean | 140 | sorry |
| BlockedQuestions.lean | 194 | sorry |
| BlockedQuestions.lean | 274 | sorry |
| ModularTime.lean | 206 | sorry |
| XYZTripotents.lean | 492 | sorry |

**Exactly 7 sorrys, 0 admits** — identical to the ledger: five T5 in
`BlockedQuestions.lean` (open conjectures Q1–Q5), one T3 in
`ModularTime.lean` (`kms_identity_diagonal`), one T5 in
`XYZTripotents.lean` (Open Problem 2). No new hit, no missing hit.
The Check 1 rebuild independently corroborates: the compiler's
`declaration uses 'sorry'` warnings fire at exactly these seven
declarations and nowhere else. **PASS.**

## Check 4 — Axiom audit

**PASS.** A scratch file (created inside `lean/` for the run and
deleted afterward) importing ThermalKernel, SpectralClock,
DiffusionDefect, ResonanceSpectrum, ThermalClock, LatticeTransfer,
SpectralActionFinite, and ModularFlux printed, verbatim:

| Theorem | Axioms |
|---|---|
| `ThetLogos.thermalClock_heatKernel_one` | propext, Classical.choice, Quot.sound |
| `ThetLogos.phaseFlow_masterTick_first` | propext, Classical.choice, Quot.sound |
| `ThetLogos.sum_normSq_add_disp` | propext, Classical.choice, Quot.sound |
| `ThetLogos.phaseFlow_stationary_iff` | propext, Classical.choice, Quot.sound |
| `ThetLogos.gibbs_conversion` | propext, Classical.choice, Quot.sound |
| `ThetLogos.gibbs_conversion_full_generator` | propext, Classical.choice, Quot.sound |
| `ThetLogos.transferOp_isSelfAdjoint` | propext, Classical.choice, Quot.sound |
| `ThetLogos.finite_heat_trace_even` | propext, Classical.choice, Quot.sound |
| `ThetLogos.modularFlux_selfAdjoint` | propext, Classical.choice, Quot.sound |

Every audited headline depends on exactly the standard three —
no extra axiom anywhere. The rebuild log corroborates for two more:
the in-source `#print axioms` in BoundedTriple.lean
(`prod_commutator_factorBounds`) and FermionicFock.lean
(`vacuum_cyclic`) printed the same three during compilation.

## Check 5 — Public numbers vs ledger

- **README headline text:** "3,315 verified theorem declarations
  across 96 counted Lean modules" and the footnote's
  attribute-inclusive 3,330. Headline 3,315 matches the recount.
  The 3,330 and the 96 do not — see D2 and D3.
- **README badge:** the shields.io badge at the top of README.md
  reads **3,302** — stale by one landing (ThermalKernel). See D1.
- **GitHub repo description** (fetched live via the API during this
  sweep): "Machine-verified foundations for quantum field theory in
  Lean 4 (ACMD) — 3,315 kernel-checked theorem declarations. Every
  claim tiered; kills published next to the proofs." — **3,315 ✓.**
- **Paper v4 draft:** still carries its frozen §0 counts (3,276
  program / 3,945 whole-tree). Recorded, not fixed: the refresh is
  scheduled for the v4 ship step, per the ship sequence Jeff approved
  (refresh once, after the fleet run). Known-stale by design.

## Discrepancies

- **D1 — README badge stale.** The badge image URL encodes 3,302;
  the README's own headline text and the recount both say 3,315.
  The badge was not refreshed at the ThermalKernel landing.
- **D2 — Attribute-inclusive figure understated by 25.** README and
  the papers state that fifteen declarations carry a same-line
  `@[simp]` prefix, giving the parallel figure 3,330. A uniform
  recount finds **40** such declarations, all in program modules:
  the fifteen named in Paper v3 (BosonicLimit 2, FermionicLimit 2,
  LatticeGauge 4, MassShellBoost 6, SecondQuantGamma 1) plus 25
  more in v1-era ladder modules that the v3 recount note did not
  list — FermionicFock 6, PoincareAction 9, MassShellMeasure 6,
  Renormalization 1, Scaffold32 3. Under the house rule the
  program's attribute-inclusive count is therefore **3,355**, not
  3,330. The strict headline (the public number of record) is
  unaffected: 3,315 stands exactly.
- **D3 — README module count unreconciled.** README says "96 counted
  Lean modules." The papers' own §0 decompositions enumerate the
  chain file by file (64 at the v1 freeze + 9 + 16 + 24 + 3
  post-freeze bricks) = **116 files**, and the strict program total
  of 3,315 reconciles only against that chain (complement: the
  15-file, 669-declaration remainder above). The 96 figure matches
  neither the decomposition count nor any subset this sweep could
  derive; it appears to be a carried-forward landing figure. The
  declaration totals are unaffected.
- **D4 — Paper v4 whole-tree attribute figure unreconciled.** Paper
  v4's §0 recount note states the whole tree holds "54 declarations
  carrying a same-line `@[simp]`" (3,945 strict + 54 = 3,999
  attribute-inclusive). This sweep's variants find 40 (same-line
  `@[simp]` before theorem/lemma — also 40 before any declaration
  kind), 50 (every line opening with `@[`), and 51 (40 + the 11
  own-line-attribute cases). No variant reproduces 54. The strict
  side of the same note reconciles exactly (3,945 + the 39 post-v4
  declarations = 3,984), so the 54 appears to be a methods slip in
  the v4 addendum; the figure is in any case superseded when v4's
  counts refresh at ship.
- **Ambiguity note (not a numeric discrepancy):** the six-file tail
  of the non-chain remainder (§Check 2) is not decided by any
  published decomposition; the four candidate memberships are
  enumerated there rather than guessed. No published total depends
  on the choice.
