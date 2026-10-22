# Corpus Axiom-Dependency Audit — thet-logos counted corpus

**Date:** 2026-10-21 (run window 03:45–07:45 EDT, filesystem clock)
**Order:** Jeff, 2026-10-21 ~23:34 EDT ("run it")
**Repo:** `~/workspace/thet-logos/lean`, toolchain `leanprover/lean4:v4.35.0-rc3` (pinned Mathlib)
**Scope:** every theorem/lemma declaration in the 122 counted modules (README totals 3,408 strict / 3,448 attribute-inclusive). All 137 non-excluded source files were in fact audited (4,117 declarations), so the counted figures below are exact subsets, not samples. `DiracTorsionMap.lean` was excluded by design (in-flight compile by another agent; also not a counted module). No repo file was edited; all runs were read-only `lake env lean` elaborations of scratch files under `~/workspace/axa-scratch`.

## Headline verdict

**NO SURPRISES. The sorryAx footprint of the counted corpus is exactly the 7 known sorry declarations — no transitive contamination anywhere.**

- Bucket (b), sorryAx-dependent, counted set: **exactly 7** — `blockedQ1_physicalClock`, `blockedQ2_continuumLimit`, `blockedQ3_threeGenerations`, `blockedQ4_closedFormGap`, `blockedQ5_physicalDevice` (BlockedQuestions), `kms_identity_diagonal` (ModularTime), `xyz_tripotents_exist` (XYZTripotents). This independently reproduces, by direct per-declaration axiom inspection, the 2026-10-18/19 sweep's rebuild-warning census.
- Stronger: across **all 137 audited files (4,117 declarations, counted + remainder)**, the sorryAx-dependent set is still exactly those 7. Nothing else in the tree — including the 474 declarations of CFKernelRetarget and every downstream importer of the three sorry-carrying files — depends on `sorryAx`.
- Bucket (c), non-standard-axiom-dependent, counted set: **11 declarations** (or 9 — see the membership hinge in §3), all previously known by name in the ledger: the two CFKernelClassification headline theorems, `ccm_classification`, `majorana_Eblock_rigidity`, all five N0Uniqueness theorems, and (hinge-dependent) CausalProduct's two product theorems.
- **Honest proved-only figure: 3,390–3,392 of 3,408 strict counted declarations (3,430–3,432 of 3,448 attribute-inclusive) have a complete axiom footprint inside the standard three** `{propext, Classical.choice, Quot.sound}`. Definition and limits in §5.

## 1. Method

1. **Extraction (house counting rule).** For each `.lean` file, strip comments with a nesting-aware, string-aware stripper, then take line-initial `^(theorem|lemma) ` declarations as the *strict* set and same-line `@[simp]`-prefixed ones as the *attribute-inclusive* increment. Result: 4,095 strict / 4,135 inclusive over 138 files — reconciling exactly with the ledger: sweep total 3,984 strict, plus the six post-sweep bricks (TwoDirections 8, WindingRing 14, FibonacciReturn 13, NoCloning 18, HermitianReduction 16, ThermalPreCompensation 24 = 93) plus DiracTorsionMap (18) = 4,095; the same-line `@[simp]` count is exactly 40, matching the sweep's corrected figure.
2. **Axiom collection (meta route).** Per group of modules: a scratch file imports exactly the group's module closure, then for each declaration name resolves candidate fully-qualified names (root + module + in-file namespaces), verifies attribution by requiring the candidate's defining module (`getModuleIdxFor?`) to lie in the group's import closure, and prints the complete transitive axiom set from `Lean.collectAxioms`. 19 group runs, serial, `nice -n 10`, memory-gated; exit codes captured directly to files (never through a pipe).
3. **Collision handling.** The extraction found **20 cross-module declaration-name collisions** (same name, different modules) — more than the 2 pairs previously documented (e.g. `Config` in BosonicFock/LatticeGauge; `vacuum_cyclic` in FermionicFock/FreeField; `pauliX/pauliZ` in ConcreteFiniteModel/NoCloning). Groups were therefore built from whole import closures and the attribution check is closure-based: a same-named declaration from another module *inside the same closure* is attribution-consistent. An earlier whole-environment run that assumed unique names misattributed `FiniteLieData.toList` and was discarded; the closure design replaced it.
4. **Resolution audit.** 4,128 AXRES result lines for 4,117 declarations (11 extra lines were false-candidate hits, each rejected by the attribution check; every declaration has exactly one attribution-verified hit). **Coverage mismatches: none. Unresolved declarations: only DiracTorsionMap's 18, by design.**

### Calibration (required spot checks — both passed, two independent routes)

| Declaration | Expected | `#print axioms` (text route) | Meta route (this audit) |
|---|---|---|---|
| `ThetLogos.modularFlux_selfAdjoint` (ModularFlux, known clean) | standard three only | `[propext, Classical.choice, Quot.sound]` | `[propext, Classical.choice, Quot.sound]` ✓ |
| `ThetLogos.kms_identity_diagonal` (ModularTime, known dirty) | contains `sorryAx` | `[propext, sorryAx, Classical.choice, Quot.sound]` | `[propext, sorryAx, Classical.choice, Quot.sound]` ✓ |

The two routes agree exactly on both anchors. The pipeline was then run unchanged over the full corpus.

### Counted-set membership

Reconstructing the 122 from the papers' §0 decompositions + landing dossiers: **120 files are certainly counted** (3,405 strict / 3,445 inclusive). The residual arithmetic is exact: the counted total needs +3 strict/+3 inclusive from the ambiguous tail, and the only combination achieving it is **exactly one of {ThermalKMS (1 decl), WightmanAxioms (1 decl)} and exactly one of {CausalProduct (2 decls), OrderOne (2 decls)}** — 3,408/3,448 over 122 files under all four combinations. All results below are stated under all four; the findings are membership-invariant except where the CausalProduct/OrderOne hinge is named.

## 2. Bucket counts over the counted declarations

Standard three = `{propext, Classical.choice, Quot.sound}`; "std-only" = complete footprint ⊆ standard three (31 declarations corpus-wide depend on no axioms at all; they are inside std-only).

| Counted set (strict, 3,408) | (a) std-only | (b) sorryAx | (c) other non-std |
|---|---:|---:|---:|
| ThermalKMS + CausalProduct | 3,390 | 7 | 11 |
| ThermalKMS + OrderOne | 3,392 | 7 | 9 |
| WightmanAxioms + CausalProduct | 3,390 | 7 | 11 |
| WightmanAxioms + OrderOne | 3,392 | 7 | 9 |

| Counted set (inclusive, 3,448) | (a) std-only | (b) sorryAx | (c) other non-std |
|---|---:|---:|---:|
| … + CausalProduct | 3,430 | 7 | 11 |
| … + OrderOne | 3,432 | 7 | 9 |

The ThermalKMS/WightmanAxioms choice never moves any number (both single declarations — `spectralGap_pos`, `minkowskiInner_nonneg_of_mem` — are std-only). The CausalProduct/OrderOne hinge moves exactly CausalProduct's 2 non-std declarations. Documentary evidence (Paper v1 §0 discusses CausalProduct as program content) favors the CausalProduct-counted reading, i.e. **3,390 / 3,430**; the audit reports the range because the published decompositions do not pin it.

Whole audited tree (137 files, for reference): strict 4,077 = 4,059 std-only + 7 sorryAx + 11 non-std; inclusive 4,117 = 4,099 + 7 + 11. The 15-file remainder contributes **zero** sorryAx and **zero** non-std declarations.

## 3. Bucket (b) — sorryAx-dependent declarations (complete list, counted set)

All seven carry the identical footprint `[propext, sorryAx, Classical.choice, Quot.sound]`, and each is one of the seven lexical-`sorry` declarations themselves — i.e. **no declaration depends on a sorry other than by containing one**:

1. `ThetLogos.blockedQ1_physicalClock` (BlockedQuestions)
2. `ThetLogos.blockedQ2_continuumLimit` (BlockedQuestions)
3. `ThetLogos.blockedQ3_threeGenerations` (BlockedQuestions)
4. `ThetLogos.blockedQ4_closedFormGap` (BlockedQuestions)
5. `ThetLogos.blockedQ5_physicalDevice` (BlockedQuestions)
6. `ThetLogos.kms_identity_diagonal` (ModularTime)
7. `ThetLogos.xyz_tripotents_exist` (XYZTripotents)

## 4. Bucket (c) — non-standard-axiom-dependent declarations (complete list, grouped by axiom)

11 declarations in 5 modules use the corpus's own file-level axioms (T2 pattern: opaque data + named properties, taken as hypotheses of the classification theorems). Grouped by axiom, with dependent-declaration counts in the counted-maximal set:

- **`ThetLogos.exotic_decomposition`** (CFKernelClassification) — 4 decls; **`ThetLogos.exoticBasisAux`** (CFKernelClassification) — 4 decls. Dependents: `cf_kernel_classification_46_10`, `cf_kernel_classification_full` (CFKernelClassification); `ccm_classification` (CCMAlgebraClassification, also via `AdmitsClassifyingDirac_unpack`); `majorana_Eblock_rigidity` (InnerFluctuations).
- **`ThetLogos.n0NullDim`** (N0Uniqueness) — 5 decls; **`SMAlg`, `SMAlg_ring`, `sm_nullDim_eq_10`, `sm_four_sectors`** — 2 decls each (`sm_admissible`, `n0_uniqueness_three_candidates`); **`cand1_nullDim_eq_18`, `cand2_nullDim_eq_6`** — 2 decls each (`cand*_not_admissible`, `n0_uniqueness_three_candidates`). All five N0Uniqueness theorems are axiom-dependent; the file's theorem content is eliminative logic over its own axiom-supplied candidate data, exactly as its T2 design states.
- **CausalProduct product axioms** (hinge: counted only in the CausalProduct-in combinations) — `trace_collapse_hypothesis_fails` depends on 12 (`Cprod, Dprod, Hprod, ProdOp, prodForm, prodOpRing, prodSmul, prodSmul_comp, prodSmul_one, prodSmul_zero_op, prodStar, prod_nonzero_causal_commutator`); `product_not_forced_central` on 9 of them. The file's two theorems are non-implication witnesses over its own axiomatized product data — again the stated T2 design.
- **`ThetLogos.AdmitsClassifyingDirac_unpack`** (CCMAlgebraClassification) — 1 decl (`ccm_classification`).

## 5. The honest proved-only figure

**Definition.** A counted declaration is *proved-only* iff its complete transitive axiom footprint (as computed by the Lean kernel environment, `Lean.collectAxioms`) is a subset of `{propext, Classical.choice, Quot.sound}` — Lean's standard logical axioms, the same basis Mathlib itself rests on.

**Figure: 3,390 of 3,408 strict counted declarations (99.47%), or 3,392 if OrderOne rather than CausalProduct is the 122nd-file hinge; 3,430 / 3,432 of 3,448 attribute-inclusive.** The remaining 18 (or 16) are exactly: 7 sorry-dependent (§3) + 11 (or 9) corpus-axiom-dependent (§4).

**What this does NOT mean.**
- It does not mean the 3,390 statements say what their names suggest. An axiom audit verifies the *proof* side; statement adequacy (the definition-gap failure mode — a theorem can be honestly proved and still be about a weaker statement than its headline) is a separate audit and is not certified here.
- It does not cover declarations outside the house census: `def`s, instances, and structures are not counted declarations and were not audited as targets (they enter only as dependencies). One material instance: `pauliBounded` (ConcreteBoundedTriple) is an *instance*, not a theorem — it does use the file's T2 axiom (see §6), but no counted declaration does.
- It does not assert the standard three are "no axioms" — they are Lean's standard logical basis (choice, propositional extensionality, quotient soundness), accepted throughout Mathlib practice.
- DiracTorsionMap (18 declarations, in-flight, uncompiled at audit time) is neither counted nor audited; nothing here speaks to it.

## 6. Notable negatives (axioms depended on by nothing)

- **`pauli_compactResolvent`** (ConcreteBoundedTriple's T2 axiom): **no theorem/lemma in the entire tree depends on it.** The only dependent is the instance `pauliBounded` (in-source: `hcompactRes := pauli_compactResolvent`), which is not a counted declaration. The module's four counted theorems (`pauliD_resolvent`, `pauliD_resolvent_compact`, `pauliD_sub_det`, `pauliD_sub_smul_matrix`) are all std-only. (The 2026-10-15 spot-check table's "pauliBounded depends on pauli_compactResolvent" was a statement about the instance; at the declaration level the axiom is load-bearing for zero theorems.)
- **SpectralAction placeholder axioms** (`scalarCurv`, `lichnerowicz`, `heatKernelExpansion`, `seely_dewitt_a0`, `seely_dewitt_a4`, `spectral_action_expansion`): depended on by **nothing** — both of the module's counted declarations are std-only.
- **SpectralFrontier operator axioms** (`UnboundedOp.adjoint/isClosed/cayley`, `ProjValuedMeasure`, `isSpectralMeasureOf`, `borelFC`): depended on by **nothing** — all 16 of the module's declarations are std-only.
- **Axioms.lean remainder axioms** (`Void`, `thetPair_exists`, `N0`, `N0_tripotent`): depended on by **nothing** in the tree, including the counted importers TRO, TriadicPin, TriadicScreening, XYZTripotents.
- CausalProduct's `M` and `GloballyHyperbolicM`, N0Uniqueness's full axiom list beyond those in §4: likewise unused by any declaration.

## 7. Coverage, wall-clock, incidents

- **Coverage: 4,117 / 4,117 auditable declarations resolved (100%)** — counted strict 3,408/3,408 and inclusive 3,448/3,448 under every membership combination; remainder 669/669. No module failed to load. The only unresolved items are DiracTorsionMap's 18 extracted names, excluded by the task's hard constraints.
- **Wall-clock:** ≈ 2 h 52 min of Lean process time across the 19 completed group runs, ≈ 4 h calendar including calibration, three incident retries, and heavy co-tenancy (the DiracTorsionMap compile and another agent's job shared the machine throughout; no `lake build` was run, no `.olean` touched).
- **Incidents, for the record:** (i) a first whole-environment prototype misattributed same-named declarations (see §1.3) and was discarded before any results were taken from it; (ii) an early group run failed on the `Config` name collision, motivating the closure design; (iii) a service restart killed one group run mid-flight — rerun clean, no data lost (results are per-group files); (iv) one group (AxG18) recorded exit code 1 from a trailing empty command block *after* all 28 of its results were emitted — cosmetic, data verified complete; (v) EdgeSignature (full-`Mathlib` import) needed 2,413 s alone — the single most expensive module, as expected.
- **Raw results:** per-declaration CSV (4,117 rows: module, name, kind, fully-qualified name, bucket, complete axiom list) at `~/workspace/your_files/corpus-dependency-audit-2026-10-21-results.csv`. Scratch, group files, and logs retained at `~/workspace/axa-scratch/`.

## Appendix — per-module results

Set key: `counted` = certainly in the 122; `ambig-1` = exactly one of the pair is counted (either way, numbers unchanged); `ambig-2` = exactly one of the pair is counted (the §2 hinge); `remainder` = audited, not counted. DiracTorsionMap omitted (excluded by design).
| Module | Set | Checked | Std-only | sorryAx | Non-std |
|---|---|---:|---:|---:|---:|
| ActiveFlux | counted | 5 | 5 | 0 | 0 |
| AnalyticTriple | counted | 17 | 17 | 0 | 0 |
| Axioms | remainder | 0 | 0 | 0 | 0 |
| BRSTFinite | counted | 24 | 24 | 0 | 0 |
| BlockedQuestions | counted | 7 | 2 | 5 | 0 |
| BosonicAssembly | counted | 31 | 31 | 0 | 0 |
| BosonicESA | counted | 17 | 17 | 0 | 0 |
| BosonicESABeta | counted | 16 | 16 | 0 | 0 |
| BosonicFock | counted | 25 | 25 | 0 | 0 |
| BosonicGamma | counted | 6 | 6 | 0 | 0 |
| BosonicGammaFunctor | counted | 42 | 42 | 0 | 0 |
| BosonicInteraction | counted | 69 | 69 | 0 | 0 |
| BosonicLimit | counted | 29 | 29 | 0 | 0 |
| BosonicLimitOps | counted | 48 | 48 | 0 | 0 |
| BosonicSecondQuant | counted | 25 | 25 | 0 | 0 |
| BoundedTriple | counted | 6 | 6 | 0 | 0 |
| BridgeCompletion | counted | 60 | 60 | 0 | 0 |
| BridgeLaplacian | counted | 29 | 29 | 0 | 0 |
| CCMAlgebraClassification | counted | 7 | 6 | 0 | 1 |
| CFKernel | remainder | 5 | 5 | 0 | 0 |
| CFKernel22 | remainder | 75 | 75 | 0 | 0 |
| CFKernel22Dim | remainder | 0 | 0 | 0 | 0 |
| CFKernelBase | remainder | 6 | 6 | 0 | 0 |
| CFKernelClassification | counted | 4 | 2 | 0 | 2 |
| CFKernelRetarget | remainder | 474 | 474 | 0 | 0 |
| CausalProduct | ambig-2 | 2 | 0 | 0 | 2 |
| Chromatic | remainder | 1 | 1 | 0 | 0 |
| ClassicalYangMills | counted | 16 | 16 | 0 | 0 |
| ClayStatement | counted | 7 | 7 | 0 | 0 |
| ConcreteBoundedTriple | counted | 4 | 4 | 0 | 0 |
| ConcreteFiniteModel | counted | 42 | 42 | 0 | 0 |
| ConcreteHilbertRep | counted | 10 | 10 | 0 | 0 |
| ConcreteStar | counted | 8 | 8 | 0 | 0 |
| DecoherenceToy | counted | 37 | 37 | 0 | 0 |
| DiffusionDefect | counted | 12 | 12 | 0 | 0 |
| DixmierTrace | counted | 24 | 24 | 0 | 0 |
| EdgeSignature | counted | 21 | 21 | 0 | 0 |
| ExoticSectors | remainder | 78 | 78 | 0 | 0 |
| FactorOrderOne | counted | 4 | 4 | 0 | 0 |
| FermionicFock | counted | 49 | 49 | 0 | 0 |
| FermionicInteraction | counted | 58 | 58 | 0 | 0 |
| FermionicLimit | counted | 26 | 26 | 0 | 0 |
| FermionicLimitOps | counted | 32 | 32 | 0 | 0 |
| FibonacciReturn | counted | 13 | 13 | 0 | 0 |
| FieldOperators | counted | 14 | 14 | 0 | 0 |
| FiniteSpectralTriple | counted | 14 | 14 | 0 | 0 |
| FlowKernel | counted | 8 | 8 | 0 | 0 |
| FluxTwist | counted | 38 | 38 | 0 | 0 |
| FockCoImport | remainder | 0 | 0 | 0 | 0 |
| FockLimit | counted | 6 | 6 | 0 | 0 |
| FockLorentzBos | counted | 7 | 7 | 0 | 0 |
| FockLorentzFerm | counted | 7 | 7 | 0 | 0 |
| FockPackaging | counted | 38 | 38 | 0 | 0 |
| FockPackagingBos | counted | 99 | 99 | 0 | 0 |
| FockPackagingFerm | counted | 78 | 78 | 0 | 0 |
| FreeField | counted | 14 | 14 | 0 | 0 |
| HaagKastler | remainder | 0 | 0 | 0 | 0 |
| HaagKastlerFree | counted | 14 | 14 | 0 | 0 |
| HermitianReduction | counted | 16 | 16 | 0 | 0 |
| InnerFluctuations | counted | 39 | 38 | 0 | 1 |
| KMSBridge | counted | 10 | 10 | 0 | 0 |
| LatticeAnalyticity | counted | 87 | 87 | 0 | 0 |
| LatticeBlocking | counted | 60 | 60 | 0 | 0 |
| LatticeCorrelations | counted | 68 | 68 | 0 | 0 |
| LatticeGauge | counted | 72 | 72 | 0 | 0 |
| LatticeOSSpace | counted | 42 | 42 | 0 | 0 |
| LatticePositivity | counted | 44 | 44 | 0 | 0 |
| LatticeReflection | counted | 67 | 67 | 0 | 0 |
| LatticeTransfer | counted | 58 | 58 | 0 | 0 |
| LorentzContinuity | counted | 28 | 28 | 0 | 0 |
| MartinettiRep | counted | 159 | 159 | 0 | 0 |
| MassGapDossier | counted | 1 | 1 | 0 | 0 |
| MassShellBoost | counted | 86 | 86 | 0 | 0 |
| MassShellMeasure | counted | 63 | 63 | 0 | 0 |
| Mod9Triad | counted | 10 | 10 | 0 | 0 |
| ModularFlux | counted | 13 | 13 | 0 | 0 |
| ModularTime | counted | 12 | 11 | 1 | 0 |
| N0Uniqueness | counted | 5 | 0 | 0 | 5 |
| NoCloning | counted | 18 | 18 | 0 | 0 |
| OSRepin | counted | 15 | 15 | 0 | 0 |
| OneModeFermion | counted | 37 | 37 | 0 | 0 |
| OperatorWick | counted | 70 | 70 | 0 | 0 |
| OrderOne | ambig-2 | 2 | 2 | 0 | 0 |
| OrderOneFull | counted | 14 | 14 | 0 | 0 |
| OsterwalderSchrader | remainder | 0 | 0 | 0 | 0 |
| PoincareAction | counted | 20 | 20 | 0 | 0 |
| PreCompensation | counted | 28 | 28 | 0 | 0 |
| ProductTriple | counted | 63 | 63 | 0 | 0 |
| RationalPivot | counted | 4 | 4 | 0 | 0 |
| Renormalization | counted | 61 | 61 | 0 | 0 |
| ResonanceSpectrum | counted | 15 | 15 | 0 | 0 |
| Rung5W1 | counted | 2 | 2 | 0 | 0 |
| Rung5W2 | counted | 13 | 13 | 0 | 0 |
| Rung5W3 | counted | 1 | 1 | 0 | 0 |
| Rung5W4 | counted | 2 | 2 | 0 | 0 |
| Rung5W5 | counted | 12 | 12 | 0 | 0 |
| Rung5W6 | counted | 7 | 7 | 0 | 0 |
| SMFermions | counted | 23 | 23 | 0 | 0 |
| SMGaugeAlgebra | counted | 11 | 11 | 0 | 0 |
| SMHiggsBreaking | counted | 42 | 42 | 0 | 0 |
| SMLagrangian | counted | 19 | 19 | 0 | 0 |
| Scaffold32 | counted | 11 | 11 | 0 | 0 |
| SchrodingerDynamics | counted | 49 | 49 | 0 | 0 |
| SchrodingerSmalls | counted | 24 | 24 | 0 | 0 |
| SchwartzComplete | counted | 2 | 2 | 0 | 0 |
| SchwartzSpace | counted | 14 | 14 | 0 | 0 |
| SecondQuantDGamma | counted | 18 | 18 | 0 | 0 |
| SecondQuantGamma | counted | 33 | 33 | 0 | 0 |
| SexagesimalClock | counted | 31 | 31 | 0 | 0 |
| SpectralAction | counted | 2 | 2 | 0 | 0 |
| SpectralActionBridge | counted | 12 | 12 | 0 | 0 |
| SpectralActionFinite | counted | 55 | 55 | 0 | 0 |
| SpectralClock | counted | 14 | 14 | 0 | 0 |
| SpectralFrontier | counted | 16 | 16 | 0 | 0 |
| StoneFiniteDim | counted | 4 | 4 | 0 | 0 |
| StoneFiniteDim2 | counted | 3 | 3 | 0 | 0 |
| TRO | counted | 6 | 6 | 0 | 0 |
| ThermalClock | counted | 33 | 33 | 0 | 0 |
| ThermalKMS | ambig-1 | 1 | 1 | 0 | 0 |
| ThermalKernel | counted | 13 | 13 | 0 | 0 |
| ThermalPreCompensation | counted | 24 | 24 | 0 | 0 |
| ThreeGen | counted | 20 | 20 | 0 | 0 |
| TranslationContinuity | counted | 10 | 10 | 0 | 0 |
| TriadicPin | counted | 0 | 0 | 0 | 0 |
| TriadicScreening | counted | 19 | 19 | 0 | 0 |
| TritGrading | remainder | 27 | 27 | 0 | 0 |
| TwistedTriple | counted | 93 | 93 | 0 | 0 |
| TwoDirections | counted | 8 | 8 | 0 | 0 |
| UltimateReduction | counted | 6 | 6 | 0 | 0 |
| WeldDuality | counted | 73 | 73 | 0 | 0 |
| WickSigns | counted | 31 | 31 | 0 | 0 |
| WightmanAxioms | ambig-1 | 1 | 1 | 0 | 0 |
| WightmanRepin | counted | 14 | 14 | 0 | 0 |
| WightmanTargets | remainder | 0 | 0 | 0 | 0 |
| WindingRing | counted | 14 | 14 | 0 | 0 |
| XYZTripotents | counted | 90 | 89 | 1 | 0 |
| YukawaInteraction | counted | 119 | 119 | 0 | 0 |
