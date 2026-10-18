# Active Cartesian Modular Dynamics: Machine-Verified Foundations

**Jeffrey Michael Gurd — Nexus Research (independent)**
**2026-10-17 — Version 3.**

Repository: https://github.com/jeffgurd888/thet-logos

> "If we don't stop worrying about the Almighty dollar, we're not
> going to change the world!"
> — Caleb Gurd, as remembered by his father.

**Version note.** Version 1 (2026-10-15; DOI: 10.5281/zenodo.23408680)
reported the program through Rung 8, together with the SM-Match program
and the first round of the theories intake. Version 2 (2026-10-16;
DOI: 10.5281/zenodo.23427964) added the closing of Rung 8's bosonic
half (Rung 8B, §8B), fermionic second quantization (Rung 9, §9),
bosonic second quantization (Rung 10, §10), and a fenced
background-algebra appendix (Appendix A). Version 3 adds: the
infinite-mode free theory (Pitch 2, §10A); interacting Hamiltonians at
finite modes for both statistics, with the Pitch 3 verdict stated
exactly as ruled (§10B); finite-dimensional Schrödinger dynamics
(§10C); the discharge of Rung 7's boost window (§7 amendment);
the graph-Laplacian bridge exhibit (Appendix A); and the opening
stages of the continuum pitch (Pitch 4, §13A) — the lattice scoping,
Stage 0, Stage 1a, and Stage 1b in its four sub-stages. It also
carries a full re-audit of §16 (what is NOT claimed): two lines
carried from Version 2 were overtaken by the work and are amended
in the open (§0, corrections to Version 2). Everything else is
carried from Version 2 unchanged except as amended in the open
where dated amendment notes say so. Version 3 is published as a new
version of the Version 2 record; its DOI is minted on publication.

---

## Abstract

This paper states exactly what the machine has verified in the Active
Cartesian Modular Dynamics (ACMD) program through Pitch 4, Stage 1b,
together with the SM-Match program and the first round of the theories
intake. Every
theorem named here is proved in Lean 4 (tier T1), explicitly axiomatized
with proved consequences (T2), stated as a labeled open target (T3/T5),
or recorded as refuted. The program is machine-verified mathematical
*scaffolding toward* a rigorous four-dimensional quantum field theory: a
finite spectral triple and its classification; the Connes–Kreimer Hopf
algebra of renormalization; the almost-commutative product with its
twist derived rather than assumed; analytic and Hilbert-space
infrastructure for a concrete model; verdicts on all six Wightman axioms
in a one-mode fermionic model; genuine Schwartz test-function machinery
and a geometric Poincaré action; a finite-dimensional Stone theorem and
a joint functional calculus for commuting symmetric operators; a
Fock-space inner product with proved creation/annihilation adjoints on
both the fermionic and bosonic sides; fermionic second quantization —
the functorial lift Γ(U), the differential lift dΓ, and a free
Hamiltonian whose gap is *derived* at finite modes; the bosonic dΓ lift
with its own derived free gap, and the bosonic Γ(U) lift, completed as
a verified functor by the same-day campaign that proved the two
permanent identities its functoriality had been priced at; a structural
match against the Standard Model's gauge algebra, fermion content,
classical Lagrangian sectors, and Higgs breaking pattern; and fit
verdicts for KMS theory, classical Yang–Mills, Haag–Kastler algebraic
QFT, and the finite spectral action. Version 3 adds: the free theory
at countably many modes for both statistics, with the derived free
gap in the eigenvalue-on-finite-particle-domain sense (Pitch 2);
interacting Hamiltonians at finite modes — the fermionic campaign
stands whole with gap persistence, the bosonic campaign stands except
for essential self-adjointness, its sole priced clause (Pitch 3);
unitary Schrödinger dynamics with picture equivalence and proved
time-invariance of the interacting gap clusters; full
restricted-Lorentz invariance of the free one-particle mass-shell
measure (the Rung 7 boost window, discharged); and the opening of the
lattice road toward the continuum (Pitch 4): Wilson-action lattice
gauge theory with exact gauge invariance, the Gibbs measure and
correlation package, Elitzur's theorem at a general gauge group and
every coupling, the reflection structure, the
Osterwalder–Schrader form with positivity proved at zero coupling and
reduced at general coupling to one named lemma, the OS Hilbert space,
and the transfer matrix — with the lattice gap proved exactly at
zero coupling and fenced, with its price, at general coupling.

**What this is not.** No continuum limit is claimed. No interacting 4D
quantum field theory is claimed. Interacting Hamiltonians *are*
constructed (§10B) — at finite modes, for matter self-interaction
only, with no gauge field; no interacting continuum theory of either
statistics is constructed, and no scattering content appears anywhere.
The Yang–Mills existence and mass gap problem
is the program's stated horizon and mission target; it is not claimed,
approached in the Clay sense, or implied by anything below. The mass
gap appears in this paper only as a fixed, quarantined target statement
against which future partial results can be measured; the gaps that
*are* derived below (§§9, 10, 10A, and the lattice gap of §13A) are
gaps of free Hamiltonians at finite or countably many modes, of an
interacting finite-mode Hamiltonian under a proved persistence
threshold, and of a finite-lattice transfer matrix at zero coupling —
labeled as such wherever they occur. **Parts of the official Clay
Yang–Mills statement closed by this corpus: 0.**

**Tier key.** T1: proved in Lean 4, zero `sorry`s. T2: axiomatized, with
proved (T1) consequences. T3: theorem stated, proof open, labeled
in-file. T5: opaque, quarantined, or priced window — theorem-shaped,
content not established. KILL: refuted or withdrawn; returns only as a
new entry by proof.

**Verification status.** All verification claims for Rungs 1–8 were
re-checked on 2026-10-15 (§0). That re-check raised two flags — the
finite spectral-action proofs failed to compile under the pinned
toolchain (§12) and the Morley gauntlet file could not be rebuilt to
completion in that pass (§13) — and **both flags were resolved on
2026-10-15**: `SpectralActionFinite.lean` was repaired (proof-local
fixes only; no statement changed; no `sorry`/`admit`/axiom added) and
its FIT verdict stands restored (§12), and `EdgeSignature.lean` was
re-verified by a standalone green build (exit 0; zero `sorry`/`admit`;
axiom checks on the 13 headline theorems clean; §13). The material
added in Version 2 (§§8B, 9, 10, Appendix A) was verified at its
landings on 2026-10-15/16 as reported in the §0 addendum. The material
added in Version 3 (§§10A, 10B, 10C, 13A, the §7 amendment, and the
Appendix A bridge exhibit) was verified at its landings on
2026-10-16/17 as reported in the §0 Version 3 addendum, where every
count in this paper is re-derived from the current sources by a
single stated method.

---

## 0. Verification protocol and corpus inventory

**Counting method (uniform, reproducible).** All counts in this paper are
counts of `theorem` and `lemma` declarations, obtained by the regular
expression `^\s*(private\s+|protected\s+)?(theorem|lemma)\s` applied to
every file in `lean/ThetLogos/`. Counts include
auxiliary lemmas; they are counts of declarations, not of "importance."
**Inventory freeze:** the corpus was inventoried at commit `790c1e0` on
2026-10-15. Work landing after the freeze (a Rung 9 start and a ternary
substrate module, both in progress under separate directives) is outside
this paper's scope and is not assessed here.

**Corpus totals (exact).**

| Scope | Files | Theorem/lemma declarations |
|---|---|---|
| Whole Lean corpus (`lean/ThetLogos/`) | 77 | **2,016** |
| ACMD program files (Rungs 1–8, SM-Match, intake, Morley, targets/dossiers) | 64 | **1,352** |
| Earlier exploratory campaigns in the same repository (CF-kernel arc, exotic sectors, chromatic and related work) | 13 | 664 |

The figure "300+" that circulated in earlier drafts of program summaries
was never derived from a count of this corpus. It is withdrawn and replaced
by the exact counts above.

**Build (2026-10-15, reported exactly).** `cd lean && lake build`
completes successfully (3,324 jobs). Stated plainly: the root module
`ThetLogos.lean` imports only 14 core modules, so the remaining 63 modules
were additionally built one by one (`lake build ThetLogos.<Module>`).
Result: **74 of 77 modules build green.** The three exceptions:

- `SpectralActionFinite.lean` **failed** at the 2026-10-15 re-check:
  four proof errors
  (`simp` made no progress / failed rewrite at lines 942, 1006, 1024,
  1074), all inside the a₂ trace-computation proofs and consistent with
  Mathlib deprecation drift since the file's 2026-10-11 verification.
  No statement was changed and no `sorry` introduced; the proofs no
  longer closed under the pinned toolchain. **Repaired the same day
  (2026-10-15): proof-local fixes only; the file builds green again and
  the FIT verdict of §12 stands restored** (theories-intake dossier
  amended accordingly).
- `SpectralActionBridge.lean` failed transitively (it imports the file
  above); restored with the repair.
- `EdgeSignature.lean` (the Morley gauntlet file, §13): two rebuild
  attempts on 2026-10-15 timed out (10 and 25 minutes, under heavy
  machine contention) without emitting any error — the build did not
  finish in that pass. **Re-verified later on 2026-10-15 by a standalone
  build: exit 0, zero `sorry`/`admit`, axiom checks on the 13 headline
  theorems clean. Closed.**

A minor wart, recorded for completeness: two declaration names collide
across modules in the shared `ThetLogos` namespace (`vacuum_cyclic` in
`FreeField` and `FermionicFock`; `Dprod` in `ProductTriple` and
`CausalProduct`), so those module pairs cannot be imported into a single
environment. Each module builds and verifies on its own. Wiring the newer
modules into the root import list, and repairing the spectral-action
proofs, are queued mechanical follow-ups.

**Sorry hygiene (exact).** The corpus contains exactly **seven** `sorry`s,
all pre-existing, all labeled in-file, none introduced by Rungs 1–8,
SM-Match, or the intake:

| Location | Count | Tier | Content |
|---|---|---|---|
| `BlockedQuestions.lean` (lines 76, 108, 140, 194, 274) | 5 | T5 | Open conjectures Q1–Q5, filed as questions |
| `ModularTime.lean:206` | 1 | T3 | `kms_identity_diagonal`; numerically verified, proof open |
| `XYZTripotents.lean:492` | 1 | T5 | `xyz_tripotents_exist`; single documented target |

There is no `admit` anywhere in the corpus. Every other occurrence of the
word "sorry" in the sources is documentation prose, mostly statements that
a file contains none.

**Axiom footprint (spot-checked 2026-10-15).** `#print axioms` was run
on thirteen headline results. Eleven depend only on Lean's standard
axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`:
`antipodeAxiomEval_proved`, `modularFlux_selfAdjoint`, `w5_span_true`,
`wick_four_point_operator`, `schwartzComplete_discharge`,
`jointFC_spectralMapping`, `higgs_stabilizer_is_Q`, `gibbs_kms_weight`,
`stone_finiteDim`, `ann_adjoint`, `adag_adjoint`. The two labeled
exceptions behave exactly as their labels say: `pauliBounded` depends
additionally on the one T2 axiom `pauli_compactResolvent`, and
`trace_collapse_hypothesis_fails` on the `CausalProduct` file-level T2
product axioms. And `kms_identity_diagonal` depends on `sorryAx` —
precisely its T3 label.

### v2 addendum (2026-10-16): increments since the Version 1 freeze

The Version 1 freeze above stands as the 2026-10-15 record. The work
that landed after it — and that Version 2 reports — is inventoried here
by the same counting method, as increments.

**Program total (Version 2, decomposed).** Version 2's program total,
by the same decomposed method as the §0 table, is **1,648**

| Increment | Files | Theorem/lemma declarations (definitions counted separately) |
|---|---|---|
| Rungs 1–8 era (Version 1 freeze) | 64 program files | 1,352 |
| Rung 9 — fermionic second quantization (§9) | 2 | +50 (plus 13 definitions) |
| Rung 8B — bosonic assembly (§8B) | 1 | +31 (plus 6 definitions) |
| Rung 10 — bosonic second quantization (§10) | 2 | +31 (plus 13 definitions) |
| Background algebra — sexagesimal clock (Appendix A) | 1 | +31 (plus 12 definitions, 1 structure) |
| Γ functor campaign — Rung 10 Task 3 closed (§10) | 1 | +42 (plus 8 definitions) |
| Background algebra — flux-twist toy (Appendix A) | 1 | +38 (plus 10 definitions) |
| Background algebra — weld duality (Appendix A) | 1 | +73 (plus 18 definitions) |
| **Program total (decomposed)** | | **1,648** |

The ternary substrate module of Appendix A (`TritGrading.lean`,
350 lines) also landed after the Version 1 freeze; it is reported
qualitatively in Appendix A and carries no separate increment in the
decomposed chain above.

**Builds (as reported at each landing).** The root `lake build` was
green (3,325 jobs, exit 0) at the Rung 9, Rung 8B, and Rung 10 landings,
with the pre-existing corpus untouched. The newer rung modules are not
in `ThetLogos.lean`'s root import list — the same staging as at
Version 1 — and are verified by targeted builds, each green:
`ThetLogos.SecondQuantGamma` and `ThetLogos.SecondQuantDGamma`
(Rung 9, within the root build); `ThetLogos.BosonicAssembly` (2,452
jobs); `ThetLogos.BosonicSecondQuant` (2,453 jobs);
`ThetLogos.BosonicGamma` (2,454 jobs); `ThetLogos.SexagesimalClock`
(3,118 jobs, zero errors, zero warnings); `ThetLogos.FluxTwist`
(3,120 jobs); `ThetLogos.WeldDuality` (3,120 jobs). Wiring the newer modules into
the root import list remains a separate, queued decision.

**Sorry hygiene (increments).** The new files introduce no `sorry` and
no `admit`: zero-sorry sweeps are reported clean for both Rung 9 files,
for `BosonicAssembly.lean`, for both Rung 10 files, for
`TritGrading.lean`, for `SexagesimalClock.lean` (which also has no
`native_decide`), and for `FluxTwist.lean` and `WeldDuality.lean`
(zero `sorry`/`admit`/`native_decide` in code for both). The corpus
total of §0 — exactly seven, all
pre-existing and labeled — is unchanged.

**Axiom footprint (increments).** `#print axioms` spot-checks on the
new headline results return exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new axioms:
every headline theorem of both Rung 9 files (per that rung's dossier);
eleven named headlines of Rung 8B, including `adjoint_relation`,
`ccr_mixed`, `numberOp_basis`, `sector_orthogonal`, and
`cycSub_eq_top`; fifteen named headlines of Rung 10 across its three
tasks, including `dgammaBos_adjoint`, `freeHamiltonianBos_eigenvalue_gap`,
and `gammaBos_apply_basis`; and eight named headlines of the
sexagesimal clock module, including `crtEquiv` and
`ClockGrading.reduceToTrit`; six named headlines of the flux-twist
module, including `twistedShift_unitary` and
`twistedShift_mul_gaugeMatrix`; and seven named headlines of the weld
module, including `trace_weldPlus`, `etaCorr_sq`, and
`signature_etaDirac`. The clock module's
`lcm_one_through_six` depends on no axioms at all.

<!-- V2 NOTE (parent audit, 2026-10-16): the two Version 1 re-verification flags (SpectralActionFinite build failure / suspended FIT, §12; EdgeSignature not re-verified, §13) were resolved on 2026-10-15 — repair completed (FIT restored; intake dossier amended) and standalone re-verification green, respectively — and §0, §12, §13 and the abstract's verification paragraph have been updated together in this draft to state the full sequence: flag raised, then resolved. -->

### v3 addendum (2026-10-17): increments since the Version 2 freeze, counted by one method

The Version 2 record above stands as published. The work that landed
after it — and that Version 3 reports — is inventoried here. For this
addendum every count was **re-derived from the current sources** (at
commit `4380a2a`) by a single method, stated exactly so any reader
can reproduce it:

**Counting method (Version 3 — strict line-initial, retained).**
A theorem or lemma is counted when a line of the comment-stripped
source begins at column 0 with `theorem` or `lemma`: the regular
expression `^(theorem|lemma) ` applied after stripping Lean
comments (line and nested block comments). This is the Version 2
§0 pattern, retained unchanged by the author's decision of
2026-10-17, taken after both candidate rules had been computed
and compared (see the recount note below): the strict rule is the
one whose total any reader can reproduce with the simplest
possible grep, and it never overcounts. Definitions are counted
by the analogous line-initial pattern over
`def`/`abbrev`/`structure`/`instance`, admitting the standard
same-line prefixes (an attribute, `noncomputable`, `private`,
`protected`) that definition keywords routinely carry; the
program total itself is the theorem/lemma count. The recount
consequences follow, recorded here rather than absorbed silently:

- **The Version 2 total stands.** Recounting the Version 2 scope
  by the strict rule gives exactly its published **1,648**, and
  the Rung 9 increment is 50 as published in §0. Fifteen
  declarations in today's program modules carry a same-line
  `@[simp]` attribute prefix and are therefore **not** counted
  by the strict rule; an attribute-inclusive count of the same
  modules totals 2,432. The fifteen, all present and verified
  since their files landed: `gamma_apply` (Rung 9, §9);
  `loopEnd_nil`, `loopEnd_cons`, `loopProd_nil`, `loopProd_cons`
  (Pitch 4 Stage 0 — its increment is 68, as its landing dossier
  stated); `fermConfigEmb_apply`, `fermConfigEmbLim_apply`,
  `configEmb_apply`, `configEmbLim_apply` (Pitch 2 Campaign A —
  its increment is 57 line-initial, not the attribute-inclusive
  61 of its dossier); and `boostLin_apply_zero`,
  `boostLin_apply_one`, `boostLin_apply_two`,
  `boostLin_apply_three`, `boostLin_symm_apply_zero`,
  `boostLin_symm_apply_one` (the Rung 7 boost discharge —
  80 line-initial, not the attribute-inclusive 86 of its
  dossier).
- **The running chain is corrected.** The decomposed chain
  published in the repository's README at the time of assembly
  totaled 2,427, because it summed the landing dossiers' figures
  under their two historical patterns: the Pitch 2 and
  MassShellBoost dossiers counted attribute-inclusive (+4 and
  +6 over strict), the rest counted strict. Under the single
  strict rule the program total is **2,417**, and Version 3
  reports that figure everywhere.

**Program total (Version 3, decomposed).**

| Increment | Files | Theorem/lemma declarations (definitions counted separately) |
|---|---|---|
| Rungs 1–8 era (Version 1 freeze) | 64 program files | 1,352 |
| Rung 9 — fermionic second quantization (§9) | 2 | +50 (plus 13 definitions) |
| Rung 8B — bosonic assembly (§8B) | 1 | +31 (plus 6 definitions) |
| Rung 10 — bosonic second quantization (§10) | 2 | +31 (plus 13 definitions) |
| Background algebra — sexagesimal clock (Appendix A) | 1 | +31 (plus 13 definitions and structures) |
| Γ functor campaign — Rung 10 Task 3 closed (§10) | 1 | +42 (plus 8 definitions) |
| Background algebra — flux-twist toy (Appendix A) | 1 | +38 (plus 10 definitions) |
| Background algebra — weld duality (Appendix A) | 1 | +73 (plus 18 definitions) |
| *Subtotal — Version 2 scope (strict recount = as published)* | | *1,648* |
| Pitch 2 — free theory at countably many modes (§10A) | 5 | +137 (plus 57 definitions) |
| Pitch 3 Campaign 1 — fermionic interaction (§10B) | 1 | +58 (plus 15 definitions) |
| Schrödinger dynamics (§10C) | 1 | +49 (plus 10 definitions) |
| Pitch 3 Campaign 2 — bosonic interaction (§10B) | 1 | +69 (plus 21 definitions) |
| Rung 7 boost window discharged (§7 amendment) | 1 | +80 (plus 15 definitions) |
| Background algebra — bridge exhibit (Appendix A) | 1 | +29 (plus 7 definitions) |
| Pitch 4 Stage 0 — finite lattice gauge theory (§13A) | 1 | +68 (plus 33 definitions and instances) |
| Pitch 4 Stage 1a — correlations and Elitzur (§13A) | 1 | +68 (plus 13 definitions) |
| Pitch 4 Stage 1b-A — reflection structure (§13A) | 1 | +67 (plus 16 definitions) |
| Pitch 4 Stage 1b-B — OS form and positivity (§13A) | 1 | +44 (plus 10 definitions) |
| Pitch 4 Stage 1b-C — OS Hilbert space (§13A) | 1 | +42 (plus 17 definitions) |
| Pitch 4 Stage 1b-D — transfer matrix (§13A) | 1 | +58 (plus 13 definitions) |
| **Program total (decomposed, strict line-initial method)** | | **2,417** |

As at Version 2, the ternary substrate module (`TritGrading.lean`,
27 declarations) is reported qualitatively in Appendix A and carries
no separate increment in this chain. For reference only, the whole
Lean corpus as it stands today — 103 files, including the earlier
exploratory campaigns and every post-freeze module whether or not
it belongs to the program chain — counts **3,086** declarations by
the strict rule; that figure is an inventory of the tree, not a
program total, and is not a partition of the chain above.

Two raw-grep disclosures, so the counts can be checked without
surprise: in `FermionicInteraction.lean` a raw line count gives 59
hits — the 59th is the word "theorem" opening a line inside the §4
header comment, disclosed in that campaign's dossier; the
comment-stripped count is 58. In `SchrodingerDynamics.lean` the raw
count gives 52 hits, of which exactly 3 are header or
comment prose, disclosed in its dossier; the count is 49.

**Builds (as reported at each landing, parent-verified).** Every
Version 3 module was verified by a targeted build
(`lake build ThetLogos.<Module>`), each green, at its landing:
Pitch 2 Campaign A modules (2,456 jobs) and Campaign B (3,207 jobs
across the pitch modules); `ThetLogos.FermionicInteraction`
(3,297 jobs); `ThetLogos.SchrodingerDynamics` (3,319 jobs);
`ThetLogos.BosonicInteraction` (2,704 jobs targeted);
`ThetLogos.MassShellBoost` (3,463 jobs);
`ThetLogos.BridgeLaplacian` (3,117 jobs);
`ThetLogos.LatticeGauge` (3,390 jobs);
`ThetLogos.LatticeCorrelations` (3,391 jobs);
`ThetLogos.LatticeReflection` (3,392 jobs);
`ThetLogos.LatticePositivity` (3,393 jobs);
`ThetLogos.LatticeOSSpace` (3,550 jobs);
`ThetLogos.LatticeTransfer` (3,551 jobs). The newer modules are
not in `ThetLogos.lean`'s root import list — the same staging as at
Versions 1–2, disclosed in each module header; wiring them in
remains a separate, queued decision.

**Sorry hygiene (re-derived 2026-10-17).** A comment-stripped sweep
of all 103 corpus files finds the word `sorry` in code **exactly
seven times** — the same seven labeled occurrences of the §0 table
(five T5 in `BlockedQuestions.lean`, one T3 in `ModularTime.lean`,
one T5 in `XYZTripotents.lean`) — and the word `admit` in code
**zero times**. None of the Version 3 modules introduces either;
every other occurrence of either word in the sources is prose,
mostly statements that a file contains none. The corpus total of
§0 — exactly seven, all pre-existing and labeled — is unchanged.

**Axiom footprint (increments).** `#print axioms` spot-checks on
the Version 3 headline results return exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new
axioms: nine named headlines of Pitch 2 Campaign A and eight of
Campaign B; `hamInt_gap_persistence`, `densityInt_not_dgamma`, and
`intOp_isSymmetric` of Pitch 3 Campaign 1; ten named headlines of
Schrödinger dynamics; six named headlines of Pitch 3 Campaign 2;
six named headlines of the boost discharge
(`boostInvariance_window_proved` among them); eight named
headlines of the bridge exhibit; eight of Stage 0; the five scoped
headlines of Stage 1a (`gibbsExpect_eq_integral`,
`elitzur_single_link` among them); six of Stage 1b-B; eleven of
Stage 1b-C; and eleven of Stage 1b-D (`transferOp_inner`,
`transferOp_isSelfAdjoint`, `transferOp_zero_apply` among them).

### Corrections to Version 2 (in the open)

Version 2 is a dated snapshot and is not retro-edited. Four of
its statements are overtaken by the work Version 3 reports, and
the recount above corrects the running chain built since Version 2. They are listed
here, and amended in place in the sections named:

1. **§16, "No infinite-mode or continuum Γ" — FALSE since
   2026-10-16.** Pitch 2 (§10A) verifies Γ at countably many
   modes for the free theory. The line is amended in §16; the
   continuum clause of it stands.
2. **§16 and the Version 2 abstract, "no interacting theory of
   either statistics is constructed" — overtaken by Pitch 3
   (§10B).** Interacting Hamiltonians at finite modes are
   constructed for both statistics. What stands: no interacting
   *continuum* theory, no gauge-coupled interaction, no
   scattering. The lines are amended in the abstract and §16.
3. **§7's mass-shell track and §14 item 3 — the priced boost
   lemma is discharged.** The one-dimensional Jacobian identity
   is proved and the window closed whole (§7 amendment);
   §14 item 3 is marked discharged.
4. **§14 item 2 — the infinite-mode limit is discharged in the
   free theory** by Pitch 2 (§10A); the item is amended to its
   priced remainder (the spectral gap statement; rectangular
   functoriality at Task 3b scope).
5. **The counts stand as published.** Under the strict
   line-initial rule retained for Version 3, the Version 2
   program total recounts to exactly its published 1,648, and
   the Rung 9 count is 50 as printed. What the recount corrects
   is the running chain assembled since (see the addendum):
   two landing dossiers counted attribute-prefixed declarations;
   the strict full-program total is 2,417.

---

## 1. Rung 1 — The finite spectral triple (T1) — STANDS

The finite factor is a concrete matrix spectral triple; its classification
and constraint census are machine-checked.

- **Classification and census.** The generator family `smGen : Fin 12`
  gives 144 pairs; the order-zero condition is checked machine-side over
  147,456 complex components (`order_zero_comm`). Three-generation
  inheritance is proved in `ThreeGen.lean` (20 declarations), including
  `smGen3_order_zero` and the Kronecker-factorization identities. The
  576-pair order-one census is a T4 Python scan, not a Lean proof.
- **Modular dynamics.** `thermal_flux_vanishes`: the modular flux vanishes
  identically on Gibbs states for every inverse temperature β.
  `exists_activeDriver`: a non-equilibrium driver producing nonzero flux
  exists. `modularFlux_selfAdjoint`: the flux φ = i[K, D] is Hermitian.
  Gauge covariance and trace gauge-invariance of the flux are proved.
- **Ultimate reduction.** `UltimateReduction.lean` proves 6 T1 theorems,
  including `dynamicallyFrozen_of_noHeat_noGauge` and
  `equilibriumKillsFlux`. The same file records finite-level kills:
  micro-vortices (no vorticity operator exists in the finite triple) and
  the vortices→matter→gravity chain (needs continuum data).
- **Connes–Kreimer Hopf algebra.** `Renormalization.lean` (60 declarations)
  formalizes the Hopf algebra of rooted trees: coproduct, B₊ grafting,
  counity, coassociativity. The record on the antipode is two-sided and
  both sides are kept: the as-stated antipode axiom was **refuted**
  (`antipodeAxiom_false`), and the corrected evaluation version was
  **proved** (`antipodeAxiomEval_proved`, T5→T1). The refuted statement is
  not laundered into the proved one.

## 2. Rung 2 — The almost-commutative product (T1) — STANDS

`ProductTriple.lean` (63 declarations) builds the product of an axiomatized
manifold factor with the finite triple.

- **Product Dirac identity.** `Dprod_sq`: D_prod² = D_M² ⊗ 1 + 1 ⊗ D_F².
  The formerly axiomatized `product_sum_of_squares` was promoted to a
  proved T1 — upgraded, not resurrected.
- **Twist derived, not assumed.** The product twist is the flip on the
  doubled product algebra (`flipProd_involutive`,
  `flipProd_CM_regular`); the candidate ρ_M ⊗ ρ_F product twist was killed
  (it does not typecheck).
- **Fluctuation decomposition.** `prod_commutator_decomp` splits inner
  fluctuations into manifold and finite parts.
- **KO data.** `koProd_signs`: KO signs ⟨−1, 1, −1⟩ (`koDim_add`:
  (4 + 6) % 8 = 2).
- **Causality re-entry.** `CausalProduct.lean`: the finite-level Span-5
  causality obstruction does not carry to the product
  (`trace_collapse_hypothesis_fails`, `product_not_forced_central` — T1
  consequences of the T2 product axioms, footprint labeled in §0). Genuine
  causal order is pinned at its exact price: global hyperbolicity.
- **The 6-dimensional caveat.** The surviving finite *represented* gauge
  algebra is six real dimensions: Option-A kills the represented M₃(ℂ)
  summand. The full Standard Model gauge group is not claimed from the
  finite factor. This caveat stands and is revisited precisely in §11.

## 3. Rung 3 — Lorentzian-structure pins (T2+T1, one partial) — STANDS

- **Antilinear J — promoted (T2+T1).** The obstruction (bare ℂ-modules; J
  not even statable) was removed by explicit enrichment of `TripleData`
  (sesquilinear form; positivity, nondegeneracy, completeness explicitly
  *not* assumed; antilinear `Janti` with KO axioms). Product theorems
  proved T1: `Jprod_sq` (J² = −1), `Jprod_D` (JD = DJ), `Jprod_Γ`.
- **Krein inner product — promoted (T2+T1).** Fundamental symmetry η with
  η² = 1 and form-self-adjointness proved (`ηprod_sq`, `ηprod_selfadj`).
  No adjoint operator is constructed and no spacetime signature is
  claimed: η is an abstract fundamental symmetry.
- **Twisted first-order condition — PARTIAL.** The opposite representation
  is built in the `conjJ`-shadow of a° = Ja*J⁻¹ (multiplication reverses,
  T1); the diagonal reduction is proved (`prodTwistedFOC_diag_reduce`).
  The exact remaining obstruction is priced: no `Star` instance on
  `Module.End` over the tensor module in this setting, and factor-level
  order-one is absent from the abstract `TripleData`.
- **Continuum scoping — priced roadmap, no limit claimed.** "Finite triple
  converges" language is killed with reason; the continuum is scoped
  per-axiom as future work.
- **Promotion honesty.** The Rung 3 promotions are T2-axiomatization plus
  T1 consequences — not derivation from analysis. This paper repeats that
  qualification wherever the promotions are cited.

## 4. Rung 4 — The analytic house (T1 + one T2 bridge) — STANDS

Directive: "Build the house and use the gaps as windows."

- **Bounded-triple instance for the concrete Pauli model.**
  `pauliBounded : BoundedAnalyticTriple` forms. Its mathematical content
  is proved T1 underneath (`pauliD_sub_det`, `pauliD_resolvent`,
  `pauliD_resolvent_compact` — finite-dimensionality is the whole proof of
  compactness); one model-specific T2 axiom (`pauli_compactResolvent`)
  bridges the deliberately opaque `HasCompactResolvent` predicate. The
  window is eliminable only by redefining that predicate transparently —
  a design decision, priced in the dossier. The model stays analytically
  trivial (scalar representation, vanishing commutators); it discharges
  analytic debt, not gauge content.
- **Hilbert completion and bounded \*-representation (T1).** Completion of
  the model is trivial (`CompleteSpace (EuclideanSpace ℂ (Fin 2))`); the
  bounded \*-representation of the Pauli algebra is proved with the *true*
  adjoint star, transported from matrix conjugate-transpose
  (`repScal_is_star_rep`). The incorrect `star := conjJ` construction was
  explicitly refused earlier in the program and stays refused.
- **Smeared field operators (14 T1).** Creator-half canonical
  (anti)commutation relations for smeared fermionic and bosonic fields,
  smeared Pauli exclusion, and one-point vanishing
  (`FieldOperators.lean`).
- **Wightman targets framed (T5, unproved by design).** All six axioms are
  stated as structured propositions with exact hypotheses, conclusions,
  and per-axiom prices (`WightmanTargets.lean`). Stating them is not
  proving them; Rung 5 takes the verdicts.

## 5. Rung 5 — The Wightman ascent on a one-mode model — STANDS

On a one-mode fermionic Fock model (∧(ℂ) ≅ ℂ², Majorana field
ψ(c) = c • (a† + a)), all six targets received T1 verdicts. These are
verdicts about the toy model and about the framings — not about 4D QFT.

- **W1 (fields exist): PROVED** (`w1_majorana`).
- **W2 (covariance): PROVED for ℤ₂ fermion parity** (`w2_parity`). This is
  explicitly *not* Poincaré covariance; the group is `ZMod 2` acting by
  parity.
- **W3 (spectrum condition): PROVED for the trivial translation
  representation** (`w3_trivial`) — a frame-consistency check (spectrum
  {0} ⊆ forward light cone), not Stone's theorem.
- **W4 (locality): PROVED** at s = +1 (`w4_majorana`); the one-mode model
  has no spacetime, so the spacelike hypothesis is vacuous.
- **W5 (vacuum cyclicity): REFUTED as framed; corrected version PROVED.**
  Monomial-*range* density is false even for a free fermion
  (`w5_framed_false`); the linear-*span* density the literature means is
  true (`w5_span_true`). The Rung 4 framing was strictly stronger than
  the literature; the refutation is a framing correction recorded as a T1
  result.
- **W6 (non-triviality): bosonic form proved but fermion-blind; corrected
  version PROVED.** The bosonic-form criterion gives −2 ≠ 0 for the free
  Majorana field — a documented false positive (`w6_majorana`); the
  corrected Koszul-sign Wick criterion vanishes as it should
  (`w6_fermionic_wick`).

Rung 5 files: `OneModeFermion.lean` (37 declarations) and `Rung5W1–W6`
(39 declarations).

## 6. Rung 6 — Infinite modes — STANDS

- **Schwartz machinery — premise correction, then GO.** The Rung 4/5
  framing "Mathlib has no Schwartz space" was wrong: Mathlib ships the
  full Schwartz machine (Doll 2026). `SchwartzSpace.lean` proves 14 T1
  results on genuine 𝒮(ℝ⁴, ℂ) — closure under derivatives and polynomial
  multiplication, temperate growth, Fourier inversion — and discharges
  the earlier T2 test-function marker. One genuine gap remained at this
  rung: no `CompleteSpace 𝒮(E,F)` instance in Mathlib (discharged at
  Rung 7, §7).
- **Poincaré — geometric half GO.** `PoincareAction.lean` (11
  declarations): the Lorentz group O(1,3) and Poincaré group as
  `Group` instances; the field action `f ↦ f(Λ⁻¹(x−a))` satisfies the
  group-action laws and is ℂ-linear in the test function
  (`poincareAct_mul`, `poincareActLin`). The one-particle unitary
  representation and second quantization stayed priced at this rung.
- **Wick combinatorics — PARTIAL.** `WickSigns.lean` (31 declarations):
  complete pairings of `Fin (2n)`, the Koszul sign, its independence of
  pair ordering, and the four-point signs (+1, −1, +1)
  (`koszulSign_four_point`). The operator Wick identity stayed priced
  (discharged at Rung 7 in a two-mode model).
- **Stone — analytic core T1.** `continuous_char_lift`: a continuous
  norm-one character of (ℝ,+) is `exp(i·a·t)` — the analytic core of
  Stone's theorem. The full finite-dimensional Stone theorem hit Lean
  engineering friction at this rung (discharged at Rung 7).

## 7. Rung 7 — The frontier — STANDS

Four of the five outstanding prices were discharged T1; the fifth was
narrowed. This rung also marks where formalized analysis currently stops.

- **Schwartz completeness — T1.** `schwartzComplete_discharge`
  (`SchwartzComplete.lean`, 415 lines): 𝒮(ℝⁿ, ℂ) is Fréchet-complete —
  the genuine Mathlib gap from Rung 6, closed by a direct proof
  (countable uniformity basis → uniform convergence of all iterated
  derivatives → decay bounds pass to the limit).
- **Operator Wick identity — T1, with a correction.** In a concrete
  two-mode fermionic Fock model, `wick_four_point_operator`:
  ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ − G₀₂G₁₃ + G₀₃G₁₂, with all Wick hypotheses
  *proved* (CAR, Hilbert adjoints, quasi-free move), and the Koszul signs
  discharged against Rung 6. Correction recorded in-file: Rung 6's priced
  hypothesis pair ({ψᵢ,ψⱼ} = 2Gᵢⱼ together with ω(ψᵢψⱼ) = Gᵢⱼ) is jointly
  false in the model; the identity holds with the full non-symmetric G.
  The n-point expansion remains priced (T5).
- **Stone / joint spectral ONB — T1.** `jointSpectral_orthonormalBasis`
  (commuting symmetric family ⇒ orthonormal basis of joint eigenvectors)
  and the full finite-dimensional Stone theorem `stone_finiteDim`
  (strongly continuous unitary one-parameter group ⇒ skew-adjoint
  generator diagonal in that basis, `(U t)(b k) = exp(i·a k·t) • b k`).
- **Joint functional calculus — T1.** For commuting bounded symmetric
  operators, `SpectralFrontier.lean` proves a joint functional calculus
  stronger than Mathlib's single-operator continuous functional calculus,
  with the spectral mapping theorem `jointFC_spectralMapping`.
- **Mass-shell track — PARTIAL.** The invariant measure d³p/2E_p is
  constructed as a density-weighted pushforward; its integral formula and
  rotation invariance are proved, and the restricted (proper
  orthochronous) Lorentz group is formed as a subgroup. Boost invariance
  is priced at exactly one missing lemma: the one-dimensional Jacobian
  identity |φ′| = E′/E for the x¹-boost. The one-particle representation
  law and unitarity-from-invariance are proved at function level;
  strong continuity and the linear-isometry packaging remain priced.
  Second quantization was blocked at this rung by the Fock inner-product
  gap — the subject of Rung 8.
- **Amendment (2026-10-17) — the boost window is DISCHARGED WHOLE.**
  The one missing lemma priced above is proved, and the cap the
  pricing flagged as likely is proved with it.
  `MassShellBoost.lean` (1,629 lines; 80 declarations, 15
  definitions; targeted build green, 3,463 jobs; six headline
  axiom checks exactly `[propext, Classical.choice, Quot.sound]`).
  The x¹-boost is built as a concrete element of the restricted
  Lorentz group (`boostRestricted`: Minkowski-form preserving,
  determinant 1, orthochronous); the shell parametrization is
  intertwined with the boosted-energy identity
  E′ = γ(E − βu₁); the priced Jacobian identity is proved exactly
  as scoped — |φ′(u₁)| = E_{φ(u₁)}/E_u, with φ strictly monotone
  and surjective (`boostSlice_jacobian`, `boostSlice_abs_deriv`) —
  and the density cancellation (E′/E)·(2E′)⁻¹ = (2E)⁻¹ assembles
  into `boost_preserves_massShellMeasure`: the boost's shell
  action is measure-preserving for the mass-shell measure. The
  cap: **every** restricted Lorentz transformation factors as
  (spatial lift)⁻¹ ∘ (x¹-boost) ∘ (spatial lift) — the spatial
  factor built from a Householder reflection, with the block
  lemma that a Lorentz map fixing the time direction is a
  spatial lift — so `boostInvariance_window_proved` holds for
  every Λ: **the free one-particle mass-shell measure is
  invariant under the full restricted Lorentz group.** Scope,
  exactly: the *free*, *one-particle* measure. This rung's other
  priced items are untouched by the discharge: **strong
  continuity** of the one-particle representation remains priced
  (repriced by the 2026-10-17 parked-fleet gauntlet: the
  translation part is a discharge-ready S — the file itself names
  the dominated-convergence lemma and the dominator 4‖ψ‖²; the
  Lorentz part is S–M, with this discharge's Jacobian identity
  supplying the domination), and **Fock packaging** remains
  priced at M (a concrete orthonormal-basis port; the abstract
  SymmetricAlgebra route stays killed, §15).

## 8. Rung 8 — The Fock inner product — STANDS (fermionic) / PARTIAL (bosonic, closed at §8B)

- **Fermionic — STANDS.** `FermionicFock.lean` (43 theorems, 1,064 lines):
  the Fock space as ℓ² over occupation subsets, with Pauli exclusion
  automatic from the subset guards. Proved T1: creation/annihilation
  adjoints (`ann_adjoint`, `adag_adjoint` — the fermionic discharge of
  the W0 inner-product gap), the canonical anticommutation relations,
  sector orthogonality, the number operator with eigenvalues `S.card`,
  and vacuum cyclicity. **Fermionic second quantization is unblocked.**
  Priced windows, stated in-file: unitary equivalence with exterior-power
  subspaces, the infinite-mode limit, and the general-n Gram determinant
  (base case and reassembly proved; inductive step priced).
- **Bosonic — PARTIAL at this rung; closed at §8B.** `BosonicFock.lean`
  (25 theorems): ℓ² over finitely supported occupation configurations,
  with creation/annihilation as linear maps on a dense domain (the honest
  standard formulation for unbounded operators). The inner product,
  orthonormal basis, explicit basis actions, and the basis-level adjoint
  relation (`adjoint_basis` — the computational core of W0) are proved.
  The final linearity assembly of the full adjoint relation stalled on
  Mathlib API friction (submodule inner-product coercion handling) and is
  priced as engineering, not mathematics; the induction principle needed
  for the assembly is proved. CCR, number operator, and sector results
  follow from the basis actions by standard computations not yet
  formalized. *All of these were discharged in full at Rung 8B (§8B),
  with no weakened statements.*

## 8B. Rung 8B — Bosonic assembly (T1) — STANDS; the Rung 8 bosonic partial is closed

`BosonicAssembly.lean` (520 lines; 31 theorems and 6 definitions, zero
sorrys; imports `BosonicFock.lean`, which is unmodified) performs exactly
the assembly Rung 8 priced. All results are T1, on the dense
finite-particle domain `Dom d` over a finite mode set `Fin d` — the free
bosonic theory, stated with the same honesty labels as §8.

- **Full adjoint relation.** `adjoint_relation`: for all `x y : Dom d`,
  `⟪ann i x, y⟫ = ⟪x, adag i y⟫`, assembled from Rung 8's `adjoint_basis`
  by its own two-variable induction principle; the Rung 8 API friction
  yielded to an explicit motive. Companion form `adjoint_relation_adag`.
- **CCR on `Dom d`.** `ccr_mixed` — the mixed commutator
  `(ann i) ∘ₗ (adag j) − (adag j) ∘ₗ (ann i)` equals `1` if `i = j` and
  `0` otherwise, as linear maps on `Dom d` — together with `ccr_ann_ann`,
  `ccr_adag_adag` (annihilators commute; creators commute) and the
  pointwise form `ccr_mixed_apply`. Proved first on coefficient space and
  transported through the representation, not assembled by fiat.
- **Number operator.** `numberOp = ∑ i, (adag i) ∘ₗ (ann i)`, with
  `numberOp_basis`: the basis eigenvalue is the total occupation count,
  and `numberOp_vacuum`: the vacuum eigenvalue is `0`.
- **Vacuum and sectors.** `ann_vacuum` (annihilation kills the vacuum in
  `Dom d`); `sector_orthogonal`: sectors of distinct total occupation
  are orthogonal.
- **Vacuum cyclicity (stretch target, landed).** `cycSub_eq_top`: the
  submodule of `Dom d` generated from the vacuum by finitely many
  creation operators is everything.

Priced remainder, unchanged and not attempted here: bosonic Γ(U) (the
subject of §10, Task 3); the infinite-mode limit; unitary equivalence
with symmetric tensor-power sectors and the Gram/permanent formula
(blocked upstream on n-fold tensor inner products); the continuum
one-particle space and the mass-shell representation (the §9 Task 4
frontier).

---

## 9. Rung 9 — Fermionic second quantization (T1) — STANDS (Tasks 1–3) / PARTIAL (Task 4)

All results in this rung are T1: 50 theorems and 13 definitions across
two files, zero sorrys, with axiom spot-checks returning exactly
`[propext, Classical.choice, Quot.sound]` for every headline theorem.
Labels that apply to everything below: **free theory, finite modes.**
This rung is not a continuum QFT, not an interacting theory, and not
the Yang–Mills mass gap; the one gap in it is *derived*, and it is
labeled exactly where it lives.

- **Task 1 — the Γ lift: STANDS.** `SecondQuantGamma.lean` (992 lines,
  32 theorems, 10 definitions). For a one-particle matrix `M` on the
  mode space `Fin d`, `Γ(M)` is constructed on the Rung 8 fermionic
  Fock space by the compound-matrix (minor) formula. Proved:
  `gamma_one` (`Γ(1) = 1`); `gamma_mul` (`Γ(M * N) = Γ(M) * Γ(N)`);
  `gamma_adjoint` (`Γ(M*) = Γ(M)*`, in inner-product form);
  `gamma_vacuum` (`Γ(M)` fixes the vacuum, for every `M`);
  `gamma_sector` (`Γ(M)` preserves every n-particle sector);
  `gamma_inner` with `gamma_comp_self` and `gamma_self_comp` — for
  unitary `M`, `Γ(M)` is unitary as an operator identity; and
  `gamma_diagonal_basis` — `Γ(diag v)` multiplies a basis vector by the
  product of the selected phases. The supporting determinant core is
  proved in the same file, from scratch where Mathlib lacks it:
  `minorDet` and its calculus, the expansion `det_mul_expansion`, and
  the rectangular Cauchy–Binet formula `cauchy_binet_rect` (not in
  Mathlib at this toolchain), yielding the compound-matrix identity
  `minorDet_mul`.
- **Task 2 — the dΓ lift: STANDS.** `SecondQuantDGamma.lean` (329
  lines, 18 theorems, 3 definitions). `dΓ(M) = ∑ i, ∑ j, M i j •
  (a†ᵢ ∘ aⱼ)` as a finite sum of creation–annihilation composites.
  Proved: `dgamma_adjoint` (the adjoint of `dΓ(M)` is `dΓ(Mᴴ)`);
  `dgamma_one` (`dΓ(1)` is the Rung 8 number operator); sector
  preservation; `dgamma_basis_diag` — on a basis vector,
  `dΓ(diag λ) e_S = (∑ j ∈ S, λ j) • e_S`; and `dgamma_vacuum`.
- **Task 3 — the free Hamiltonian gap, DERIVED: STANDS.** For a diagonal
  one-particle Hamiltonian with eigenvalues `λ j ≥ 0`, set
  `freeHamiltonian λ = dΓ(diag λ)`. Proved: the vacuum is an
  eigenvector with eigenvalue `0` (`freeHamiltonian_vacuum`); every
  basis vector is an eigenvector with eigenvalue the sum of its
  occupied one-particle energies (`freeHamiltonian_basis`);
  self-adjointness; the expectation formula and its nonnegativity; and
  the derived gap itself — `freeHamiltonian_eigenvalue_gap`: if every
  one-particle eigenvalue is `0` or `≥ Δ`, then every non-vacuum
  eigenvalue of `H` is `≥ Δ`, with `free_gap_dichotomy` giving the
  eigenvalue dichotomy `0` or `≥ Δ`. **Label, precisely:** the
  one-particle gap `Δ` is an input, but the Fock-space gap is
  *computed* from the operator — as the sum of occupied one-particle
  energies — not assumed as a structure field and not inserted by
  definition. It is a statement about the **free** theory at **finite
  modes**. It is not the interacting Yang–Mills mass gap, and nothing
  in this rung touches the continuum theory.
- **Task 4 — quantum Poincaré implementation at finite modes:
  PARTIAL.** What lifts is proved, in form: `gamma_rep` — any
  one-particle unitary representation `ρ : G → Matrix` of any group `G`
  lifts through `Γ` to a unitary representation of `G` on Fock space
  (homomorphism, identity, vacuum fixed, sectors preserved, inner
  product preserved), discharging the *form* of Rung 6's second-
  quantization window at finite modes for any group whose action
  preserves the finite mode set. A concrete instance is implemented:
  `lattice_translation_rep`, the lattice translation group acting by
  diagonal phases, whose lift multiplies a basis vector by exactly the
  product of its occupied modes' phases — the finite-mode shadow of
  momentum additivity. What does **not** lift is priced exactly:
  (1) the mass-shell one-particle representation (Rung 6's window stays
  T5; no Lorentz-invariant hyperboloid measure or massive one-particle
  Hilbert space exists in Mathlib to restrict to finitely many modes,
  and this rung does not construct one); (2) boosts and continuum
  rotations (a boost mixes any finite momentum set into infinitely
  many modes; no finite mode set is preserved, so there is nothing for
  `Γ` to lift — the liftable symmetry at finite modes is exactly the
  mode-set-preserving subgroup); (3) the infinite-mode / continuum
  limit (needs the infinite-mode Fock construction, priced since
  Rung 8); (4) interaction (`Γ` and `dΓ` are the free lifts; no
  interacting Hamiltonian, gauge field, or Yang–Mills dynamics appears
  in this rung).

The free fermionic theory at finite modes is now complete as a
machine-checked package: Fock space (§8) + `Γ` + `dΓ` + free
Hamiltonian with derived gap + a unitary symmetry representation in
lifted form.

## 10. Rung 10 — Bosonic second quantization (T1) — STANDS (Tasks 1–3)

Two new modules (31 theorems and 13 definitions, zero sorrys;
`BosonicFock.lean` and `BosonicAssembly.lean` unmodified). Labels that
apply to everything below: **finite modes** (`Fin d`), operators on
the **dense domain** `Dom d` (finite-particle vectors), **free bosonic
theory**. This is not the interacting Yang–Mills theory and not a
Millennium claim. The Task 2 gap is *derived* for the free Hamiltonian
at finite modes — exactly the bosonic analog of §9 Task 3, with the
same scope.

- **Task 1 — the bosonic dΓ lift: STANDS.** `BosonicSecondQuant.lean`
  (531 lines, 25 theorems, 5 definitions).
  `dgammaBos d M = ∑ i, ∑ j, (M i j) • ((adag d i) ∘ₗ (ann d j))` on
  `Dom d`, mirroring §9's fermionic `dgamma` with the Rung 8B domain
  adjoint relations in place of finite-dimensional adjoints. Proved:
  `dgammaBos_adjoint` (`⟪dΓ(M) x, y⟫ = ⟪x, dΓ(Mᴴ) y⟫` on `Dom d`);
  `dgammaBos_one` (`dΓ(1) = numberOp`, connecting to §8B's number
  operator); `dgammaBos_vacuum`; `dgammaBos_basis_diag`
  (`dΓ(diag λ) e_c = (∑ i, λ i * (c i : ℂ)) • e_c`); sector
  preservation (`dgammaBos_mem_domSector`), with `domSector_coe`
  coercing the domain sectors into §8B's Fock sectors.
- **Task 2 — the bosonic free Hamiltonian gap, DERIVED: STANDS.** For
  `freeHamiltonianBos d lam = dΓ(diag λ)` with `λ i : ℝ`, proved:
  every basis vector is an eigenvector with eigenvalue
  `∑ i, λ i * (c i)` (`freeHamiltonianBos_basis`, with the coefficient
  form `freeHamiltonianBos_coord`); the vacuum eigenvalue is `0`;
  self-adjointness on `Dom d`; the expectation formula
  (`freeHamiltonianBos_expectation`) and its nonnegativity for
  `λ ≥ 0`; and the derived gap — `free_gap_dichotomy_bos` and
  `freeHamiltonianBos_eigenvalue_gap`: every eigenvalue of `H` on a
  nonzero vector of `Dom d` is a basis eigenvalue, hence `0` or `≥ Δ`
  whenever each one-particle eigenvalue is `0` or `≥ Δ`. As in §9, the
  one-particle gap `Δ` is an input and the Fock-space gap is computed
  from the operator; the statement is about the **free** theory at
  **finite modes**.
- **Task 3 — bosonic Γ(U): PARTIAL at the rung's first landing; CLOSED
  by the Γ functor campaign (2026-10-16, later the same day).**
  `BosonicGamma.lean` (215 lines, 6 theorems, 8 definitions). The
  fermionic Γ of §9 used determinant minors over subsets; bosons need
  **permanent** minors over occupation configurations, repetitions
  allowed. The lift is defined (`configsOfTot`, `configEnum`,
  `perMinor`, `normFactor`, `gammaKernel`, `gammaC`, `gammaBos`) and
  what the definition gives directly is proved: the kernel formula
  `gammaBos_apply_basis` (`Γ(M) e_c` is the sum, over configurations
  `c'` of the same total count, of `gammaKernel M c' c • e_{c'}`);
  `perMinor_of_tot_ne` (minors vanish across different total counts);
  `gammaBos_sector` (`Γ(M)` preserves the total-occupation sector);
  and `gammaBos_vacuum` (`Γ(M)` fixes the vacuum). **Priced
  remainder — the two obstructions, named exactly:** (1) `Γ(1) = 1`
  and the diagonal action `Γ(diag λ) e_c = (∏ i, λᵢ^{c i}) • e_c` both
  reduce, for this kernel, to the **fiber-permanent counting lemma**:
  the permanent of the fiber-indicator matrix (entries `1` where the
  enumerated positions of `c` agree, else `0`) equals `∏ i, (c i)!` —
  a finite but genuine counting argument about `Matrix.permanent` over
  repeated indices, not in Mathlib at this toolchain. (2)
  **Multiplicativity** `Γ(M)Γ(N) = Γ(MN)` and **unitarity** need a
  **permanent Cauchy–Binet identity for repeated indices**: expanding
  `per (M N)` over intermediate index functions and grouping them by
  their multiset image, with the `1/∏ c'!` weights matching the kernel
  normalization exactly — the bosonic analog of §9's rectangular
  Cauchy–Binet campaign, a separate campaign of comparable size.
  Until (1) lands, even `Γ(1) = 1` is unproved for this definition —
  so bosonic Γ is recorded as a *candidate lift with its kernel
  formula, vacuum, and sector preservation proved*, not as a verified
  functor. No statement was weakened to get here. **Closure
  (2026-10-16):** the functor campaign
  (`BosonicGammaFunctor.lean`, 1,161 lines, 42 theorems, 8 definitions,
  zero sorrys; targeted build green, 2,455 jobs; headline axiom checks
  exactly `[propext, Classical.choice, Quot.sound]`) proved both
  obstructions with their consequences: the fiber-permanent counting
  lemma (`permanent_fiberIndicator_configEnum`), `Γ(1) = 1`
  (`gammaBos_one`), the diagonal action (`gammaBos_diagonal_basis`),
  the permanent Cauchy–Binet identity for repeated indices
  (`perMinor_mul`, with the multiplicity-weight bookkeeping proved),
  multiplicativity (`gammaBos_mul`), and the unitarity package
  (`gammaBos_adjoint`, `gammaBos_comp_conjTranspose`,
  `gammaBos_conjTranspose_comp`, `gammaBos_isometry`). **Task 3 is
  closed; bosonic Γ is a verified functor on finite modes, and Rung 10
  stands whole.** Full record:
  `whitepaper/gamma-functor-campaign-2026-10-16.md`.

Priced remainder beyond this rung: the infinite-mode limit (no longer
`Fin d`); the symmetric tensor-power
unitary equivalence / permanent formula in Mathlib's tensor API (still
blocked upstream, as priced at §8); and the standing frontier —
continuum limit, interacting theories, Yang–Mills — which nothing in
this rung touches.

---

## 10A. Pitch 2 — The free theory at countably many modes (T1) — STANDS WHOLE

The priced build order for the infinite-mode limit that §10 left
open — scoped in `whitepaper/pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md`
and executed in two campaigns (2026-10-16) — landed in full. The
landing removes exactly one scope word from §§9–10: "finite modes"
becomes "countably many modes." Everything else about the labels
is unchanged: **free theory**, states on the **finite-particle
domain**, and the gap in the sense stated below. Five new modules,
137 theorem/lemma declarations and 57 definitions, zero sorrys;
headline axiom checks (nine in Campaign A, eight in Campaign B)
exactly `[propext, Classical.choice, Quot.sound]`.

- **Campaign A — the tower (57 declarations).** `FockLimit.lean`
  builds the shared machine Mathlib lacks: `onbEmb`, a
  linear-isometry constructor from a source Hilbert basis and a
  target orthonormal family, and density of finite-support vectors
  in the constant-ℂ `lp` spaces. `FermionicLimit.lean` and
  `BosonicLimit.lean` build the limit spaces — ℓ² over
  configurations on ℕ (Finset ℕ for fermions, ℕ →₀ ℕ for bosons) —
  with orthonormal configuration bases via `lp.single`, vacua,
  finite-particle domains and sectors; configuration embeddings
  between all finite levels and into the limit, with the cocycle
  proved in the **general** coherence form (all d ≤ e ≤ f, not
  merely successive steps) and the factorization that every limit
  configuration lives at a finite level. (A forced split,
  disclosed: `FermionicFock` and `BosonicFock` cannot share one
  Lean environment — both define `ThetLogos.adag`; the limit
  files inherit the split. The collision is the subject of the
  priced `adag` repair, §14.)
- **Campaign B — the operators and the gap (80 declarations).**
  `FermionicLimitOps.lean` and `BosonicLimitOps.lean`. The corpus
  Γ API is square-only, so a rectangular widening was ported
  (`minorDetRect`/`perMinorRect`, definitionally the square
  kernels) and the identifications proved at operator level:
  `gammaFermRect_pad` (whole-space operator equality, fermions)
  and `gammaBosRect_pad` (equality of domain maps — the honest
  bosonic landing, since bosonic Γ preserves domains, not whole
  spaces). The finite-particle domain of the limit is the union
  of the finite levels (`fermDomLim_eq_iSup_range`;
  `DomLim_eq_iSup_map` in domain-map form — the bare-range form
  is false for bosons, recorded), with density corollaries.
  Diagonal dΓ in the limit for both statistics: basis eigenvalue
  formulas, finite-level compatibility as operator equalities,
  and the number operator as the constant-1 case.
- **The gap, Δ-general (Task 6).** For a diagonal one-particle
  Hamiltonian whose eigenvalues are 0 or ≥ Δ (any Δ > 0), the
  free Hamiltonian in the limit has vacuum eigenvalue 0 and the
  eigenvalue dichotomy: every finite-particle eigenvalue is 0 or
  ≥ Δ (`freeHamiltonianLimFerm_gap_of_orth`,
  `freeHamiltonianLimBos_gap_of_orth`), with self-adjointness on
  the domain. **Mandatory clause, carried in both module headers
  and repeated here verbatim in substance: this is the gap in the
  eigenvalue-on-finite-particle-domain sense of Rungs 9–10; the
  spectral statement (the gap as a statement about the full
  spectrum of the closed operator) is priced, unattempted** —
  the scoping's Task 7, a pre-agreed cut, as is Task 3b
  (rectangular functoriality beyond the padding identifications
  proved).

**What Pitch 2 does not buy** (its dossier's honesty line,
adopted): not interaction — that is Pitch 3 (§10B), which is a
separate construction at finite modes and has no limit-space
form; not continuum or Poincaré (§13A); and not any part of any
Millennium statement.

## 10B. Pitch 3 — Interaction at finite modes — STANDS (fermionic, whole) / STANDS except one priced clause (bosonic)

The corpus's first interacting Hamiltonians. Both campaigns are
finite-mode matter self-interactions — quartic Wick-ordered
density-type terms added to the free Hamiltonians of §§9–10. No
gauge field, no continuum, no Poincaré, and not the interacting
Yang–Mills mass gap: that clause is carried in both module
headers and applies to everything below. Scoping:
`whitepaper/pitch-3-interaction-scoping-DRAFT-2026-10-16.md` (§6
named the landing shape and its failure consequence in advance;
the verdict below applies §6 exactly as written).

- **Campaign 1 — fermionic interaction: STANDS WHOLE.**
  `FermionicInteraction.lean` (1,303 lines; 58 declarations, 15
  definitions; build green, 3,297 jobs; headline axiom checks
  exactly `[propext, Classical.choice, Quot.sound]`). The general
  interacting Hamiltonian `hamInt lam W g = freeHamiltonian +
  g • intOp W` is symmetric for every coupling tensor W, with
  g = 0 recovering the free Hamiltonian; the quartic `intOp W`
  is built on the corpus's first operator-norm bounds for the
  one-mode creators and annihilators, with every matrix
  coefficient and row sum of `intOp W` bounded by
  `intBound W = 2·∑‖W i j k l‖`. **Gap persistence (headline):**
  if `2·|g|·intBound W ≤ Δ/4`, there is a ground eigenvalue E₀
  with `|E₀| ≤ |g|·intBound W`, and every eigenvalue is either in
  the ground cluster or `≥ Δ/2` — the free gap persists at size
  ≥ Δ/2 above the ground cluster, in the eigenvalue sense, at
  finite modes (`hamInt_gap_persistence`). The interaction is
  *proved* interacting: `densityInt_not_dgamma` — the density
  interaction equals `dΓ(M)` for no one-particle matrix M.
  Recorded in the module, per the house pattern: a scoped
  exact-gap statement under the weak dichotomy was **false**
  (two zero modes with U a b > 0 give an eigenvalue
  g·U a b ∈ (0, Δ)); the counterexample is in the theorem's
  doc-comment, the exact gap is proved under the strengthened
  no-zero-mode hypothesis, and the true weaker statements are
  proved instead.
- **Campaign 2 — bosonic interaction: STANDS except essential
  self-adjointness.** `BosonicInteraction.lean` (1,956 lines;
  69 declarations, 21 definitions; targeted build green;
  headline axiom checks exactly
  `[propext, Classical.choice, Quot.sound]`). **B1 (Wick
  calculus):** monomial calculus on the finite-particle domain
  `Dom d` with the √-coefficient basis formula and
  number-relative bounds (`intBoundBos W = 2 · couplingMassBos W`);
  the symmetrized quartic `intOpBos W` is symmetric on `Dom d`
  for every W (`intOpBos_isSymmetric`). **B2
  (self-adjointness, in three scoped senses):** symmetry of
  `hamIntBos lam W g` on the dense domain; sectorwise
  self-adjointness with full diagonalization (on every finite
  particle sector the operator is symmetric with an orthonormal
  eigenbasis and real eigenvalues —
  `hamIntBosSector_spectral`); and LinearPMap formal
  self-adjointness, `hamPMap ≤ hamPMap†`
  (`hamPMap_le_adjoint`). **B3(i) (exact diagonal gap):** under
  the **strong dichotomy** (`∀ i, Δ ≤ lam i` — no zero modes),
  every eigenvalue of the diagonal bosonic Hamiltonian is
  exactly 0 or ≥ Δ, uniformly over all sectors
  (`hamiltonianDensBos_gap_exact`). The weak-dichotomy form is
  **false**, by the same two-zero-mode counterexample shape as
  Campaign 1, recorded in-doc; only its dominated form is
  proved. **B3(ii) (windowed persistence):** for an eigenvector
  in sector n, under the threshold
  `2 · (‖g‖ · intBoundBos W · (n+2)²) ≤ Δ/4`, the eigenvalue is
  within `‖g‖ · intBoundBos W · (n+2)²` of 0 or ≥ Δ/2 — the
  window is in the statement (`hamIntBos_gap_persistence_windowed`).
  The density interaction is again proved not to be a dΓ lift
  (`densityIntBos_not_dgamma`) — for both statistics now.
- **Disproved in-module (a result, recorded as one).** Uniform
  gap persistence for general bosonic quartic coupling is
  **false**: `densHamEigBos_unbounded_below` — attractive pair
  coupling (U a b = −1, g = 1) gives the eigenvalue
  (lam a + lam b)·n − n² at the (n, n) configuration, below
  every bound for large n. This proved collapse is the reason
  B3(ii) is windowed; it is also entered in the kill ledger (§15).
- **The one open clause — essential self-adjointness: PRICED.**
  What is not proved is the closure equality
  `hamPMap = hamPMap†` as partial linear maps. The obstruction,
  with one correction to the campaign dossier's account: the
  dossier stated that Mathlib has no LinearPMap closure
  operator; the parked-fleet gauntlet's audit (2026-10-17)
  found that stale — pinned Mathlib *does* define
  `LinearPMap.closure` (`Mathlib/Topology/Algebra/Module/LinearPMap.lean`),
  with `le_closure` and `IsClosable.closure_isClosed`, so the
  target is statable sharply as `hamPMap.closure = hamPMap†`.
  What remains absent is the analytic input: no Kato–Rellich
  theorem and no Nelson commutator theorem in the pinned
  Mathlib, and the closure's domain is an ℓ²-growth condition
  across infinitely many sectors. Two proof routes are named:
  R1, a Faris–Lavine/Nelson commutator argument with comparison
  operator (N+1)²; R2 (**recommended**), banded truncation —
  the quartic moves sectors by Δn ∈ {−4,−2,0,2,4} only, so
  the core property reduces to one ℓ² tail estimate.
  Re-priced **M–L** (restating the target: S).

> **Pitch 3 verdict** (the scoping §6's pre-named PARTIAL,
> narrowed to a single clause): Pitch 3 **stands for fermionic
> interaction whole**. For bosonic interaction, the Wick
> calculus with relative bounds, the exact diagonal gap,
> windowed persistence, sectorwise self-adjointness, and
> LinearPMap formal self-adjointness all stand; **essential
> self-adjointness is priced**. The §6 headline sentence
> ("…both statistics, with self-adjointness proved…") is
> **not** spendable in unqualified form, and no text in this
> paper spends it.

Route C of the scoping (interaction in the limit spaces of
§10A) stays FRONTIER and is not attempted.

## 10C. Schrödinger dynamics — the evolution exhibit (T1) — STANDS

`SchrodingerDynamics.lean` (868 lines; 49 declarations, 10
definitions; build green, 3,319 jobs; ten headline axiom checks
exactly `[propext, Classical.choice, Quot.sound]`). Finite
dimensions only; the module takes no interpretation position
(interpretations are T5), and whole-Fock-space/bosonic dynamics
is FRONTIER and absent from it.

For any symmetric operator T on a finite-dimensional complex
inner-product space, `evolOp hT t` is constructed diagonally —
spectral phases in Mathlib's `eigenvectorBasis`. Proved: the
group law (`evolOp_add`, with the inverse identities) and
`evolOp_zero`; unitarity (`evolOp_isometry`; the linear isometry
equivalence `evolUnitary` with inverse `evolOp (−t)`;
`evolOp_adjoint`); the explicit solution formula
(`evolOp_solution_formula`: coefficients evolve by eigenphases);
**the Schrödinger equation as a derivative theorem**
(`hasDerivAt_evolOp_apply`: dψ/dt = −i • Tψ) with **uniqueness**
(`evolOp_unique`, by a coordinatewise integrating factor — no
ODE library needed); eigenspace invariance. The Heisenberg side
is built with its group law and algebra-automorphism package,
and the Heisenberg equation (dA/dt = i[H, A] in the corpus's
sign conventions). **Picture equivalence is a theorem**
(`picture_equiv`): expectation values agree between the
Schrödinger and Heisenberg pictures. **Headline application:**
under the exact hypotheses of §10B's `hamInt_gap_persistence`,
the ground cluster and the high (≥ Δ/2) cluster of the
interacting fermionic Hamiltonian are subspaces, each invariant
under the time evolution, covering the space with the ground
cluster nontrivial (`groundCluster_invariant`,
`highCluster_invariant`, `hamInt_clusters_cover_and_nontrivial`)
— the gap persists not only under coupling but in time.

Two fenced shortfalls, named and priced: `evolOp` is
*characterized* as the exponential by the Schrödinger equation
plus uniqueness, but a literal identification
`evolOp = NormedSpace.exp (−it•T̂)` was **not** proved (priced
**S**); and the Dyson first-order term (interaction-picture,
needs interval integrals of the Heisenberg-evolved interaction)
was **not** landed (priced **S–M**).

---

## 11. SM-Match — structural match against the Standard Model (3 MATCH + 1 PARTIAL)

"Match" means: the formalized structures coincide with the Standard
Model's known algebraic structure — same gauge group, same fermion
quantum numbers, same classical Lagrangian shape, same breaking pattern.
Masses, couplings, and mixing angles are **inputs** (labeled T2), never
derived. This is a structural formalization result, not a new Standard
Model and not a derivation of any measured value. 95 theorem/lemma
declarations across four files (the program dossier's earlier estimate of
"~70" understated the count; the verified figure is 95).

- **Track 1 — Full finite gauge algebra: PARTIAL.** On the algebraic side,
  the match is proved T1: the unitary group of ℂ⊕ℍ⊕M₃(ℂ) is
  U(1)×SU(2)×U(3) (`quat_mem_specialUnitary_iff`: U(ℍ) = SU(2)), and its
  unimodular subgroup is exactly U(1)×SU(2)×SU(3)
  (`SMUnimodular_mem_iff`). On the represented side, the Rung 2 caveat is
  located exactly, not redefined: the kernel of the Option-A
  representation is characterized (`pi_ker_iff`); ℂ and ℍ survive
  faithfully; M₃(ℂ) survives only locked to the electroweak sector; pure
  color dies. And the priced gap is proved, not asserted:
  `pi_u1_eL_trivial` — the represented U(1) acts trivially on the left
  electron, so **the represented U(1) is not the Standard Model
  hypercharge U(1)**. A faithful representation of the full SM gauge
  group on the finite Hilbert space is not achieved; the gap is priced at
  the pre-Option-A representation or the manifold factor.
- **Track 2 — Fermion content: MATCH.** The eight fermion types carry the
  Standard Model's (Y, T³, color) assignments as labeled T2 inputs
  (hypercharges are not derived; generation triplication is imposed, per
  `ThreeGen.lean`). Proved T1: electric-charge consistency
  Q = T³ + Y/2 for all eight types (`charge_consistency`), and
  consistency of the index↔fermion mapping with the finite-triple
  embedding. Priced: full SU(3) color is unrepresented in the Option-A
  representation (Track 1's gap).
- **Track 3 — Classical Lagrangian sectors: MATCH.** 19 declarations:
  three-factor gauge kinetic term with joint gauge invariance proved
  (`smGaugeKinetic_gauge_invariant`), the correct −¼ sign, and
  nonnegativity; the fermion term's fluctuation split
  (`fermionTerm_split`); the Higgs potential's minima structure (pure
  algebra); the Yukawa sector *structure* with an input matrix and no
  values. Priced: the quantum Lagrangian, the continuum integral, the
  junk quotient, and all coupling values.
- **Track 4 — Symmetry breaking: MATCH.** 42 declarations. The VEV
  stabilizer is *exactly* span(Q) (`higgs_stabilizer_is_Q`) — the precise
  algebraic statement of SU(2)_L×U(1)_Y → U(1)_em; the VEV minimizes the
  potential; the photon direction is massless *because* Q is unbroken
  (`higgs_photon_direction_massless`); M_W = gv/2 and
  M_Z = √(g²+g′²)v/2 hold as formal relations among the input parameters
  (g, g′, v), with no numerical values anywhere.

## 12. Theories intake, Round 1 — fit verdicts

Standing rule: a theory is admitted only if its core structures map onto
the program's formalized objects with real theorems. Refusals are results.

- **KMS / Tomita–Takesaki: FIT at finite level.** 10 T1 theorems in
  `KMSBridge.lean`, including the finite-dimensional KMS identity for
  Gibbs states (`gibbs_kms_weight`) and the equivalence of KMS
  equilibrium with vanishing thermal flux; two previously pinned T5
  targets in the modular-flux file are discharged. Priced T5 window:
  unbounded Tomita–Takesaki theory and type-III factors — Mathlib has no
  von Neumann algebra theory.
- **Classical Yang–Mills: FIT classically; quantum NO-FIT.** 16 T1
  theorems in `ClassicalYangMills.lean`, including the represented
  curvature from 1-form data with *exact* gauge covariance
  (`repCurvature_gauge_covariant`) and gauge invariance of the
  Tr(F†F) action. The quantum theory — quantization, continuum, mass
  gap — is recorded NO-FIT and remains quarantined T5.
- **AQFT / Haag–Kastler: per-axiom.** In `HaagKastlerFree.lean` (14
  declarations): isotony FIT (T1); locality FIT at creator level and for
  fermionic even observables (T1), with the honest caveat that the
  spacelike hypothesis is vacuous at creator level; Poincaré covariance
  PARTIAL (geometric half T1, implementer priced); vacuum PARTIAL (cyclic
  vector T1, invariance priced); spectrum condition and irreducibility
  NO-FIT as theorems in the current setting (priced windows recorded).
- **Spectral action / finite index bridge: FIT at finite level (2026-10-11
  verification); build failure found and repaired 2026-10-15 — see the
  correction below.**
  On the formalized `smDirac`: Tr(1) = 32; Tr(D_F²) as the explicit
  Yukawa-sum formula; the fluctuated trace expansion; vanishing of odd
  traces; the finite-dimensional Fredholm index and the chiral-compression
  index (zero). NO-FIT recorded: the continuum heat-kernel expansion and
  the Atiyah–Singer theorem (both need continuum elliptic analysis).
  **Correction (2026-10-15):** re-verification for this paper found that
  `SpectralActionFinite.lean` no longer compiles under the pinned
  toolchain — four proof failures (`simp` made no progress / failed
  rewrite at lines 942, 1006, 1024, 1074), all inside the a₂
  trace-computation proofs and consistent with Mathlib deprecation drift
  (`if_pos`/`if_neg` simp behavior). `SpectralActionBridge.lean` fails
  transitively. The theorem *statements* are unchanged and no `sorry` was
  introduced, but until the proofs are repaired this entry's T1 status is
  **not currently machine-verified** and the FIT verdict is suspended,
  not standing. Repair is a queued, well-localized job.
  **Resolution (2026-10-15):** the repair was completed the same day —
  proof-local fixes only (re-applying the diagonal multiplication
  reduction inside the affected trace computations); no statement
  changed; no `sorry`/`admit`/axiom added; the file builds green again
  and **the FIT verdict stands restored** (theories-intake dossier
  amended; repair commit `6b4e2f9`).

**Round 2 queue (not yet run):** BRST/anomalies; the
Osterwalder–Schrader reconstruction bridge; noncommutative integration /
Dixmier trace.

**Note (2026-10-17).** Round 2 has still not been run as an
intake. Its Osterwalder–Schrader item has meanwhile split (per the
parked-fleet gauntlet's ruling): the *fit-audit* half is killed as
redundant — Pitch 4's Stage 1b (§13A) is now the program's OS
work, done as construction rather than audit — while the
*re-pinning* half stands: the corpus's `OsterwalderSchrader.lean`
header premise ("Mathlib has no tempered distributions") is stale
(pinned Mathlib has 𝓢′ and the Fourier transform; the true
absences are the smearing map, the full field φ(f), and OS
verification), and the reconstruction dependency audit remains
priced S–M. BRST stands priced M; the Dixmier trace item stands
priced S–M.

## 13. The Morley edge-signature gauntlet — PROMISING, with one precise kill

Hypothesis (Jeff): a 4D boundary carrying two 2D edge operators generates
the 3+1 split, with the torsion/twist in the D_F projection carried, not
assumed away. Steelmanned, then formalized in `EdgeSignature.lean`
(30 theorem/lemma declarations; the gauntlet dossier groups the core
results into four sections). Build status: verified green by the gauntlet
on 2026-10-11; the 2026-10-15 group rebuild timed out without errors,
and the file was **re-verified later on 2026-10-15 by a standalone build
(exit 0; zero `sorry`/`admit`; axiom checks on the 13 headline theorems
clean)** — see §0. The verdicts below stand as the record.

- **Morley core — T1.** Edge-pair ⟺ fundamental symmetry: from η² = 1,
  the operators E± = (1±η)/2 are idempotent, orthogonal, and
  complementary (`edgePair_of_symm`); conversely a perfect pair gives
  η = E₊ − E₋ with η² = 1 (`symm_of_edgePair`). The "arbitrary input →
  perfect structure" pattern has real formal content: perfection is
  forced by η² = 1 alone.
- **Flip twist carried — T1.** The doubled edge decomposition is
  flip-invariant for (η, η): the Rung 2 twist preserves the perfection.
- **Torsion carried exactly — T1.** (η+T)² = 1 + (ηT + Tη + T²)
  (`torsion_defect`); fluctuated edge operators miss idempotence by
  exactly (2⁻¹)² • (ηT + Tη + T²) (`edgePlus_torsion_defect`);
  perfection survives torsion iff ηT + Tη + T² = 0, a Maurer–Cartan-type
  flatness condition (`torsion_flat_iff`). (The earlier ℂ⁷-torsion claim
  remains killed and is not resurrected.)
- **Strong emergence — KILL, by T1 counterexample.**
  `signature_not_determined`: (1,1) and (1,−1) on ℂ×ℂ both square to 1,
  but one has vanishing minus-edge (signature (2,0)) and the other does
  not (signature (1,1)). η² = 1 does not determine the signature; the
  3+1 numbers are extra data. The kill is itself a theorem.
- **Analogy assessment:** real formal content at the algebraic level; the
  "miracle" grading (maximal symmetry from no symmetry) remains
  philosophy, labeled NEEDS-WORK as an analogy.

Priced next steps: a D_F-specific torsion map (η built from Dirac data,
defect computed under inner fluctuations); the dimensional reading —
"two 2D" suggests neutral signature (2,2), and what breaks it to (3,1)
is open; integration with the twisted first-order condition; a boundary
spectral triple as the formal home of the "4D boundary."

## 13A. Pitch 4 — The continuum passage, opened on the lattice — Stages 0, 1a, 1b stand as stated; NO CLAIM on the pitch

Pitch 4 is the program's scoped route from its finite
constructions toward the continuum Yang–Mills theory. Its scoping
(`whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md`) is
chartered **NO CLAIM**: before every stage below, and after all of
them, **parts of the official Clay statement closed: 0**. The
scoping's decisions, stated once here: the route is **lattice
first** — the analytic route (continuum fields via Minlos-type
measure constructions) is priced XL with no landing, blocked at
its first move by the absence of nuclear spaces and a Minlos
theorem from the pinned Mathlib. The stage map: Stage 0, finite
lattice gauge theory; Stage 1a, correlations; Stage 1b,
reflection positivity and its consequences; Stage 1c,
strong-coupling clustering (priced XL, separately killable);
Stage 2, one exact coarse-graining step (M–L; the iterated flow
with estimates is XL, Balaban-scale); Stages 3a/3b, OS-reconstruction
scaffolding (M / M–L); Stage 3c, uniform estimates along a
continuum trajectory — **priced research-scale and open in
print**, with one audit rule the scoping states plainly:
deriving the continuum gap from a gap assumed uniform along the
trajectory is circular as an audit instrument and is forbidden
in this program's writing; Stage 4, an interacting Poincaré
representation in the continuum — FRONTIER. Two traps are named
in advance: Elitzur's theorem (gauge-variant quantities cannot
carry expectations — met, and discharged, at Stage 1a) and
triviality (the φ⁴₄ precedent: a lattice route can end in a
free continuum theory; nothing below speaks to that question).

All stages below are finite-lattice T1. The lattice is not the
continuum, no limit of any kind is taken or claimed in any of
them, and none of them is a step *in* a Clay proof — they are
the first priced bricks of the road the scoping draws.

- **Stage 0 — finite lattice gauge theory: STANDS WHOLE.**
  `LatticeGauge.lean` (1,656 lines; 68 declarations by the §0
  strict method — 72 counting its four `@[simp]` loop lemmas,
  which the strict rule excludes;
  33 definitions and instances; build green, 3,390 jobs).
  Sites form an abstract finite type Λ with four shift
  bijections, concretely the torus `Fin 4 → ZMod N`; links are
  group-valued, `U : Link Λ → G` for a general compact group G;
  the plaquette and Wilson action are built from a general
  unitary representation ρ. Proved: **exact gauge invariance
  of the Wilson action for every gauge transformation** — no
  gauge fixing anywhere — with invariance of the product-Haar
  configuration measure in the strong form
  (`Measure.map (gaugeAction σ g) (configMeasure μG) =
  configMeasure μG`); Wilson loops gauge-invariant; the
  normalized Haar probability `haarProb` built in-file from
  Mathlib's Haar measure, its right- and inversion-invariance
  proved from uniqueness. The **β = 0 package at general
  (G, ρ)**: at zero coupling the Gibbs expectation is the
  product-Haar expectation, the single-plaquette expectation
  factorizes through the Haar intertwiner P, and
  `gibbsExpect_zero_plaquette : ⟨W_p⟩₀ = tr P` — which
  vanishes exactly when ρ has no nonzero fixed vectors
  (`gibbsExpect_zero_plaquette_eq_zero`), with the circle and
  full-unitary instances discharged on the torus. Action
  nonnegativity for β ≥ 0.
- **Stage 1a — correlations and Elitzur: STANDS WHOLE**
  (pitch-level shape after this stage: PARTIAL-β).
  `LatticeCorrelations.lean` (1,667 lines; 68 declarations, 13
  definitions; build green, 3,391 jobs; the five scoped
  headline axiom checks exactly
  `[propext, Classical.choice, Quot.sound]`). The Gibbs
  measure is constructed as an actual probability measure at
  **every real β** (`gibbsMeasure`, with
  `isProbabilityMeasure_gibbsMeasure`), and Stage 0's
  ratio-of-integrals expectation is proved equal to its
  integral (`gibbsExpect_eq_integral`) — the measure Stages
  1b–1c consume. The expectation algebra (constants,
  additivity, scaling, finite sums, |⟨F⟩| ≤ ⟨|F|⟩, the real
  form with monotonicity) and the covariance package:
  symmetry, the centered form, **variance nonnegativity**
  (`gibbsVar_nonneg`), and **Cauchy–Schwarz**
  (`gibbsCov_sq_le`, by the elementary discriminant argument).
  **Elitzur's theorem at general (G, ρ), for every β**
  (headline): the mechanism theorem
  `expectMatrix_eq_zero_of_left_covariant` — the expectation
  matrix of any left-covariant insertion is zero whenever ρ
  has no nonzero fixed vectors — with corollaries
  `elitzur_single_link` and `elitzur_open_wilson_line` and
  the torus instances. The pre-authorized narrowing to
  instance-level Elitzur was **not** needed. The contrast is
  proved, not gestured: plaquette expectation matrices are
  intertwiners, not vanishing subjects
  (`expectMatrix_plaquette_intertwines`). β = 0 factorization
  for disjointly supported observables landed **stronger
  than scoped** — the identities carry no integrability
  hypotheses at all — and is fenced to β = 0 in the module, its
  dossier, and here. The Wilson two-point function is defined
  as an object, with the bound |⟨W₁W₂⟩| ≤ d² and the
  connected function defined; **no decay or clustering claim
  is made at any β** (that is Stage 1c, untouched).
- **Stage 1b-A — reflection structure: STANDS WHOLE.**
  `LatticeReflection.lean` (1,335 lines; 67 declarations, 16
  definitions; build green, 3,392 jobs). The abstract-Λ
  presentation of Stages 0–1a provably carries no reflection
  (a grep-verified obstruction recorded by the gauntlet), so
  the reflection is built on the concrete torus: the
  **between-sites** reflection in direction 0,
  `reflSite x = update x 0 (-1 - x 0)` — an involution with
  the shift calculus θσ₀θ = σ₀⁻¹, θσᵢ = σᵢθ (i ≠ 0), and
  **no fixed sites at even N**. The fixed link stratum is
  **characterized by an if-and-only-if**
  (`reflLink_eq_self_iff`): the fixed links are exactly the
  time links based in the two layers adjacent to the two
  reflection planes — not enumerated, characterized; the
  pre-named enumeration-only PARTIAL shape was not triggered.
  The configuration reflection factors as θ = invConfig ∘
  permConfig, and **both the product-Haar measure and the
  Gibbs measure are reflection-invariant at every real β**,
  in the strong `Measure.map` form
  (`gibbsMeasure_map_reflConfig`) — stronger than the
  pre-named Haar-level fallback. **The Wilson action split is
  proved term by term**: S = S₊ + S₋ + S₀, with
  S₊(θU) = S₋(U), S₋(θU) = S₊(U), and S₀ — the crossing class
  of temporal plaquettes over the two fixed layers —
  θ-invariant term by term.
- **Stage 1b-B — reflection positivity: PARTIAL (the
  pre-named shape γ, extended).** `LatticePositivity.lean`
  (1,559 lines; 44 declarations, 10 definitions; build
  green, 3,393 jobs). The observable class is the **strict
  positive half** `posLinks = halfLinks \ planeLinks`; the
  exclusion of the reflection-fixed plane links is forced —
  two finite counterexamples are recorded in the stage
  dossier (hand computations, not Lean theorems): a
  plane-link observable over G = ℤ/3 at β = 0 gives the form
  value −2, and at fixed stratum variables a U(1) character
  gives I₁(β)e^{iγ}, not even real. What stands, at general
  (G, ρ) and **every real β**: the OS form `osForm` (θ on
  observables = conjugation ∘ the observable ∘ the
  configuration reflection), its **conjugate symmetry**
  (`osForm_conj_symm`, via 1b-A's Gibbs reflection
  invariance), reality of the diagonal, full sesquilinearity,
  the bridge to the bare-pullback reading of ⟨θ(F)·F̄⟩
  (`osForm_bare_eq`), and the **kernel identity**
  (`osForm_eq_kernel`): the form is Z⁻¹ times a double
  integral over the two halves, with the crossing action in
  the kernel. **Positivity is proved at β = 0**
  (`osForm_zero_nonneg`: the weight is 1, the kernel factors,
  and the diagonal is W·W̄). The **Gram criterion is proved,
  β-sign-free** (`osForm_nonneg_of_gram`): *if* the Gibbs
  weight in split variables is a finite Gram sum
  ∑ᵢ conj(Ξᵢ∘mirror)·Ξᵢ∘restrict with bounded measurable
  features, *then* the diagonal is
  Z⁻¹·∑ᵢ‖∫f·Ξᵢ‖² ≥ 0. Positivity at general β is thereby
  reduced, losslessly, to **one named open clause**: the
  Gram (character-expansion) factorization of the Wilson
  weight. Its standard proof needs Schur/Peter–Weyl
  orthogonality of matrix coefficients on a general compact
  group, which the pinned Mathlib (v4.35.0-rc3) does not
  contain — its representation theory covers finite groups
  and the algebraic theory. **Price: XL, blocked on Mathlib
  infrastructure.** The positivity theorem itself is
  classical (Osterwalder–Schrader; Glimm–Jaffe); it is
  unproved here, **not** killed.
- **Stage 1b-C — the OS Hilbert space: STANDS.**
  `LatticeOSSpace.lean` (1,065 lines; 42 declarations, 17
  definitions; build green, 3,550 jobs; eleven headline axiom
  checks exactly `[propext, Classical.choice, Quot.sound]`).
  Built by the **time-slice L² route** (the gauntlet's ruling;
  the quotient/completion-of-the-form route was declined):
  `osSpace μG ρ β := Lp ℂ 2 (sliceMeasure μG ρ β)`, where the
  slice measure is the Gibbs marginal on the time-0 slice —
  a probability measure at **every real β**, and at β = 0
  exactly the product Haar measure over the slice. The space
  is a Hilbert space by Mathlib's Lp instances — positive by
  construction, with **no appeal to OS positivity**. The
  **vacuum** is the constant function 1, of norm 1
  (`norm_osVacuum`); vacuum expectation equals the Gibbs
  expectation of the pulled-back observable
  (`vacuum_expectation`). Bounded slice observables act as
  multiplication operators (`sliceMul`), operator norm ≤ the
  bound, with **adjoint = pointwise conjugation** and
  real-valued ⇒ self-adjoint. What routes through 1b-B's
  open clause is stated **conditionally on it, by name**:
  the clause is packaged as `GramClause`, and
  `osForm_nonneg_of_gramClause` /
  `osForm_slice_nonneg_of_gramClause` assume it as an
  explicit hypothesis; positivity at β = 0 for slice
  observables is unconditional (`osForm_slice_zero`). One
  marginal identity (the pushforward of product Haar along
  the slice inclusion) is named, unproved, priced **S**, and
  **not used**.
- **Stage 1b-D — the transfer matrix: STANDS.**
  `LatticeTransfer.lean` (1,610 lines; 58 declarations, 13
  definitions; build green, 3,551 jobs; eleven headline
  axiom checks exactly `[propext, Classical.choice,
  Quot.sound]`). The transfer operator is the adjoint
  compression `T_β = A*† ∘L B*` on the OS space, where A*
  (`slicePull`) pulls a slice observable back along the
  time-0 restriction and B* (`nextPull`) does the same
  along the time-1 restriction transported to the time-0
  slice; both legs are linear isometries into the same
  L² of the Gibbs measure, and both slice marginals are
  proved equal to the slice measure at every real β
  (translation invariance of the Gibbs measure, proved in
  the module in `Measure.map` form, by 1b-A's reflection
  argument run for translations). The operator package, at
  **every real β**: the **form identity**
  (`transferOp_inner`: ⟪g, T_β f⟫ is the two-slice Gibbs
  kernel pairing, as an identity); **contraction**
  (`transferOp_norm_le`: ‖T_β‖ ≤ 1, by Cauchy–Schwarz
  against the two isometries); **vacuum fixed**
  (`transferOp_vacuum`: T_β Ω = Ω); **self-adjointness**
  (`transferOp_adjoint`, `transferOp_isSelfAdjoint`, at
  even N — from 1b-A's *proved* reflection invariance via
  the reflection step Ψ = (time shift by −2) ∘ θ, which
  exchanges the two slices; **no clause spent**); and **form
  positivity** (`transferOp_form_nonneg`: for pointwise real
  nonnegative slice observables, ⟪g, T_β f⟫ is real and
  nonnegative — proved from the positivity of the Gibbs
  measure alone, again with no appeal to OS-form positivity
  or the Gram clause). **The lattice gap at β = 0 is exact:**
  the kernel pairing factorizes over the disjoint slices
  (Stage 1a's β = 0 factorization), giving
  `transferOp_zero_apply : T₀ f = ⟪Ω, f⟫ • Ω` — **T₀ is
  exactly the orthogonal projection onto the vacuum line**,
  idempotent (`transferOp_zero_comp_self`), killing the
  vacuum-orthogonal complement; its spectrum is {1} on the
  vacuum line and {0} on the complement, so **the gap of
  T₀ is exactly 1**. That is the free (infinite-temperature)
  point; it is exact, and it is all the gap this stage
  claims.

**Pitch-level shape after Stage 1b.** Stages 0 and 1a stand
whole; Stage 1b stands in A (structure), C (the space), and D
(the operator package with the exact β = 0 gap), and in B it
stands in the form, at β = 0, and as the proved Gram
criterion, with general-β positivity the stage's single open
clause. **PARTIAL-δ** — the scoping shape that would let this
paper say "reflection positivity stands" for Stage 1b — is
**NOT claimed**, and will not be claimable until 1b-B's clause
closes. Stages 1c, 2, 3a/3b, 3c, and 4 are unbuilt and priced
(§14). Nothing in this section takes a thermodynamic or
continuum limit, constructs an interacting Poincaré
representation, or closes any part of the Clay statement.

## 14. Frontier and priced windows

The following are named, framed, and priced — not claimed.

1. **Unbounded operator theory in Mathlib.** Densely defined closed
   operators, the unbounded adjoint, von Neumann's A** theorem, the
   Cayley transform, projection-valued measures, the unbounded spectral
   theorem, and Borel functional calculus are absent from Mathlib
   (surveyed 2026-10-11; five checkable window statements are filed in
   `SpectralFrontier.lean`). This is the boundary of formalized analysis
   on the spectral prong.
2. **Second quantization (bosonic) — discharged in Version 2.** The
   adjoint-relation assembly is discharged (§8B), and Γ(U)
   functoriality is discharged (§10, Task 3, closed by the Γ functor
   campaign of 2026-10-16): `Γ(1) = 1`, the diagonal action,
   multiplicativity, and unitarity are proved at finite modes. The
   **infinite-mode limit is now also discharged** (Version 3): the
   direct-limit Fock construction exists and the free theory stands
   at countably many modes (§10A, Pitch 2). What remains priced on
   this line: the **spectral** form of the free gap at countable
   modes (the eigenvalue-on-finite-particle-domain form is proved;
   Task 7 of the Pitch 2 scoping), rectangular functoriality
   beyond the padding identifications (Task 3b), interaction in
   the limit spaces (§10B's Route C: FRONTIER), and the symmetric
   tensor-power unitary equivalence (blocked upstream, as priced
   at §8).
3. **Boost invariance** of the mass-shell measure — **DISCHARGED in
   Version 3** (§7 amendment): the one-dimensional Jacobian identity
   is proved and, with the factorization cap, the measure is
   invariant under the full restricted Lorentz group.
4. **Strong continuity** of the one-particle representation: a dominated
   convergence argument with the dominating function identified.
   Repriced by the parked-fleet gauntlet: the translation part is
   **S, discharge-ready** (the dominating function 4‖ψ‖² and the
   dominated-convergence lemma are named in the source file); the
   Lorentz part is **S–M** (§7 amendment's discharge supplies the
   Jacobian domination). **Fock packaging** (the one-particle
   representation assembled on the Fock spaces of §§8–10A) is
   priced **M** by the concrete orthonormal-basis route; the
   abstract route stays killed (§15).
5. **n-point Wick expansion:** the Wick recursion at 2n points.
6. **Faithful SM gauge representation** (§11, Track 1): priced at the
   pre-Option-A representation or the manifold factor.
7. **Continuum limit and interacting 4D QFT.** No construction exists in
   this corpus. The Wightman verdicts of Rung 5 are toy-model verdicts;
   the general theory is not formalized.
8. **Yang–Mills existence and mass gap.** Quarantined T5. The Clay
   statement is formalized as a fixed target (`ClayStatement.lean`), and
   the dossier discipline records why finite-level gaps do not transfer:
   Osterwalder–Seiler's strong-coupling lattice gap excludes the
   continuum limit; Balaban's renormalization-group work is not a
   mass-gap proof; φ⁴₄ triviality says nothing directly about Yang–Mills;
   spectral-gap undecidability results concern families of Hamiltonians,
   not the single Yang–Mills Hamiltonian.
9. **Bosonic essential self-adjointness** (§10B): the closure equality
   `hamPMap.closure = hamPMap†`, statable since the parked-fleet
   gauntlet found `LinearPMap.closure` in the pinned Mathlib. Priced
   **M–L** (restating the target, S; the domain argument, M–L), by the
   banded-truncation route (R2) or the Nelson-commutator route (R1).
   This is Pitch 3's sole remaining priced item.
10. **The `adag` repair and Yukawa.** The fermionic and bosonic Fock
    modules cannot be co-imported (both define `ThetLogos.adag`, with
    `ann`, `adag_basis`, `ann_basis` — the collision set is exactly
    those four names): a mixed fermion–boson (Yukawa) term cannot yet
    even be *stated* in one environment. The repair (rename the
    bosonic side, 82 use sites in 4 files, plus a co-import smoke
    module as the deliverable) is priced **S–M**; the Yukawa campaign
    on top of it is priced **M–L** (its walls fenced in advance:
    essential self-adjointness verbatim from item 9, and uniform
    persistence *false* by §10B's collapse counterexample).
11. **Reflection positivity at general β** (§13A, Stage 1b-B): the
    Gram/character-expansion factorization of the Wilson weight.
    Priced **XL, Mathlib-blocked** (needs Peter–Weyl orthogonality for
    general compact groups). Until it closes, PARTIAL-δ stays
    unclaimed.
12. **The lattice gap at general β** (§13A, Stage 1b-D): spectral
    input on the transfer operator at fixed β > 0 (classically,
    compactness of the continuous-kernel operator and its spectrum).
    Priced **M–L**. A gap uniform in volume and coupling along a
    continuum trajectory is item 13's Stage 3c, not this.
13. **Pitch 4's unbuilt stages** (§13A): Stage 1c-0, a finite-order
    strong-coupling exhibit (M; its first-order plaquette coefficient
    in closed intertwiner form is a perimeter law at first order —
    any reading of it as area-law evidence is killed in advance);
    Stage 1c proper, uniform clustering (XL, killable — any
    clustering statement routing through gauge-variant intermediates
    is dead on arrival by §13A's Elitzur theorem); Stage 2, one exact
    blocking step (M–L; iterated flow XL, Balaban-scale); Stages
    3a/3b, OS scaffolding (M / M–L); Stage 3c, uniform estimates along
    the continuum trajectory (research-scale, open in print); Stage
    4, interacting Poincaré (FRONTIER).
14. **Schrödinger smalls** (§10C): the literal `NormedSpace.exp`
    identification of `evolOp` (S), and the Dyson first-order term
    (S–M: define and FTC-characterize, S; full Duhamel with remainder,
    M).
15. **Bridge follow-ons** (Appendix A): attainment of the Fiedler
    infimum (S), exponential decay at the Fiedler rate (M), and the
    Faraday storey (S–M; graph and lattice objects differ in kind —
    the lattice work of §13A does not cheapen it).
16. **Decoherence toy.** No partial trace exists in the corpus or the
    pinned Mathlib (grep-verified); a finite-dimensional toy built on
    a hand-rolled partial trace is priced **S–M** and is the
    program's cheapest fully standalone landing.

## 15. Kill ledger (selected)

Killed claims return only as new entries by proof; the originals stand.

- As-stated Connes–Kreimer antipode axiom — refuted; corrected version
  proved (different claim).
- ρ_M ⊗ ρ_F as product twist — does not typecheck.
- Strong Morley emergence (edge data determine 3+1) — T1 counterexample.
- p/n as a fundamental gauge-coupled ± pair; electron as an interaction
  product of that sector — killed by standard physics (isospin is an
  approximate global symmetry; lepton number, spin, and statistics all
  fail for the composite-electron reading). The honest survivors:
  approximate global isospin, the electron as a separate lepton field,
  beta decay as weak charged current.
- W5 monomial-range cyclicity as framed — false; span version proved.
- Bosonic-form W6 criterion for fermions — fermion-blind; Koszul version
  proved.
- "Finite triple converges" (continuum language) — killed; priced roadmap
  instead.
- The φ-tower (golden-ratio mass hierarchy) — killed against measured
  mass ratios.
- ℂ⁷ torsion — killed; not resurrected by the Morley gauntlet.
- Uniform bosonic gap persistence for general quartic coupling —
  **disproved in-module** (§10B): attractive coupling gives eigenvalues
  (lam a + lam b)·n − n², unbounded below. The windowed statement is
  the true one and is proved.
- The weak-dichotomy exact-gap forms of both Pitch 3 campaigns — false
  by the two-zero-mode counterexample recorded in both modules; the
  strengthened (no-zero-mode) statements are proved as different
  claims.
- Positivity of the Osterwalder–Schrader form over observables
  supported on the reflection-fixed plane links — false (Stage 1b-B
  dossier's counterexamples: form value −2 at β = 0 over ℤ/3; a
  U(1) character value I₁(β)e^{iγ}, not real, at fixed stratum
  variables). The strict-positive-half class is the true one.
- The abstract SymmetricAlgebra route to Fock packaging — killed
  (again, and permanently, in the 2026-10-17 gauntlet); the concrete
  orthonormal-basis port is the only route (§14, item 4).
- A separate Osterwalder–Schrader *fit-audit* intake (the Round 2
  item) — killed as redundant: absorbed by Pitch 4's construction
  (§12 note). Its re-pinning half survives as a priced item, not as
  an audit.

## 16. What is NOT claimed (the immune system)

- **No 4D QFT.** The finite triple is zero-dimensional; the Wightman
  verdicts are one-mode toy verdicts; no interacting theory *in four
  dimensions, or in any continuum*, is constructed. (Interacting
  Hamiltonians at finite modes are constructed — §10B; the fence is
  stated at "No interacting continuum theory" below.)
- **No continuum limit.** The continuum is a priced roadmap throughout.
- **No mass gap.** The Clay target is fixed and quarantined; nothing here
  is a step in a Clay proof, only infrastructure such a proof would need.
  Parts of the official Clay Yang–Mills statement closed by this
  corpus: **0** — before and after every result in this paper.
- **No full SM gauge group from the finite representation.** The
  represented U(1) is provably not hypercharge (§11). The algebraic
  match holds at the level of the full finite algebra and its unimodular
  subgroup.
- **No derived masses, couplings, or mixing angles.** All are labeled
  inputs wherever they appear.
- **No physical predictions.** Spectral, thermal, and trace numbers in
  this corpus are properties of the mathematical models, not measurements
  of nature.
- **No derivation from analysis where axiomatization was used.** Rung 3's
  promotions and Rung 4's bridge axiom are labeled T2 at every citation.
- **The free-theory gaps are not the mass gap.** The derived gaps of §9
  (Task 3), §10 (Task 2), and §10A (Pitch 2, at countably many modes)
  are statements about free Hamiltonians, with the one-particle gap Δ
  as an input; the persistence result of §10B is a statement about a
  finite-mode interacting Hamiltonian under its threshold; and the
  lattice gap of §13A is a statement about a finite-lattice transfer
  matrix at β = 0. None of them is the Yang–Mills mass gap, and none
  transfers to any interacting or continuum theory (§14, item 8).
- **No interacting continuum theory.** *(Amended in Version 3; the
  Version 2 line "no interacting theory of either statistics" is
  overtaken by §10B and is withdrawn.)* Interacting Hamiltonians at
  finite modes are constructed for both statistics (§10B) — matter
  self-interaction only. No gauge-coupled interaction appears
  anywhere in this paper: a mixed fermion–boson (Yukawa) term cannot
  yet even be *stated* in one Lean environment, because the two
  Fock modules cannot be co-imported (the `adag` collision; repair
  priced, §14 item 10). No scattering content, no interacting
  Poincaré representation, and no interacting theory in the
  continuum is constructed or claimed.
- **No continuum Γ.** *(Amended in Version 3; the Version 2 line
  "No infinite-mode or continuum Γ" was false from 2026-10-16 and
  is withdrawn.)* Γ is verified at finite modes (§§9–10) and, for
  the free theory, at countably many modes (§10A). No continuum
  lift of Γ is proved or claimed.
- **No Poincaré representation on Fock space, and no interacting
  Poincaré representation.** *(Amended in Version 3.)* What is now
  proved is one-particle: the free mass-shell measure is invariant
  under the full restricted Lorentz group (§7 amendment). §9
  (Task 4) discharges the Γ-lift's *form* at finite modes for
  mode-set-preserving groups only. No boost or continuum rotation
  is implemented as a strongly continuous unitary representation
  on any Fock space in this corpus (strong continuity and Fock
  packaging remain priced, §14 item 4), and the interacting
  continuum Poincaré representation is Pitch 4's Stage 4 —
  FRONTIER, unbuilt.
- **No reflection positivity at general coupling.** Stage 1b-B
  (§13A) proves the OS form, its positivity at β = 0, and the
  Gram criterion; positivity at general β is reduced to one named
  open clause (the Gram factorization of the Wilson weight,
  XL/Mathlib-blocked). **PARTIAL-δ is not claimed.** Nothing in
  §13A's Stages 1b-C/1b-D spends that clause: the OS space is
  positive by construction, and the transfer matrix's proved
  properties route through 1b-A's proved reflection invariance
  and the Gibbs measure's positivity alone.
- **No lattice gap at general coupling, and no uniformity.** The
  transfer matrix's gap is proved exactly at β = 0 only (§13A).
  At general β the gap is fenced and priced (§14, item 12); no
  gap uniform in volume or coupling is stated anywhere, and no
  continuum-limit conclusion is drawn from any finite-lattice
  statement in this paper (Stage 3c's uniform estimates are
  research-scale and open in print; Stage 4 is FRONTIER).
- **The bosonic interacting Hamiltonian is not called
  self-adjoint without its scoped senses.** Symmetry, sectorwise
  self-adjointness, and LinearPMap formal self-adjointness are
  proved (§10B); essential self-adjointness is priced (§14,
  item 9), and the unqualified headline is not spendable.
- **No bridge from the background algebra.** The modules of Appendix A
  (the ℤ₃ and ℤ₆₀ gradings, the flux-twist toy, the weld, and the
  graph-Laplacian bridge exhibit) are T1 algebra standing alone: no ℤ₃ grading of the TRO, of any tripotent
  family, or of any Dirac operator is claimed, and no physical content
  is asserted for them.

## 17. Reproducibility

- **Source:** https://github.com/jeffgurd888/thet-logos (Lean sources in
  `lean/ThetLogos/`; verdict dossiers in `whitepaper/`).
- **Build:** with Lean 4 / Mathlib per `lean/lean-toolchain` and
  `lean/lake-manifest.json`: `cd lean && lake build` (green; covers the
  root-imported modules, and was green at 3,325 jobs at the Rung 9,
  Rung 8B, and Rung 10 landings). The remaining modules build
  individually: `lake build ThetLogos.<Module>` — the 2026-10-15 status
  per module is reported in §0, the Version 2 modules' targeted
  builds are reported in the §0 addendum, and the Version 3 modules'
  targeted builds (each green, with job counts) are reported in the
  §0 Version 3 addendum. The Version 3 inventory was taken at commit
  `4380a2a`.
- **Counts:** the counting method of §0 (Version 1–2 numbers) and of
  the §0 Version 3 addendum (all Version 3 numbers, one uniform
  method) reproduce every number in this paper from the sources.
- **Axioms:** `#print axioms <theorem>` in any module reproduces the
  footprints reported in §0.

## Acknowledgments

This program formalizes. It did not originate the ideas, the
problems, or most of the mathematics it verifies. The staircase
this corpus stands on, named at the author's direction ("make
sure the true credit goes to them"; the repository's
`ACKNOWLEDGMENTS.md` carries the same text):

- **The problem.** Chen Ning Yang and Robert Mills — the gauge
  theory whose rigorous construction is the summit this program
  climbs toward. Arthur Jaffe and Edward Witten — the official
  Clay statement of the Yang–Mills existence and mass gap
  problem. The Clay Mathematics Institute — for posing it as a
  Millennium Problem.
- **The geometry.** Paul Dirac — the Dirac operator at the heart
  of every spectral triple in this corpus. Alain Connes —
  noncommutative geometry and the spectral triple; the distance
  formula, the spectral action, and the framework this corpus
  formalizes. Ali Chamseddine — co-architect of the spectral
  action and of the almost-commutative Standard Model geometry.
- **The modular theory.** Minoru Tomita and Masamichi Takesaki —
  the modular theory that turns a state into a flow. Alain
  Connes and Carlo Rovelli — the thermal time hypothesis.
- **The axioms and the fields.** Arthur Wightman — the axioms a
  rigorous quantum field theory must satisfy. Konrad
  Osterwalder and Robert Schrader — the Euclidean axioms and
  reconstruction. Werner Heisenberg — the operator language of
  quantum mechanics. Erwin Schrödinger — the equation whose
  dynamics this corpus formalizes. James Clerk Maxwell — the
  first gauge field theory. Albert Einstein — the field
  equations whose Hilbert-type terms the spectral action
  recovers at finite level. Isaac Newton and Gottfried Wilhelm
  Leibniz — the calculus and the limit: the continuum this
  program works to reach honestly.
- **The lattice.** Kenneth Wilson — lattice gauge theory and
  the renormalization group picture; the route §13A takes.
  Shmuel Elitzur — the theorem that gauge-variant quantities
  cannot acquire expectation values; proved here as a result,
  not assumed as a slogan. Miroslav Fiedler — the variational
  eigenvalue bound used in this corpus's graph-Laplacian
  exhibit. Alfréd Haar — the measure every lattice expectation
  here is integrated against.
- **The analysis.** Laurent Schwartz — distributions and the
  function spaces of this corpus's analytic rungs. Marshall
  Stone and John von Neumann — the spectral and unitary
  machinery underneath the dynamics. Leonhard Euler — the
  action-and-extremum tradition the whole Lagrangian world
  descends from.
- **The staircase in modern form.** The Lean community and the
  Mathlib contributors — thousands of people whose verified
  library this corpus imports directly; our theorems stand on
  their theorems, mechanically and literally. The constructive
  field theory tradition — Glimm, Jaffe, Balaban, and many
  others — whose decades of work mark the frontier this
  program measures itself against.

Formalization, verification, and the finite-level results are
ours. The concepts are theirs. If this corpus is ever cited,
cite the originators first.

## Appendix A. Background algebra (fenced — not part of the ladder)

This appendix reports five T1 modules that stand alone. They
are **not** rungs of the ladder, **not** physics, and **not** claimed
to connect to the corpus's operator-algebra structures; they are
recorded here so the inventory is complete and the fence is explicit.

- **Ternary substrate (`TritGrading.lean`, 350 lines; T1).** A
  three-element type `Trit` (`neg | zero | pos`) with its full abelian-
  group laws proved by case analysis and a bundled additive equivalence
  `Trit.addEquivZMod3 : Trit ≃+ ZMod 3`; a submodule-valued grading
  structure `TritGrading` whose only axiom is multiplication closure,
  with commutator closure (`TritGrading.commutator_mem`) and adjoint-
  action closure (`TritGrading.ad_mem`) proved, plus a block-offset
  instance; honestly named commutator facts (`commutator`, `ad` — not
  "curvature", not "covariant derivative"); and the squared-commutator
  trace bound `trace_commutator_sq_nonpos` for Hermitian matrices
  (`trace [A,B]²` is not a Chern character, and is not named as one).
  Zero sorrys; headline axiom footprint exactly
  `[propext, Classical.choice, Quot.sound]`. **Connection audit
  (honest): none.** The corpus's "ternary" is the TRO product
  `⟨a, b, c⟩ = a · star b · c` — a 3-ary *operation*, a different notion
  of "three" from a cyclic *grading*; nothing in the corpus grades the
  TRO or its tripotents by ℤ₃, and the corpus's operator-algebra
  gradings are ℤ₂ (the spectral triple grading `γ_F`). The substrate
  stands alone as background algebra: hygiene and readiness, no forced
  bridges.
- **Sexagesimal clock (`SexagesimalClock.lean`, 433 lines; 31
  theorem/lemma declarations, 12 definitions, 1 structure; T1).** The
  ℤ₆₀ sibling of the trit module, built to the same standard: unique
  two-place sexagesimal representation for every n < 3600 (and the
  three-place version for n < 216000), both with uniqueness proved;
  the divisibility core (every k in {1,2,3,4,5,6} divides 60, and
  lcm(1,…,6) = 60 — the last depending on no axioms at all); the
  canonical sub-clock reduction maps out of ℤ₆₀, the mod-3 one named
  `toTritClock`; the Chinese remainder decomposition
  `crtEquiv : ZMod 60 ≃+* ZMod 3 × ZMod 4 × ZMod 5` with the projection
  compatibility `crtEquiv_fst` proved (the first component *is* the
  trit reduction); a `ClockGrading` structure with commutator and
  adjoint-action closure; and the headline `ClockGrading.reduceToTrit`
  — every ℤ₆₀ clock grading pushes forward along the mod-3 reduction
  to a genuine `TritGrading`. That is grading bookkeeping: the trit
  clock sits inside the sexagesimal clock *as gradings*. Not a
  physical identification. Targeted build green (3,118 jobs); zero
  `sorry`, `admit`, or `native_decide`; eight headline axiom checks
  exactly `[propext, Classical.choice, Quot.sound]`. One vocabulary
  fence, stated in the file header: the "modular" of this program is
  Tomita modular theory; this module is modular *arithmetic*, and the
  rhyme earns nothing.
- **Flux-twist toy (`FluxTwist.lean`, 582 lines; 38 theorem/lemma
  declarations, 10 definitions; T1).** A finite toy on the same
  shelf: the twisted shift on the ring of `Fin (n+1)` sites, the
  boundary bond carrying the flux phase. Proved: unitarity
  (`twistedShift_unitary`, both products with the conjugate
  transpose); flux periodicity (`twistedShift_add_two_pi`:
  S(θ + 2π) = S(θ)); gauge redistribution
  (`twistedShift_mul_gaugeMatrix` — the boundary twist *is* the
  uniform twist, conjugated by the diagonal gauge matrix whose site-k
  phase is θ·k/(n+1)); and the ring hearing the flux — the eigenphase
  (θ + 2πm)/(n+1), proved for the uniform twist on plain Fourier
  vectors and for the boundary twist on flux-carrying Fourier vectors
  (plain ones fail the wrap bond by exactly the flux factor; recorded
  in the file). The stretch target landed except its priced item: the
  hopping Hamiltonian is Hermitian (`hopping_isHermitian`) with
  eigenvalues −cos((θ + 2πm)/(n+1)); the Gibbs-state modular-flow
  generation statement is **priced, not formalized** (it needs matrix
  exponentials and the finite-dimensional modular theory of Gibbs
  states), and is stated as priced in the file header. The vocabulary
  fence is the module's point: "magnetism" appears only as flux twist
  — the Aharonov–Bohm effect in miniature. It is **not** a bridge to
  real magnetism or Maxwell's equations, and **not** a Yang–Mills
  rung. Targeted build green (3,120 jobs); zero `sorry`, `admit`, or
  `native_decide` in code; six headline axiom checks exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Weld duality (`WeldDuality.lean`, 893 lines; 73 theorem/lemma
  declarations, 18 definitions; T1).** Finite linear algebra: the
  finite shadow of the Morley idea of §13, built in both of its
  configurations as two faces of one module. The common core: for an
  involution η (η² = 1), the spectral projections `weldPlus` /
  `weldMinus` = (1±η)/2 are complementary orthogonal idempotents,
  η = P₊ − P₋, the trace formula `tr P₊ = (n + tr η)/2` holds, and
  the signature count is rigid under conjugation. Face A is the
  grading split with a corrected involution: `corrInv` in
  parametrized form (an involution when η² = A² = 1, ηA + Aη = 0,
  c² = 2), and on the ℂ⁴ arena (η = diag(1,1,1,−1)) a corrected
  involution carrying a Hadamard block on the mixed directions
  (`etaCorr_sq`). Face B is the Dirac sign with the gap split: for
  D = diag(2,1,−1,−3), the sign involution η_D is Hermitian with
  η_D² = 1, its plus-projection is the positive spectral subspace by
  computation (`weldPlus_etaDirac`), and H = D² is split at Δ² = 2
  into complementary orthogonal projections with `gap_dichotomy`
  (every eigenvalue is 1 or ≥ 2). The linkers are proved, and they
  are what makes the two faces one module: Face B is an instance of
  Face A (`signature_etaDirac`), so the signature count follows the
  **input** in both faces — the §13 kill (`signature_not_determined`)
  stands untouched, and nothing here derives (3,1); and the curved
  correction leaves the plus-projection's trace invariant while the
  projections genuinely differ (`trace_weldPlus_etaCorr`,
  `weldPlus_etaCorr_ne`) — the stability is not vacuity. The
  resting-place theorems the module was designed around are proved:
  the fixed set of an involution is exactly the range of its
  plus-projection (`fixed_iff_range_weldPlus`), and for two commuting
  involutions the joint fixed set is the range of the product
  projection (`joint_fixed_iff_range`). **Priced, not attempted:**
  the general correction-stability theorem (the plus-projection's
  count constant along a general correction, for arbitrary n) — only
  the worked-arena instance above is proved. The fence, stated in
  the file header: "2D holography" does not survive into this
  module — only the finite shadow does, dimension counted by traces
  of spectral projections. **Not** a Yang–Mills rung.
  `EdgeSignature.lean` is not imported (its §1 pair algebra is
  restated locally; disclosed in the file header). Targeted build
  green (3,120 jobs); zero `sorry`, `admit`, or `native_decide` in
  code; seven headline axiom checks exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Graph-Laplacian bridge exhibit (`BridgeLaplacian.lean`, 466
  lines; 29 theorem/lemma declarations, 7 definitions; T1).**
  *(Added in Version 3.)* On a finite weighted graph (vertex type
  V, symmetric weights w as bare data — symmetry and
  nonnegativity are theorem hypotheses, never baked into the
  definitions): the bridge operator `dropVec F i j = F j − F i`
  between node potentials and edge drops, with its linearity,
  antisymmetry, and the telescoping path law whose closed-path
  corollary is the discrete Kirchhoff voltage law; Ohm's law as
  the middle factor `ohm w X i j = w i j * X i j`; and the
  **factorization** `laplacianOp_eq_diverge_ohm_drop` —
  L = dᵀσd — a genuine theorem, not a definition (the divergence
  gathers transposed entries, so the two sides agree only after
  the symmetry of w is spent). With it: the current law
  (∑ᵢ (LF)ᵢ = 0), the dissipation identity
  (2·energy = ∑ᵢⱼ w i j (Fᵢ−Fⱼ)²) and energy nonnegativity,
  self-adjointness of the form, the kernel characterization
  (zero energy ⟺ F constant across every conducting edge; at
  all-positive weights, F constant), and the **Fiedler value**
  as a variational infimum with its bound proved whole
  (`fiedler_le_energy`, `fiedler_nonneg`) — the pre-authorized
  fallback of pricing the bound was not needed. The three
  readings of the exhibit (resistor network / graph heat /
  DeGroot consensus) are recorded as an *equation identity* —
  one operator equation read three ways — claiming nothing
  about real circuits, real heat, or real electorates.
  **Priced, not attempted:** attainment of the variational
  infimum (S), exponential decay at the Fiedler rate (M), and
  Faraday's law — the exhibit's second storey, needing
  cycle/flux data (S–M). Relation to Mathlib, stated in the
  dossier: Mathlib's `SimpleGraph.lapMatrix` is the unweighted
  0/1 Laplacian; this exhibit differs in kind (arbitrary
  symmetric real weights, function-level operators, the
  explicit d/σ/dᵀ factorization), and no novelty beyond that
  packaging is claimed. Not a Yang–Mills rung, and not
  connected to §13A's lattice: graph and lattice objects
  differ in kind, and no bridge between the exhibit and the
  lattice stages is claimed. Targeted build green (3,117
  jobs); zero `sorry`/`admit` in code; eight headline axiom
  checks exactly `[propext, Classical.choice, Quot.sound]`.

---

*Notation.* φ denotes the modular flux i[K, D] (Hermitian,
`modularFlux_selfAdjoint`). Φ is reserved for the ontological glyph and is
not used in this paper. Tet (the narrator of the companion books) and thet
(the law) are distinct; neither is a mathematical object of this paper.
