# Pitch 4 Scoping — The Continuum Passage (Lattice → Continuum, Gauge Sector)

**DRAFT SCOPING — NOT A DOSSIER. Nothing in this document is built, proved,
or claimed. It is a priced build order for Jeff's greenlight, written
2026-10-17 after Pitch 3 closed (verdict: the scoping's pre-named PARTIAL
narrowed to one priced clause — bosonic essential self-adjointness), after
the Schrödinger dynamics exhibit stood, and after the Rung 7 boost window
was discharged whole (2026-10-17). Format and honesty template:
`pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md` and
`pitch-3-interaction-scoping-DRAFT-2026-10-16.md`. Ancestor guardrail:
`rung-3-continuum-scoping-2026-10-10.md` (§0: a finite object does not
"become" continuous; a limit is a new object with a proved relation to its
approximants — that kill carries into this pitch verbatim).**

**NO CLAIM charter.** This pitch makes no claim on any Millennium Problem.
Parts of the official Clay Yang–Mills statement closed by this program:
**0** — before this pitch, and (stated in advance, §8) after any landing of
it. The charter of the millennium board governs: a project states NO CLAIM
until a proved theorem closes part of the official statement, and no stage
of this pitch closes one.

Labels that govern every line below, now and after any landing: this pitch
is about the **continuum passage for a gauge theory the corpus does not yet
possess**. Standing whole (§8), it buys a finite lattice gauge theory with
exact gauge invariance, its correlation/reflection-positivity package, one
honest coarse-graining step, and the continuum-limit *scaffolding* — pinned
targets and named uniform-estimate obligations. It does **not** buy the
continuum theory, its Poincaré covariance as a theorem, or any part of the
mass gap. It removes, at most, the scope words **"no gauge sector"** and
**"no passage formalized"** — and replaces them with **"gauge sector at
finite lattice; the passage priced at its own front door."** The words
"continuum" and "Poincaré" are not removed from the frontier list by
anything in this pitch; §9 prices what still stands behind them.

Effort classes used below: **S** = one small module section (days);
**M** = one focused module (week scale); **L** = a campaign (Γ-functor
campaign scale, ~1,000+ lines); **XL** = new-infrastructure scale,
open-ended. One calibration this pitch needs and the earlier ones did not:
for Stages 3–4 the XL class stretches past anything the ladder has priced —
Balaban's block-spin program for lattice gauge theory is roughly 500
journal pages across a decade (1987–1995), in print, by a master of the
method, and it is a *mathematics* result, not a formalization, with the
mass gap absent from it and open issues noted by its critics. Where a
stage's price is of that character, the document says so in words, not
just in letters.

---

## 0. Verdict preview

**Recommendation: the lattice route, Stages 0–2 as campaigns, Stage 3 as
scaffolding-plus-priced-wall, Stage 4 not in the landing.** In order:

1. **Stage 0 — finite lattice gauge theory** (link variables, Wilson
   action, exact gauge invariance): the gauge sector's birth certificate.
   Pure finite mathematics on a finite product of Lie groups with Haar
   measure. **L.** This is the only stage whose every input already exists
   in Mathlib or in the corpus.
2. **Stage 1 — lattice correlations + reflection positivity** at finite
   volume and spacing, for the Wilson action, with strong-coupling
   clustering priced separately as the stage's XL component.
3. **Stage 2 — one coarse-graining step as a theorem-shaped object**
   (blocking as partial integration of the Stage-0/1 measure; what
   composes, what does not; what a fixed point would mean in our
   language). **M–L** for the honest finite form; the iterated flow with
   estimates is priced XL and named Balaban-scale.
4. **Stage 3 — continuum-limit scaffolding**: the target pinned with real
   content (Schwinger functions as data, OS axioms E0–E4 as obligations,
   the uniform-in-spacing estimates stated as the pitch's exposed debt).
   The analytic core — proving the limits exist with OS control — is
   **priced, not promised**: in print, for 4D Yang–Mills, it is not done
   by anyone, and a formalization campaign cannot outrun the mathematics
   it formalizes.
5. **Stage 4 — real Poincaré for the interacting continuum theory**: not
   a stage of this pitch's landing. Priced FRONTIER in §6.5, with its
   inputs (Rung 7 remainders, OS reconstruction) itemized.

**The alternative analytic route** (continuum-first / OS-direct) is priced
in §6.6 as a comparison: **XL with no landing in sight**, and recommended
only as the *language* in which Stages 3–4's targets are pinned — which is
the corpus's established pattern (pin the target as a statement with real
content, build the finite thing exactly, price the passage).

**The honesty line.** Pitch 2 removed "finite modes" and Pitch 3 removed
"free." Pitch 4 does not remove "finite lattice" — because the continuum
is not a bigger lattice, and the passage to it is the part of constructive
QFT that has resisted the entire field for fifty years. What this pitch
removes is the program's *excuse* for not facing the passage with its own
instruments: a gauge sector that exists, transitions whose distortions are
priced at each boundary (§3), and the remaining wall stated in the
program's own theorems-to-be rather than in fog.

---

## 1. The target pin — the official statement, and what this pitch touches

### 1.1 The official Clay statement (Jaffe–Witten, 2000), stated precisely

For **any compact simple gauge group $G$** (e.g. $SU(3)$, but the problem
quantifies over all of them): **prove that a non-trivial quantum
Yang–Mills theory exists on $\mathbb{R}^4$** — i.e., construct a quantum
field theory of Yang–Mills fields on four-dimensional Minkowski spacetime
satisfying the **Wightman axioms** (equivalently, via Osterwalder–Schrader
reconstruction, a Euclidean theory satisfying the OS axioms E0–E4 whose
reconstruction is the theory) — **and that this theory has a mass gap**:
there exists $\Delta > 0$ such that the spectrum of the Hamiltonian $H$
satisfies

  $\mathrm{spec}(H) \subseteq \{0\} \cup [\Delta, \infty)$,

with $0$ the vacuum energy and no spectrum in $(0, \Delta)$ — the least
massive excitation (the lightest glueball) is strictly massive.

The statement has four separable components, and the ledger scores them
separately:

1. **Existence** of the continuum quantum theory (a construction, not a
   formal power series).
2. **Axioms**: the constructed object satisfies Wightman (or OS)
   axioms — covariance, spectral condition, locality, vacuum, in full.
3. **Non-triviality**: the theory is not free/Gaussian.
4. **Mass gap**: $\Delta > 0$ as above.

**Parts closed: 0** — by this program, and (as of this writing) by
anyone, for 4D Yang–Mills. The nearest literature landmarks are pinned in
the corpus's own `MassGapDossier.lean` (T5 statement pins with exact
scope): lattice strong-coupling gap + area law (Osterwalder–Seiler 1978 —
lattice only, strong coupling only, continuum limit explicitly not
included); Balaban's RG program (continuum existence at small bare
coupling claimed in print; mass gap *not* proved; large-field control
open); the 2D abelian Higgs model (Brydges–Fröhlich–Seiler — the one
complete interacting gauge construction satisfying the axioms, in two
dimensions); $\varphi^4_4$ triviality (Aizenman–Duminil-Copin 2021 — the
scalar route closed). None of these is a part of the 4D statement closed.

### 1.2 The corpus's own pin — present, and deliberately content-opaque

The target is already pinned in the corpus, at marker level:
`lean/ThetLogos/ClayStatement.lean` defines `ClayProblem : Prop` —
$\forall G$ compact simple, $\exists T : \texttt{QuantumYangMillsTheory}\ G$,
$T$ nontrivial with `HasMassGap T` — where `QuantumYangMillsTheory` is a
structure whose fields are **opaque Props** (axiom satisfaction, spectrum
as an abstract `Set ℝ`, nontriviality) and `CompactSimpleGroup` is a
marker structure (carrier + two properties), the file's own header
labeling it **T5** ("theorem-shaped, content opaque"). `WightmanAxioms.lean`,
`OsterwalderSchrader.lean`, and `HaagKastler.lean` pin the three axiom
frames the same way (their E0–E4/W0–W6 fields are opaque Props;
`OSReconstruction` is pinned with conclusion `True` — a statement-shaped
marker whose current *logical* content is nil, by design and labeled as
such in-file). Consequence for this pitch: **the pins mark where the
statements go; they are not the statements in analytic dress.** Stage 3's
first job is a re-pin with real content (Schwinger functions as actual
data — sequences of tempered distributions with the axioms as actual
conditions) before anything may be aimed at them (§6.4). No text may cite
`ClayProblem` as if its marker fields were the analytic axioms.

### 1.3 Exactly what Pitch 4 touches — and what it does not

**Touches:**

- **Gauge-sector existence, at the finite level.** Stage 0 creates the
  first quantized gauge degrees of freedom in the corpus's history:
  group-valued link variables with an exactly gauge-invariant action and
  measure. Today the corpus's gauge sector is *classical finite algebra
  only* (§2) — Γ(U) acts on matter; nothing in the corpus is a gauge
  field. Stage 0 changes that fact, at finite lattice, full stop.
- **The continuum-limit sub-question, as scaffolding and priced wall.**
  Stages 2–3 formalize the *passage machinery* (one blocking step; the
  limit's target and obligations). The continuum existence component (1)
  of the official statement is the wall behind Stage 3 — named, not
  claimed.
- **Real Poincaré covariance — as target only.** Stage 4 prices it
  (§6.5). The corpus today has Poincaré in two honest finite/free forms
  (a classical Poincaré *group* object, `PoincareAction.lean`; the free
  one-particle representation with full restricted-Lorentz invariance of
  its measure after the 2026-10-17 boost discharge). Neither is the
  interacting continuum theory's covariance, and this pitch does not
  produce it.

**Does not touch:**

- **The interacting mass gap.** This must be said without softening: the
  gap (component 4) is a wall *beyond* continuum existence, not a
  corollary of it. A hypothetical whole Pitch 4 — even one in which
  Stage 3's analytic core miraculously stood — would deliver a continuum
  theory whose spectrum still has to be *proved* gapped, and the proof
  obligations for that (uniform clustering along the entire tuning curve,
  at all scales) are a further program, priced in §9. Any future sentence
  of the form "continuum, therefore gap" is a violation of this scoping.
- **Full Wightman verification for any theory.** The corpus verifies the
  Wightman axioms for no theory today (§2), and this pitch does not
  change that: OS reconstruction is a Stage-3/4 prerequisite priced XL
  (§6.4–6.5), not a campaign deliverable.
- **Matter coupling.** Stage 0 is *pure* gauge theory (no dynamical
  fermions/bosons on the lattice). Coupling the corpus's matter Fock
  machinery to lattice gauge links is a further pitch; the `adag`
  namespace collision (Pitch 3, §1.2 of its scoping) still blocks even
  *stating* mixed-statistics interactions in one environment.

---

## 2. Corpus audit — what exists, what does not (grep-verified, 2026-10-17)

Corpus: `lean/ThetLogos/*.lean`, 97 modules, at local head `b949587`
(program total 2,080 declarations by the decomposed counting convention of
the dossiers). Every claim below was checked by grep over the corpus on
2026-10-17; the greps are cited so any reader can re-run them.

### 2.1 Continuum-side assets that DO exist

- **Genuine Schwartz machinery (Rung 6).** `SchwartzSpace.lean` builds on
  Mathlib's `SchwartzMap` — the real `𝒮(ℝⁿ, ℂ)`, tempered distributions
  `𝒮'` as the continuous dual, Fourier transform with inversion — with the
  corpus's own T1 package on top (14 Schwartz T1s per the Rung 6 dossier),
  and `SchwartzComplete.lean` adds completeness results (Rung 7). This
  *discharged* the Rung-4 T2 marker: `schwartzMarker`
  (`SchwartzSpace.lean:243`) instantiates `TestFunctionMarker` with
  `𝒮(ℝ⁴, ℂ)`. **Scope honesty:** the corpus has the test-function *space*
  and its calculus. It does not have a field smeared against it (§2.2).
- **The free one-particle continuum representation (Rung 7), now with
  boosts.** `MassShellMeasure.lean` constructs the mass-shell measure
  $d^3p/2E_p$ and the one-particle $L^2$ representation.
  `MassShellBoost.lean` (2026-10-17, 1,629 lines, 86 T1) discharged the
  boost window priced in 2026-10-11: the x¹-boost Jacobian identity, the
  density cancellation, and the factorization cap — **the free
  one-particle mass-shell measure is invariant under the full restricted
  Lorentz group** (`boostInvariance_window_proved`). This is the
  program's one completed continuum-side symmetry theorem, and it is
  about the **free one-particle** representation: no interaction, no Fock
  packaging (§2.3), no gauge content.
- **A classical Poincaré group object.** `PoincareAction.lean` defines
  `LorentzGroup`/`PoincareGroup` as concrete group structures acting on
  `Minkowski := Fin 4 → ℝ` (`WightmanAxioms.lean:37`), with group-law T1s.
  Classical/algebraic level: a group, not a unitary representation of it
  on any quantum Hilbert space of a continuum theory.
- **Lattice translations at finite modes (Rung 9, Task 4 — PARTIAL).**
  `lattice_translation_rep`: the group `Multiplicative ℤ` acting by
  diagonal phases on `Fin d` modes, lifted through Γ to a unitary
  representation on fermionic Fock space fixing the vacuum and preserving
  sectors (Rung 9 dossier, Task 4). What does not lift is priced there in
  the dossier's own words: boosts and continuum rotations mix a finite
  mode set into infinitely many modes; the mass-shell one-particle
  representation is not an input to Γ. Task 4's PARTIAL stands exactly as
  recorded; Pitch 4 does not re-price it — Stage 4 (§6.5) *consumes* its
  negative half as a pre-kill.
- **Classical gauge algebra (SM-match / ClassicalYangMills).** The
  unimodular gauge group as finite matrix algebra (T1), `gaugeAct` and its
  T1 package (`ClassicalYangMills.lean:79` ff.), classical `ymAction`
  (:237), classical Lagrangian sectors (`SMLagrangian.lean`). All of it
  classical: matrices and algebra functionals. No Hilbert space, no
  operator, no measure.
- **The pinned targets** (§1.2): `ClayStatement.lean`,
  `WightmanAxioms.lean`, `OsterwalderSchrader.lean`, `HaagKastler.lean`,
  `MassGapDossier.lean` — T5 statement pins with named analytic gaps,
  including the dossier's **four transfer obstructions** (different
  objects; branch crossings — the one T1 item, `gap_closes`; no continuum
  limit; conditional lemmas don't compose). That dossier is this pitch's
  wall map; §9 is its continuation.
- **Renormalization combinatorics — with a warning label.**
  `Renormalization.lean` (1,451 lines) is the **Connes–Kreimer Hopf
  algebra of rooted trees**: grafting $B_+$, coproduct, counity and
  coassociativity T1 (the antipode partially T5). It is the combinatorial
  skeleton of *perturbative* renormalization. It contains **no
  coarse-graining map, no flow on any space of theories, no scale** — a
  grep for `coarse|blockSpin|renormalization group|RG flow` over the
  corpus returns exactly one hit, a docstring *inside a T5 pin structure*
  (`MassGapDossier.lean:65`, "Convergence of the RG flow, as proved" —
  a field of `BalabanRGProgram`, i.e. a labeled statement about
  Balaban's literature result, not a corpus construction). **Anyone
  citing `Renormalization.lean` as evidence the corpus has an RG is
  laundering a filename; this scoping flags it in advance.**
- **A flux-holonomy toy (background, not a rung).** `FluxTwist.lean`
  proves the eigenphase package for a U(1) phase twist on a finite ring —
  the corpus's own header: "No gauge field, no connection on a bundle, no
  field strength appears." It is the closest gauge-*flavored* finite
  object in the corpus and it is a one-plaquette shadow, not a lattice
  gauge theory (§2.2).

### 2.2 The hard absences (each grep-verified)

- **No quantized gauge field — anywhere.** Grep for
  `gaugeField|connectionOp|covariantDeriv|gauge field` over the corpus
  returns only header disclaimers ("no gauge field" in
  `BosonicInteraction.lean:17`, `FermionicInteraction.lean:17`,
  `FluxTwist.lean:31`) and prose about what a gauge field *would* need
  (`ClassicalYangMills.lean:41`, `ProductTriple.lean:623` — "CONSTANT
  matrices — gauge parameters, not gauge fields"). There is no gauge
  connection as an operator, no gauge-field Fock space, no link variable.
  Pitch 3's audit certified gauge self-interaction OUT for exactly this
  reason; the absence is unchanged since.
- **No lattice gauge theory.** Grep for
  `plaquette|linkVariable|wilsonAction|latticeGauge` (case-insensitive)
  over the corpus: **zero hits**. No finite spacetime lattice with
  group-valued links, no Wilson action, no Haar-integrated observable,
  no transfer matrix (grep `transferMatrix|transfer matrix`: zero hits).
- **No spacetime-smeared field operators.** The Rung-4 API
  (`FieldOperators.lean`) proves smeared-*creator* theorems
  (`createFermSmeared`, `createSmeared`) — **conditional on a T2 marker**:
  an abstract test-function type and an abstract linear smearing map into
  an abstract one-particle space $V$. Rung 6 discharged the *space* half
  of the marker (`𝒮(ℝ⁴, ℂ)` exists now, §2.1), but **no module constructs
  the smearing map** (in a real construction: the Dirac/Klein–Gordon
  solution operator with positive-frequency projection), and the full
  field $\varphi(f) = a^\dagger(f) + a(f)$ does not exist — the
  annihilation half is priced in-file as T5 windows
  (`fermionicFieldCAR_window`, `bosonicFieldCCR_window`), still unproved.
  There is no $\varphi(f)$ for $f \in 𝒮(ℝ⁴)$, no field at a spacetime
  point, no operator-valued distribution in the corpus.
- **No RG / coarse-graining formalism.** See the warning in §2.1: no
  blocking map, no space of actions, no flow, no fixed-point statement
  exists as corpus mathematics. (Mathlib is in the same position, §5.)
- **No correlation-function / Schwinger-function machinery.** Grep
  `schwinger` returns `KMSBridge.lean:12` (Kubo–Martin–**Schwinger** —
  the KMS condition, a different name-bearer) and
  `OsterwalderSchrader.lean` (the T5 marker structure `SchwingerMarker`,
  whose carrier is an abstract `Type` and whose axioms are opaque
  Props). Grep `correlation|nPoint|twoPoint` returns the pins and
  `FreeField.lean`'s *algebraic* two-point theorems
  (`twoPoint_algebraic_trivial` — one-mode algebraic identities the
  file's own header labels trivial in the technical sense: they are
  statements about the one-mode algebra, not functions on spacetime).
  There are no $n$-point functions of any field on any spacetime,
  Euclidean or Minkowski, anywhere in the corpus.
- **No OS or Wightman verification for any theory.** The axioms exist
  only as T5 pins (§1.2). `OsterwalderSchrader.lean`'s own closing note
  records that even the **free scalar field's** OS verification is T5
  for now (it needs the Gaussian measure on $𝒮'(ℝ⁴)$ — Minlos — which
  neither Mathlib nor the corpus has, §5). Reflection positivity occurs
  in the corpus only as an opaque Prop field
  (`OsterwalderSchrader.lean:51`) and as prose inside pins
  (`MassGapDossier.lean:167`). No module proves E0–E4, W0–W6, isotony +
  locality in the continuum, or reconstruction for *any* input — free or
  interacting.

### 2.3 Rung 7 remainders — priced, open, and inputs to Stage 4

Two items priced at Rung 7 remain open and are **not** discharged by the
boost result (its dossier says so explicitly):

- **Strong continuity** of the one-particle representation (the
  `StrongContinuity_window`: DCT with the dominating function
  identified) — priced T5 at Rung 7, still open.
- **Fock packaging** of the one-particle representation (second
  quantization of the mass-shell representation as a unitary
  representation on a Fock space) — blocked/priced at Rung 7 ("Fock
  inner product…" obstruction), still open.

Both are *free-side* items, independent of the gauge sector, and both are
prerequisites for any Stage-4 sentence that mentions a representation of
the Poincaré group on a Hilbert space — even the free one. Their prices
are inherited, not re-estimated here: strong continuity **S–M**
(analysis on an existing construction); Fock packaging **M** (the
Pitch-2 Γ machinery exists for `ℓ²(ℕ)`-type spaces; the mass-shell
one-particle space is a different presentation — a port, not an
invention). Neither blocks Stages 0–3.

---

## 3. The front door — Jeff's epiphany, operationalized (2026-10-17)

Jeff's framing, recorded 2026-10-17 and grafted onto the Tree of
Questions the same morning: *the discrete-to-continuum problem is the
translation of the one into the many and the many into the one — and it
is the transition problems that cause the same distortion; approach from
the analytical side and use metadata of the one to predict the
possibilities.* This scoping takes the principle as its organizing frame
— with the discipline the principle itself demands: a frame is not a
proof, and §3.3 marks exactly where it stops reaching.

### 3.1 The distortion lives in the transitions, not the levels

Corpus precedent, stated as the ladder's own empirical law: every
*level* the program has built is internally exact (finite modes,
countably many modes, finite-dimensional dynamics — T1 at the level).
Every *passage* between levels cost a priced distortion, and the price
was stated in the passage's own currency:

- finite modes → countably many modes (Pitch 2): the gap survived only
  under a **single fixed Δ** hypothesis; a sequence $\Delta_d \to 0$
  survives as nothing — the distortion, priced in the hypothesis.
- free → interacting (Pitch 3): the gap survived under an explicit
  **threshold** ($2|g|\cdot\mathrm{intBound}\,W \le \Delta/4$,
  fermionic); for bosons, uniform persistence was **false** (proved
  in-module: attractive collapse) and only windowed/sector forms stand.
- $t = 0$ → dynamics (Schrödinger exhibit): the gap clusters survived
  as invariant subspaces — proved, because the transition (spectral
  phases) was unitary and exact.
- rotations → boosts (Rung 7 discharge): the passage cost one Jacobian
  identity, priced in 2026-10-11 and paid in 2026-10-17.

Pitch 4 is the first pitch whose central transition — lattice →
continuum — has a distortion **nobody has priced**, in print or in Lean.
The stages of §6 are therefore drawn as *levels with priced internal
content*, separated by *transitions whose distortions are itemized*,
and the landing (§8) claims the levels and the *scaffolding* of the
passage — never an unpriced crossing. Each stage in §6 carries its
transition accounting explicitly: what the passage into the next stage
costs, in what currency, and who has ever paid it.

### 3.2 The named transformations

- **Many → one: coarse-graining.** The renormalization-group direction:
  integrate out short-distance degrees of freedom, obtain an effective
  description of the same physics at larger scale. On the lattice this
  is *blocking* (Kadanoff/Wilson): group sites into blocks, define
  coarse variables, induce a new action. Stage 2 is this transformation,
  formalized at the one-step level.
- **One → many: discretization / UV completion.** The reverse street:
  given a continuum description, produce finite approximants. Stage 0 is
  an instance (the Wilson action is a discretization of
  $\int \mathrm{tr}\, F^2$, chosen — among many possible discretizations
  — for its exact gauge invariance and reflection positivity). The
  one→many direction in this pitch is a *choice*, and its price is that
  the choice must be audited by the many→one direction: a discretization
  whose coarse-graining flow does not approach the Gaussian fixed point
  along an asymptotically free trajectory does not discretize
  Yang–Mills, whatever its classical limit says. (Classical
  $a \to 0$ agreement of the action density is necessary and nowhere
  near sufficient — it is a statement about the action, not about the
  measure, and the measure is the theory.)
- **The continuum limit itself is neither.** It is the many→one
  passage *iterated to the fixed point and taken along a tuned curve*
  (§4) — which is why "coarse-graining" names Stage 2's step and
  "continuum limit" names Stage 3's wall, and no module may use the
  second phrase for the first thing.

### 3.3 Protected metadata — the audit instrument, with its honest reach

The epiphany's instrument: data that is *protected* across a transition
can be computed on the easier side and used to audit the passage
(anomaly-matching being the archetype in the world's literature). For
**this** problem the protected list is thin, and the scoping's duty is
to say exactly how thin:

| Candidate metadata | Protected? | What it audits here | Honest reach |
|---|---|---|---|
| **Gauge invariance itself** | Yes — exactly, at every lattice stage (group-valued links, Haar measure) | Stages 0–1: any construction or "result" breaking finite gauge invariance is *wrong*, mechanically checkable | Full — but it audits constructions, not the limit: the continuum theory's gauge structure is a redundancy of description, recovered (in OS language) through gauge-invariant observables only |
| **Center symmetry / confinement diagnostics** (Polyakov loop, Wilson area law) | Protected as *phase* data along the flow | Stage 1/3: which phase a coupling region is in; area law at strong coupling is a theorem (Osterwalder–Seiler, pinned T5) | Qualitative: phases and order parameters, never a Δ value |
| **'t Hooft anomalies** (where matter content gives them) | Yes — anomaly matching is exact across RG flow | Pure YM has no continuous flavor symmetry to match; with fermions, anomalies forbid certain trivially-gapped IR phases | Qualitative phase constraints only; for the pure-gauge Clay problem the instrument is nearly empty — **anomaly matching does not touch existence and does not bound Δ** |
| **The gap, *if uniform in $a$*** | Would be protected *by definition of uniformity* | Stage 3→§9: exponential clustering with an $a$-uniform rate along the tuning curve passes to the continuum | **Protected-but-unavailable: proving the uniformity is essentially the gap half of the Clay problem restated.** Citing it as an instrument here is circular, and this scoping forbids the move: it is the thing to be proved, not a tool for proving |
| **Asymptotic freedom** ($\beta_0 < 0$) | A *perturbative continuum* theorem; lattice counterpart is the weak-coupling scaling law for $\beta(a)$ | Stages 2–3: it sets the *shape* of the tuning curve ($a$ as a function of bare coupling via dimensional transmutation) and tells the flow where its UV fixed point is | A tuning guide, not a protection theorem: it predicts the form of the approach to the limit, never the existence of the limit, and it is silent at strong coupling where Stage 1's theorems live |
| **Universality** | Meta-protection: the limit, *if* it exists, is independent of discretization details | Stage 0: freedom in choosing the Wilson action; Stage 3: robustness of the target | Cuts both ways (the Pitch-2 lesson): a robust limit is a weak inverse predictor — universality licenses the choice of approximant and forbids reading continuum specifics off any one of them |

**Where the instrument does not reach — stated once, plainly.** For 4D
Yang–Mills there is no known set of protected data from which existence
or a positive Δ can be *derived* by matching. The historical record
agrees: the field's continuum progress (Balaban) came from controlling
the flow itself, estimate by estimate — the unprotected, unglamorous
route — not from a metadata shortcut. The epiphany's principle is this
pitch's *organizing frame and audit discipline* (price every transition;
let protected data veto bad constructions), and under the Concrete it
may not be quoted as more than that. A frame that vetoes is worth
having: it kills wrong turns early, which is most of what a scoping is
for. It does not shorten Stage 3's wall by one meter.

---

## 4. The shape of the passage — what "continuum limit" obligates

Before pricing stages, pin the object. A lattice gauge theory at spacing
$a$ and linear size $L$ lives on $\Lambda = (a\mathbb{Z}/L\mathbb{Z})^4$
(or $\mathbb{Z}_N^4$ with $N = L/a$ sites per direction), with
group-valued links $U_\ell \in G$ on edges, the Wilson action
$S = \beta \sum_p (1 - \tfrac{1}{N_c}\mathrm{Re}\,\mathrm{tr}\, U_p)$
($\beta = 2N_c/g^2$ conventions vary), and the product Haar measure.
The continuum limit is **not** "$a \to 0$" as a standalone knob:

1. **Two limits, one curve.** $a \to 0$ at fixed physical volume (so
   $N \to \infty$) *and* the infinite-volume limit, taken along a
   **tuned curve** $\beta(a)$: the bare coupling is not free — the
   requirement that physical masses stay fixed as $a$ shrinks forces
   $\beta \to \beta_c$ (for asymptotically free YM, $\beta_c = \infty$,
   approached logarithmically: dimensional transmutation sets
   $a \sim \Lambda^{-1} f(\beta)$). At fixed $\beta$, "$a \to 0$"
   describes a family of unrelated lattice theories, not a limit.
2. **The fixed point is Gaussian; the theory is not.** The UV fixed
   point of the YM flow is the free theory at $\beta = \infty$; the
   continuum theory is the renormalized trajectory *emanating* from it.
   Non-triviality of the limit is therefore a theorem-obligation, not a
   default — the scalar precedent shows the failure shape in print:
   $\varphi^4_4$'s scaling limit exists and is Gaussian
   (Aizenman–Duminil-Copin): the passage can succeed and deliver
   nothing. (For YM, asymptotic freedom makes the mechanism different
   from $\varphi^4$'s; different mechanism, same obligation: prove the
   limit isn't free.)
3. **Uniformity is the whole game.** Correlation functions must converge
   with bounds **uniform in $a$** along the curve — exponential
   clustering with an $a$-independent physical rate, reflection
   positivity preserved at every $a$ and in the limit, temperedness
   (growth bounds) for the limiting Schwinger functions. Every
   historical failure to construct a 4D interacting theory is, at
   bottom, a uniformity failure somewhere along this list.
4. **The limit's output is Euclidean.** What the passage delivers (if
   it delivers) is Schwinger functions satisfying OS E0–E4. Minkowski
   physics — the Wightman theory, its Hilbert space, its Poincaré
   representation, its Hamiltonian and its spectrum — is on the far
   side of **OS reconstruction**, a further theorem (~100 pages of
   analysis in the literature: analytic continuation, edge-of-the-wedge,
   the OS scalar product) that is unformalized anywhere (§5, §6.4).

Every stage price in §6 is a price against this list. A construction
that does not say which items it discharges has not been priced; it has
been advertised.

---

## 5. Mathlib reality — what this pinned Mathlib actually has (grep-verified, 2026-10-17)

Checkout: `~/workspace/thet-logos/lean/.lake/packages/mathlib/`, toolchain
`leanprover/lean4:v4.35.0-rc3`. Method: `git grep` over the checkout plus
directory inspection; every absence below is "the cited grep returned
nothing (or only the named false positives)" — re-runnable as written.

**HAS — and better than the corpus's older files assume:**

- **Distributions are real now.** `Mathlib/Analysis/Distribution/`:
  `TestFunction.lean` (𝒟), `Distribution.lean`,
  `TemperedDistribution.lean` — tempered distributions 𝓢′ with a
  **Fourier transform** (`TemperedDistribution.fourierTransformCLM`,
  `TemperedDistribution.lean:469` ff.), `SchwartzSpace/{Basic,Deriv,
  Fourier}.lean`, `FourierMultiplier.lean`. The 2026 distribution
  infrastructure (Doll) is the reason Rung 6's correction stands:
  `OsterwalderSchrader.lean`'s "Mathlib has no tempered distributions"
  framing is outdated as to *existence* — 𝓢′ exists — and still correct
  as to *theory*: no module of theorems does anything QFT-shaped with it.
- **Sobolev spaces, two kinds.** (i) Bessel-potential Sobolev spaces of
  tempered distributions: `Mathlib/Analysis/Distribution/Sobolev.lean`
  defines `TemperedDistribution.besselPotential` (Fourier multiplier
  $(1+\|\xi\|^2)^{s/2}$) and `MemSobolev`, with the $p=2$ Fourier
  characterization and order-drop under derivatives/Laplacian — more
  than the "incipient" the Schrödinger gauntlet recorded; it is a
  working definition with its first theorem package, not yet an
  elliptic-regularity theory. (ii) The Gagliardo–Nirenberg–Sobolev
  inequality for functions:
  `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`.
- **Haar measure, complete for this pitch's needs.**
  `Mathlib/MeasureTheory/Measure/Haar/` (Basic, Quotient, Unique,
  NormedSpace, OfBasis, …): Haar on locally compact groups, uniqueness
  up to scale, quotients — plus finite product measures
  (`MeasureTheory/Measure/Prod`). Stage 0's measure ($G^{\#\text{links}}$
  with product Haar) is *stock*, not infrastructure work.
- **Fourier analysis, full strength.** `Mathlib/Analysis/Fourier/`
  (FourierTransform, Inversion, LpSpace/Plancherel, PoissonSummation,
  Convolution, RiemannLebesgue). Nothing in Stages 0–2 waits on Fourier.
- **Manifolds and bundles — differential geometry yes, gauge theory
  no.** Smooth manifolds exist (`Mathlib/Geometry/Manifold/`); vector
  bundles have a **covariant-derivative API**
  (`Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Metric,
  Torsion,LeviCivita}.lean`). But: **no principal bundles** (file search
  for principal-bundle content in `Geometry/` returns nothing
  gauge-theoretic), **no gauge connections, no Yang–Mills action**
  (`git grep -i "yangMills|yang-mills"`: zero hits). Continuum Riemannian
  geometry is present; continuum *gauge* geometry is not.
- **Probability with the right bones.** Martingales
  (`Mathlib/Probability/Martingale/`), finite-dimensional Gaussian
  distributions (`Mathlib/Probability/Distributions/Gaussian/`),
  **projective limits of measures** —
  `Mathlib/MeasureTheory/Constructions/Projective.lean`
  (`IsProjectiveMeasureFamily`, `IsProjectiveLimit`, uniqueness) and the
  cylinder machinery (`Constructions/Cylinders.lean`,
  `ClosedCompactCylinders.lean`) built for Kolmogorov extension;
  **Prokhorov tightness** (`Mathlib/MeasureTheory/Measure/Prokhorov
  .lean`), Portmanteau, Lévy convergence; Gaussian projective families
  (`Mathlib/Probability/BrownianMotion/GaussianProjectiveFamily.lean`).
  This is real scaffolding for Stage 3's measure-side statements — the
  projective/tightness language exists even though no lattice measure
  has ever been fed into it.
- **Unbounded operators: as far as Pitch 3 found, no further.**
  `LinearPMap` and its adjoint (Pitch 3, §2.2 of its scoping) remain the
  whole shelf; the spectral API is bounded-only; essential
  self-adjointness remains priced from Pitch 3 (its sole remainder) —
  Stage 4 inherits that debt unchanged.

**LACKS (each verified by a grep returning nothing, or only the false
positives named):**

- **No statistical mechanics of lattices.** `git grep -il ising`
  returns three files, all substring accidents ("generalising",
  "Raising"); `partitionFunction|spinSystem`, `percolation`:
  **zero hits**. No spin systems, no partition functions, no cluster
  expansions (`clusterExpansion`: zero), no transfer matrices
  (`transferMatrix`: zero), no lattice Green's functions.
- **No gauge theory, lattice or continuum.** `wilson` in the gauge sense:
  `wilsonLoop|wilson loop` zero; `plaquette` zero; `elitzur|confinement`
  zero. Combined with the bundle finding above: the word "gauge" has no
  mathematical home in this Mathlib outside finite group representation
  theory (which exists and is stock: compact groups, Peter–Weyl
  fragments, Haar integration — Stage 0 consumes exactly that).
- **No OS / reflection positivity / Schwinger anything.**
  `osterwalder`, `reflectionPositiv`, `schwinger`: **zero hits each**.
  The OS axioms have never been stated in Mathlib, let alone verified
  or reconstructed.
- **No Minlos, no nuclear spaces, no measure on 𝓢′.**
  `minlos`, `NuclearSpace|nuclear space`: zero hits. (Bochner hits in
  MeasureTheory are the Bochner *integral*, not Bochner–Minlos.) The
  free field's Euclidean measure — the Gaussian with covariance
  $(-\Delta + m^2)^{-1}$ on $𝒮'(ℝ⁴)$ — cannot currently be constructed
  in this Mathlib; this is the single deepest infrastructure absence for
  the *analytic* route (§6.6), and `OsterwalderSchrader.lean` already
  names it.
- **No fundamental solutions.** `fundamentalSolution` over
  `Mathlib/Analysis/`: zero hits. No Green's function for $-\Delta + m^2$
  as a distribution — so even the free two-point Schwinger function is
  not available off the shelf (it is buildable analysis, priced as part
  of no stage here; it belongs to the free-field OS verification the
  corpus already carries as T5).
- **No renormalization group.** `renormalization` (case-insensitive)
  returns exactly one file, `Mathlib/MeasureTheory/Integral/
  PeakFunction.lean` — an unrelated usage. No blocking, no flow on
  coupling space, no Connes–Kreimer (the corpus's own
  `Renormalization.lean` is ahead of Mathlib here — combinatorially,
  §2.1 — and equally devoid of RG flow).

**Net assessment for pricing.** Stages 0–1 stand on *stock* Mathlib
(Haar, products, finite group representations, integration) plus corpus
patterns — new mathematics, no new infrastructure. Stage 2 needs no
infrastructure either, at its honest finite scope. Stage 3 is where the
absences concentrate: everything it needs (lattice stat-mech language,
OS statements with content, uniformity machinery applied to field
measures rather than probability measures) is either missing or
unapplied, *on top of* the mathematics being open in print. The two
facts compound; §6 prices them separately and does not let either hide
behind the other.

---

## 6. Routes and stages, priced

### The route decision (made once, here)

Two traditions exist for the continuum passage. The **lattice route**
(Wilson; Osterwalder–Seiler; Balaban): discretize exactly (gauge
invariance kept *exact* on the lattice), prove Euclidean properties at
finite $a$, control the $a \to 0$ passage. The **analytic route**
(Glimm–Jaffe's continuum constructions; OS-direct; in modern dress,
stochastic quantization): define the continuum Euclidean theory as
directly as possible and verify OS on it. §6.1–6.5 price the lattice
route stage by stage because it is the only one whose early stages are
*buildable at all* from where this corpus stands (§5: the analytic
route's first move — a measure on $𝒮'(ℝ⁴)$ — is blocked by the Minlos
absence before any dynamics appears); §6.6 prices the analytic route as
the comparison the discipline requires, and §6.7 records the
recommendation and its reasons.

### 6.1 Stage 0 — Finite lattice gauge theory: the birth certificate · **L**

*Goal.* A finite 4D lattice $\Lambda = \mathbb{Z}_N^4$ (sites
$x \in \mathrm{Fin}\,N^4$ or `Fin N → Fin 4` — presentation is a design
choice, disclosed in the module), link variables
$U : \text{links} \to G$ for $G$ a compact group (build order: $U(1)$
and $SU(2)$-shaped instances first if the general compact-group
statement costs more than its instances — a partial shape named in
advance), plaquettes $U_p$ as ordered products of four links, the
**Wilson action** $S_\beta(U) = \beta \sum_p (1 - \frac{1}{d}\,
\mathrm{Re}\,\mathrm{tr}\, U_p)$ and the **lattice measure**
$d\mu_\beta = Z^{-1} e^{-S_\beta} \prod_\ell dU_\ell$ (product Haar,
finite product — Mathlib stock, §5). Theorems:

- **Exact gauge invariance**: for every gauge transformation
  $g : \text{sites} \to G$, with $U^g_{(x,\mu)} = g_x U_{(x,\mu)}
  g_{x+\hat\mu}^{-1}$: plaquettes conjugate
  ($U_p \mapsto g_x U_p g_x^{-1}$), hence $\mathrm{tr}\,U_p$ and
  $S_\beta$ are invariant; the measure is invariant (Haar invariance
  link-by-link).
- **Observables**: Wilson loops $W_C = \mathrm{tr} \prod_{\ell \in C}
  U_\ell$ as functions on configuration space, gauge-invariant by the
  same conjugation-plus-trace argument; expectations
  $\langle W_C \rangle_\beta$ defined as integrals (finite, since the
  configuration space is compact).
- **Elementary exact computations** in the corpus's style: $\beta = 0$
  expectations (Haar orthogonality: $\langle W_C \rangle_0 = 0$ for
  nontrivial $C$ — character orthogonality, stock for compact groups),
  and the strong-coupling character expansion's first terms if they run
  clean (stretch, named as such).
- **Plaquette/energy identities**: the $a \to 0$ *formal* expansion of
  $U_p = \exp(i a^2 F_{\mu\nu} + O(a^3))$ is **NOT** a theorem of this
  stage (it is a statement about continuum fields); what the stage may
  prove is the finite algebraic identity layer (plaquette as product,
  adjoint action, trace identities). The classical-limit statement
  belongs to the header as context, labeled T5-context, never as a
  result.

*Consumes.* Mathlib only: Haar + products + compact-group representation
basics (§5); corpus-side, nothing — this stage starts a new module
family. (The corpus's classical gauge algebra is a *different* $G$
presentation — finite matrix groups; reusing `ClassicalYangMills`
conventions where cheap is a style choice, not a dependency.)
*Hard step.* Bookkeeping mass: links/plaquettes as dependent data over a
finite lattice, orientation/sign conventions, and the conjugation
computation done once, generally. No analysis. This is a campaign of
finite algebra and finite integration — the Γ-campaign weight class.
*Buys.* Removes the scope words **"no gauge sector"** — replaced by
"gauge sector at finite lattice, pure gauge, exact invariance."
Concretely: for the first time, the corpus contains quantized gauge
degrees of freedom, a gauge-invariant measure, and gauge-invariant
observables with proved expectations.
*Does not buy.* Anything with a limit in it. No Hilbert space (the
measure is a probability measure on configurations, not yet a quantum
theory), no Hamiltonian, no dynamics, no correlations with spacetime
separation structure beyond finite combinatorics, no continuum word of
any kind.
*Pre-kills (agree in advance; each is a way this stage gets faked):*
- **Gauge fixing.** Importing continuum perturbation theory's habit and
  fixing a gauge on the lattice (e.g., setting links to 1 along a tree)
  *as the definition of the theory* breaks the exact invariance that is
  this stage's entire point. (Gauge fixing as a *computational device
  inside a proof*, with invariance of the conclusion restored, is
  legitimate; as a definition it is a kill.) The lattice needs no gauge
  fixing: the configuration space is compact and the integral converges
  without it. Any Stage-0 module whose action is not proved invariant
  under *all* $g : \text{sites} \to G$ does not land.
- **Algebra-valued links.** Defining $U_\ell = \exp(i a A_\ell)$ with
  Lie-algebra-valued $A_\ell$ as the fundamental variable (the
  "non-compact" discretization) destroys exact invariance and (later)
  reflection positivity. Group-valued links or nothing.
- **$\beta$ read as physics.** $\beta$ is a bare lattice parameter.
  Sentences like "at physical coupling…" inside Stage 0 are killed on
  sight: no scale exists yet (§4).
*Transition accounting (into Stage 1).* Same level, richer structure —
correlations and positivity are properties *of the Stage-0 measure*, so
the distortion is zero and the price is purely additive content. The
first true transition in this pitch is Stage 1 → 2 (§3.2).

### 6.2 Stage 1 — Lattice correlations + reflection positivity · **L–XL** (clustering priced separately at XL)

*Goal, in three sub-stages with separate prices.*

- **1a — Correlation functions of gauge-invariant observables · M.**
  For gauge-invariant $F, H$ (functions on configuration space):
  $\langle F \rangle_\beta$, $\langle F H \rangle_\beta$, covariance;
  finite-volume and finite-spacing by construction. **Elitzur discipline
  built into the definitions**: correlations are only ever formed for
  gauge-invariant observables — gauge-variant correlators are not
  "small" or "formal", they are *undefined as observables* (their
  expectations vanish by Stage-0 invariance; the module proves the
  vanishing as a theorem for one-link-variant insertions, so the
  discipline is a result, not a comment).
- **1b — Reflection positivity for the Wilson action · L–XL.** Fix a
  reflection $\theta$ across a hyperplane between lattice sites
  (time-reflection for the transfer matrix; the statement form is
  action-level OS positivity): for every observable $F$ supported on
  the positive half-lattice, $\langle (\theta F) \cdot F \rangle_\beta
  \ge 0$ (complex form: $\langle \overline{\theta F} F \rangle \ge 0$).
  Proof route in print: the Wilson action splits across the reflection
  plane into $S = S_+ + S_- + S_0$ with the crossing plaquettes
  contributing a positive kernel — the standard checkerboard/sum-of-
  squares argument; the Boltzmann weight factorizes and the form is a
  sum of absolute squares. Corollary with content: the **OS scalar
  product** and the quotient/completion Hilbert space at finite
  $(a, L)$; the **transfer matrix** as a positive self-adjoint
  contraction on it — and with it, the first *Hamiltonian-shaped*
  object of the gauge sector, with a finite-volume lattice gap defined
  as $-\log$ of its second eigenvalue ratio — **named, in every module
  header, a lattice gap at fixed $(a, L, \beta)$ and nothing else**
  (§8's mandatory clause).
- **1c — Strong-coupling clustering · XL.** At small $\beta$: the
  cluster (character) expansion converges and correlations of
  gauge-invariant observables decay exponentially in lattice distance
  with a rate $m(\beta) > 0$ — the Osterwalder–Seiler theorem at the
  level of this corpus. This is the lattice mass gap *in its honest
  home*: strong coupling, fixed spacing. Its formalization is a
  combinatorial campaign of the heaviest class the ladder has priced
  (convergent expansion over connected lattice animals with
  uniformity in volume). Priced XL and **separately killable**: Stage 1
  lands without 1c (§8), with 1c recorded as the stage's exposed price.

*Consumes.* Stage 0 whole; Mathlib integration/probability stock;
nothing from the spectral-triple side of the corpus.
*Hard steps.* 1b's factorization bookkeeping across the reflection
plane (the proof is elementary and unforgiving: every plaquette must be
accounted on exactly one side or split correctly); 1c's expansion
(finite combinatorics at research-formalization weight).
*Buys.* The Euclidean package of a quantum theory *at finite lattice*:
a positive inner product (hence a Hilbert space), a transfer matrix
(hence a lattice Hamiltonian and a lattice notion of gap), and — with
1c — exponential clustering where the literature has it. Removes the
scope words "no positivity, no correlations" for the lattice theory.
*Does not buy.* Continuum anything; the transfer matrix is not the
continuum Hamiltonian, the lattice gap is not *the* gap, and $m(\beta)$
at strong coupling says nothing about $m$ along the tuning curve of
§4 (different regime — §3.3's "protected-but-unavailable" entry is
exactly this gap between 1c's theorem and §9's wall).
*Pre-kills:*
- **"Reflection positivity is automatic."** It is a property of the
  *action and the reflection*, proved for the Wilson action by its
  plaquette structure. Improved/anisotropic actions can fail it. Stage
  1b claims it for the Stage-0 Wilson action only, by proof, not by
  family resemblance.
- **Finite-volume spectral gap language.** The transfer matrix at
  finite volume has discrete spectrum; a "gap" there is automatic and
  meaningless without uniformity in $L$ and $a$. Headers carry the §8
  clause; any text quoting 1b's lattice gap without "$(a,L,\beta)$
  fixed" attached is in violation of this scoping.
- **Gauge-variant two-point functions as physics.** Killed by 1a's
  Elitzur theorem-form; proposals to "study the gluon propagator on
  the lattice" inside this pitch are out of scope by construction (they
  need gauge fixing — pre-killed at Stage 0 — and belong to a different,
  perturbative dialect).
*Transition accounting (into Stage 2).* The first priced distortion of
the pitch: coarse-graining a Stage-1 theory does **not** return a
Wilson-action theory — blocking generates every gauge-invariant
coupling consistent with the symmetries (longer loops, multi-plaquette
terms). The distortion's currency is the **growth of the coupling
space**: Stage 2 must either carry a general action (a function space,
with topology) or accept a truncation and say so. This is the
transition Jeff's principle points at, and its price is named here so
Stage 2 cannot pretend the Wilson form is preserved.

### 6.3 Stage 2 — One coarse-graining step, theorem-shaped · **M–L** (iterated flow priced XL, Balaban-scale)

*Goal.* Fix a blocking scheme at finite volume (e.g., $2{:}1$ block
spins on a sublattice, or decimation of alternate links — one scheme,
chosen and disclosed). Define the coarse-grained measure/action by
**partial integration**: for a coarse configuration $U'$, the blocked
Boltzmann weight is the integral of $e^{-S}$ over fine configurations
restricting (via the blocking kernel) to $U'$. Theorems targeted:

- The blocked object **is a positive measure** on coarse configurations
  with the **same gauge invariance** (blocking chosen covariantly ⇒
  invariance inherited — proved, not assumed).
- **Consistency of expectations**: for observables that factor through
  the blocking, $\langle F \rangle_{\text{fine}} = \langle F'
  \rangle_{\text{coarse}}$ exactly (definitionally true — the content
  is identifying which observables factor, and proving the identity for
  them; the *distortion* is precisely the observables that do not
  factor, and the stage's honesty obligation is to name that class).
- **Composition**: two successive blockings with the same scheme equal
  the corresponding $4{:}1$ blocking where the kernel algebra supports
  it (the semigroup property of the *measure* maps — true by Fubini;
  the stage proves it for the chosen kernel at finite volume).
- **The action-space statement**: the blocked action is exhibited as a
  general gauge-invariant action (a finite sum over loop functionals
  with induced couplings, at finite volume), with the induced couplings
  computed for the leading terms if tractable — making §6.2's
  transition accounting a theorem, not a remark: *the Wilson form is
  not preserved, here is its image*.
- **What a fixed point would mean, pinned**: a fixed point is a measure
  (equivalently, an action in the chosen function space) invariant
  under the blocking map; the statement is pinned with real content
  (the map is Stage-2's own), and the **Gaussian (free) fixed points**
  are identified where the kernel makes that a computation. No
  non-Gaussian fixed point is claimed or expected at finite volume:
  at finite volume the "fixed point" language is about the map, not
  about criticality — the header says so.

*Consumes.* Stages 0–1 (1b not required — blocking is measure-level;
1a's observable language is); Mathlib measure stock (kernels,
disintegration is present in Haar dir §5; probability kernels exist).
*Hard step.* The kernel/disintegration bookkeeping — conditional
measures on fibers of the blocking map — at finite volume this is
finite-product conditioning, real but tractable; and the coupling-space
computation's combinatorics.
*Buys.* The transformation of §3.2 exists *in the corpus* as a
theorem-grade object: one exact coarse-graining step with its
invariance, consistency, composition, and its distortion (coupling
growth + non-factoring observables) named in theorems. Removes the
scope words "no RG formalism" — replaced by "one blocking step,
formalized; the flow priced."
*Does not buy.* The flow: iterating with **estimates** (contraction in
coupling space, control of the generated couplings at every scale,
large-field control) is Balaban's program — priced **XL, research
scale**, and recorded here as this stage's exposed outer price, in the
same spirit as Pitch 2 priced its Task 7: named, bounded in words, not
promised. A fixed point statement without the flow's estimates buys no
continuum limit (§4, item 2: the theory is the trajectory, not the
point).
*Pre-kills:*
- **One blocking step called "the RG."** A single step is a map; the
  RG is the map plus its dynamics on coupling space. The header clause
  (§8) fixes the vocabulary.
- **Truncated flow called exact.** If couplings are truncated to a
  finite family (e.g., Wilson-only), the composition law of the
  truncated map fails in general — the truncated "RG" is an
  approximation scheme; presenting its fixed points as theorems about
  the theory is killed. The exact object is the measure map; couplings
  are coordinates, and coordinates may be truncated only with the word
  "truncated" attached.
- **$\beta$ from one step.** No "β-function" may be read off a single
  blocking: the β-function is a statement about the flow near the
  fixed point on the critical trajectory (§4) — Stage 2's finite
  statements do not contain it.
*Transition accounting (into Stage 3).* The passage from "iterated
blocking exists" to "the continuum limit exists" is the distortion
nobody has priced (§3.1): its currency is **uniformity** (§4 item 3) —
every estimate must survive $a \to 0$ along $\beta(a)$. Stage 3 exists
to state that debt in the corpus's own language; paying it is §9's
wall, in this pitch only as scaffolding.

### 6.4 Stage 3 — Continuum-limit scaffolding · **L** of scaffolding around an **XL, research-scale** core

*Goal — three deliverables, of deliberately different kinds.*

- **3a — The re-pin (M).** Replace `OsterwalderSchrader.lean`'s marker
  bundle with a statement carrying real content: Schwinger functions as
  a sequence $S_n$ of tempered distributions on $(ℝ⁴)^n$ (𝓢′ exists,
  §5) with E0 temperedness (growth bounds as conditions, not opaque
  Props), E1 Euclidean covariance under the Euclidean group $E(4)$
  (rotations/reflections of `EuclideanSpace ℝ (Fin 4)` + translations —
  group stock exists), E2 reflection positivity (as the operator/
  sesquilinear-form inequality, stated against a specified reflection),
  E3 symmetry, E4 clustering (decay of the truncated two-point function
  — which obligates defining truncated functions: more real content).
  And the matching **OS-in-the-limit target**: the theorem-*shaped*
  statement "the Stage-1 Schwinger functions (lattice correlators of
  gauge-invariant observables, rescaled) converge, along a tuning curve
  $\beta(a)$, to an $S_n$ satisfying E0–E4" — with every hypothesis the
  convergence needs (uniform bounds, uniformity of clustering) stated
  as **named hypotheses**, so the debt is a list, not a fog. This
  deliverable is statement engineering in the corpus's best tradition
  (the Rung-3/4 pins, but with content this time).
- **3b — The measure-side scaffolding (M–L).** The lattice measures as
  a projective family (volumes/spacings nested), in Mathlib's
  projective-limit language (§5: `IsProjectiveMeasureFamily`); tightness
  obligations stated (Prokhorov exists); the precise sense in which a
  continuum measure would be a projective limit / weak limit — and the
  honest note that the continuum *field* measure (on $𝒮'$-type spaces)
  additionally needs the Minlos-class infrastructure Mathlib lacks (§5),
  so 3b's scaffolding covers the *lattice-side* projective story
  completely and names the field-side gap instead of papering it.
- **3c — The analytic core (PRICED, not a deliverable).** Proving 3a's
  target: uniform-in-$a$ estimates along $\beta(a)$ for 4D Yang–Mills.
  Status in the world: **open** (Balaban: continuum existence at small
  bare coupling claimed in print, gap absent, large-field step
  criticized; nothing in Lean anywhere). A scoping that lists 3c as a
  task would be fraudulent; it is listed as the wall Stage 3's
  scaffolding *faces*, with its literature status pinned (the corpus's
  `BalabanRGProgram` pin, §2.1, is the standing summary).
  Sub-items that *are* formalization-shaped and may be split off by a
  future scoping: the free-field OS verification (needs Minlos-class
  infrastructure first — an infrastructure campaign of its own, XL,
  and the natural first tenant of any future "analytic infrastructure"
  pitch); scaling limits in **lower-dimensional or scalar toy models**
  where the mathematics exists in print (e.g., a lattice free field's
  continuum limit — the Gaussian case — as a *dress rehearsal* with a
  theorem at the end: priced L–XL, genuinely instructive, and the only
  Stage-3-shaped object with a known proof; it proves the *scaffolding*
  can carry weight without touching YM).

*Buys.* The pitch's aim becomes exact: the target is a statement with
content, the debt is a hypothesis list, the wall has a literature
address. Removes the scope words "continuum unformalized as a target"
— replaced by "continuum target pinned with content; existence priced,
research-scale, open in print."
*Does not buy.* The continuum theory. (Repeated because this is the
stage where language laundering historically happens: scaffolding is
not a limit, a statement is not a construction, a dress rehearsal is
not the play.)
*Pre-kills:*
- **Euclidean covariance from hypercubic symmetry.** The lattice's
  symmetry is the hypercubic group; $E(4)$ covariance of the limit is
  an *emergent theorem-obligation*, famously non-automatic. Any Stage-3
  text deriving continuum covariance from lattice symmetry by adjective
  is killed.
- **Pointwise limits of correlators called a theory.** Convergence of
  $\langle \cdot \rangle_{a}$ on a class of observables, without E0–E4
  in the limit (esp. reflection positivity surviving, temperedness),
  is not a Schwinger-function package and not a theory. The hypotheses
  of 3a's target are the claim; dropping one silently voids it.
- **The tuned curve treated as a knob.** $\beta(a)$ is forced by
  dimensional transmutation (§4 item 1); a "limit" taken at fixed
  $\beta$ or along an arbitrary curve is a limit of a different (or no)
  theory.

### 6.5 Stage 4 — Real Poincaré for the interacting continuum theory · **FRONTIER** (priced, not staged)

*What it would take, as a dependency list (each item priced or pinned):*

1. Stage 3c — a continuum theory exists (research-scale, open).
2. **OS reconstruction formalized** — the theorem that E0–E4 Schwinger
   functions yield a Wightman theory: Hilbert space from reflection
   positivity, vacuum, unitary Poincaré representation with the
   spectral condition, local fields. In print ~100 pages of hard
   analysis (analytic continuation to the extended tube,
   Bargmann–Hall–Wightman, edge-of-the-wedge). In this Mathlib: the
   prerequisites are absent at several points (no several-complex-
   variables tube machinery applied this way, unbounded-operator
   spectral theory bounded-only, §5). **XL, infrastructure-first** —
   and note it is a *theorem that exists*: unlike 3c, reconstruction is
   not open mathematics, only unformalized; it is the most expensive
   *honest* item in this section.
3. The reconstructed representation identified as *the* theory's —
   covariance of the constructed fields, not merely existence of some
   representation (part of reconstruction's full statement; listed
   separately because partial reconstructions in the literature stop
   earlier).
4. Free-side inputs for calibration and for the free comparison theory:
   Rung 7's remainders (§2.3) — strong continuity (**S–M**) and Fock
   packaging (**M**) — which Stage 4 does not consume mathematically
   (the interacting representation is not built from the free one) but
   which the program owes the ladder independently; listed so the
   shelf (§9) is complete.

*Pre-kill (the stage's reason for existing as a warning):* **"Poincaré"
claimed from any combination of** (a) the classical `PoincareGroup`
object (§2.1 — a group, not a representation of an interacting theory),
(b) Rung 9 Task 4's lattice translations (finite modes, diagonal phases),
or (c) the Rung 7 free one-particle invariance incl. boosts (free,
one-particle, measure-level). Each is a true theorem about a different
object. Their sum is not Stage 4, and the boost discharge of 2026-10-17
— this program's best continuum-side result — is the one most at risk
of being misquoted here, so the scoping names the risk while the ink
is fresh: *free one-particle Lorentz invariance of a measure* is three
walls away from *Poincaré covariance of an interacting continuum
theory*, and the walls are 3c, reconstruction, and identification, in
that order.

### 6.6 The analytic route, priced as comparison · **XL, no landing in sight**

*The route.* Skip the lattice: posit the continuum Euclidean theory
directly — a measure on gauge-field configurations (distribution-valued
connections) satisfying OS — or construct it by continuum methods
(Glimm–Jaffe-style continuum limits of regularized continuum theories;
stochastic quantization / regularity structures in modern dress).

*Its first wall arrives before its first theorem:* the configuration
space is a space of distributions, and even its **free** measure needs
Minlos-class infrastructure absent from Mathlib (§5) — the corpus's own
OS file names this as the reason the *free scalar* is unverified. Past
that wall: non-Gaussian continuum measures in 4D have no construction
by *anyone* by direct methods; the historical successes of the analytic
tradition (φ⁴₂, φ⁴₃, YM₂) all pass through lattice or
lattice-like approximations at the uniformity step — i.e., the
analytic route, pursued honestly, *re-imports the lattice route's
Stages 1–3 as subroutines*, at higher infrastructure cost and with the
exact-invariance asset surrendered (continuum regularizations —
dimensional, ζ-function, cutoff — break or deform gauge invariance or
reflection positivity in ways the lattice does not). The one place the
analytic route is strictly ahead: **its target language is the right
one** (Schwinger functions, OS, reconstruction) — which is why Stage 3a
adopts that language for the pins while the campaigns run on the
lattice.

*Price:* XL with no definable landing; recommended role: **target
language + future infrastructure pitch** (a Minlos/Gaussian-measure
campaign, XL, would serve the free-field OS verification first — the
honest first tenant).
*Kill criterion for the comparison itself:* if a future scoping
proposes the analytic route as primary, it must first price the
Minlos-class infrastructure and exhibit one continuum-regularized
construction in print, in 4D, whose uniformity step does not pass
through a lattice. None is known to this scoping.

### 6.7 Recommendation and its reasons

**Lattice route: Stage 0 (L) → Stage 1a/1b (M + L–XL) → Stage 2 (M–L)
as the pitch's campaigns; Stage 1c and Stage 3's scaffolding (3a/3b)
priced and sequenced as written; Stage 3c and Stage 4 priced as walls,
not tasks.** Reasons, in order of weight:

1. **Every input of Stages 0–2 exists** (Mathlib stock + corpus
   patterns, §5); the analytic route's first input does not.
2. **Exactness is the corpus's comparative advantage.** The program's
   entire asset is statements with no unpriced error term. The lattice
   is the only discretization that keeps the theory's defining symmetry
   *exact* — the one piece of protected metadata (§3.3) that is fully
   protected — and this corpus, of all corpora, should not trade exact
   invariance for analytic convenience.
3. **The pattern is proven in-house.** Concrete-first (Pitch 2's Route
   B, Pitch 3's Route A) has landed three campaigns in a row; every
   abstract-first detour in the program's history has been re-priced
   back to a concrete construction.
4. **The walls are honestly located on this route.** On the lattice
   route, the open mathematics is concentrated at exactly one place
   (3c: uniformity along the tuning curve) with a literature address
   (Balaban). On the analytic route the walls are distributed and the
   first one is infrastructure, which disguises research risk as
   plumbing.

---

## 7. Pre-agreed cuts and kill criteria

**NOT attempted in this pitch (pre-agreed):**

- **Stage 3c in any form claimed as progress.** The uniform-estimate
  core is open mathematics (§6.4); attempting it inside a build
  campaign would produce either a sorry with good PR or a theorem
  about a toy mislabeled as the wall. Toys are welcome under their own
  names (Stage 3c's dress rehearsals, §6.4) — the wall is not a toy.
- **Stage 4** beyond its dependency list (§6.5).
- **Dynamical matter on the lattice** (fermions/bosons coupled to
  Stage-0 links): a separate pitch. Pure gauge only. (Consequence
  stated plainly: the Clay problem quantifies over gauge groups for
  the *pure* theory in the Jaffe–Witten statement — matter is not owed
  by the statement; the restriction costs nothing against the target.)
- **Gauge fixing** as a definition (Stage 0 pre-kill), and with it all
  gauge-variant observable programs (gluon propagators and kin).
- **Continuum gauge fields via bundles** as an alternative Stage 0:
  Mathlib has the bundle/covariant-derivative shelf (§5) but no
  principal connections and no measure on connections; a "continuum-
  first gauge sector" module would be all markers. Killed as a route
  for this pitch (§6.6 covers the general form of this refusal).
- **Non-compact / algebra-valued link formulations** (Stage 0
  pre-kill).
- **Any use of `Renormalization.lean` (Connes–Kreimer) as RG
  evidence** (§2.1 warning). Perturbative combinatorics is a different
  subject from coarse-graining; this pitch will not blur them, and
  neither may any summary of it.

**Kill / shrink criteria (agreed in advance, so a PARTIAL cannot be
dressed up later):**

- If Stage 0's invariance package lands only for $U(1)$ (abelian)
  instances, the stage lands as **abelian lattice gauge theory** and
  every sentence about it carries the word "abelian"; the nonabelian
  package is recorded as priced. An abelian landing is a real landing —
  it is not Yang–Mills, and the word "Yang–Mills" may not appear in its
  verdict sentence.
- If Stage 1b's reflection-positivity factorization resists for the
  Wilson action as defined in Stage 0, Stage 1 lands as 1a only, and
  the pitch's landing sentence (§8) loses "positivity/Hilbert space/
  transfer matrix" — the failure is reported as a priced obstruction
  with the exact step named, per the Concrete.
- If Stage 2's composition law holds only definitionally (Fubini on
  the nose) with no computable coupling image, Stage 2 lands as
  *blocking defined + invariance/consistency stand; the action-image
  and composition content priced* — the pitch may not say "an RG step
  is formalized" in that shape; it may say "a blocking map is defined
  and its exactness properties stand."
- Any discovery, mid-campaign, that a "proved" Stage-0/1 statement
  used a hidden continuum input (a limit, a completion presented as
  finite, a measure on an infinite product presented as finite) voids
  the stage's verdict until repaired — the Rung-3 guardrail (§0 of
  that scoping) enforced retroactively.
- Stage 1c (clustering) and Stage 3's dress rehearsals are killable
  by Jeff's word or by friction, with the landing re-scoped per §8's
  PARTIAL shapes — never by silently dropping them from the report.

---

## 8. Landing definition — what "Pitch 4 STANDS" shall mean

**The maximal honest package:**

1. **Stage 0 stands whole**: finite lattice gauge theory — group-valued
   links, Wilson action, product-Haar measure, exact gauge invariance
   proved for all gauge transformations, Wilson-loop observables with
   the $\beta = 0$ package. (Nonabelian $G$; abelian-only is the named
   PARTIAL below.)
2. **Stage 1a + 1b stand**: gauge-invariant correlation functions with
   the Elitzur vanishing theorem; reflection positivity for the Wilson
   action with the OS scalar product, the finite-volume Hilbert space,
   and the transfer matrix — every gap-shaped statement carrying its
   $(a, L, \beta)$ labels.
3. **Stage 2 stands**: one blocking step with invariance, consistency,
   composition, and the coupling-growth (action-image) content — the
   distortion of §6.2's transition accounting exhibited as theorems.
4. **Stage 3a + 3b stand**: the OS target re-pinned with real content
   (E0–E4 as conditions on actual Schwinger-function data; the
   OS-in-the-limit target stated with its uniform hypotheses as named
   obligations); the lattice measures organized as a projective family
   with tightness obligations stated; the field-side (Minlos-class)
   gap named in the module headers it blocks.
5. All modules zero-sorry with headline axiom checks
   `[propext, Classical.choice, Quot.sound]`, per house standard, and
   every module carrying the mandatory header clauses below.

With 1–5 green, the program may say: **"Pitch 4 STANDS — the corpus
contains a finite lattice gauge theory with exact gauge invariance,
reflection positivity and a transfer matrix; one exact coarse-graining
step with its distortion exhibited; and the continuum target pinned
with content, its uniform-estimate obligations named. The continuum
limit itself, the interacting theory's Poincaré covariance, and the
mass gap are priced walls (§9), not results."** The sentence must
travel with §9 attached wherever the landing is announced; a landing
announcement without the wall list is a violation of this scoping.

**Mandatory header clauses** (to appear verbatim, or in wording Jeff
approves as identical in content, in *every* module this pitch
produces):

- *(finite-lattice discipline)* "Results in this module are about a
  finite lattice at fixed spacing and volume. Nothing here is a
  continuum result; the words 'continuum', 'ℝ⁴', and 'Poincaré' do
  not describe anything proved in this module."
- *(gap discipline)* "Any gap statement in this module is a lattice
  statement at the stated $(a, L, \beta)$. No continuum mass gap is
  claimed; a lattice gap transfers to the continuum only with
  uniformity in the spacing along the tuning curve, which is not
  proved here or anywhere in this corpus."
- *(gauge discipline)* "Gauge invariance here is exact invariance of
  a finite lattice action and measure under finite gauge
  transformations. It is not a continuum gauge theory, and this module
  contains no quantized continuum gauge field."
- *(RG discipline, Stage 2 and later)* "A blocking step is a map, not
  the flow; no β-function, fixed-point criticality, or continuum limit
  is stated or implied by anything in this module."
- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

**The most likely PARTIAL shapes** (named in advance):

- **PARTIAL-α (Stage 0 only):** "the gauge sector exists — at finite
  lattice, with exact invariance." Stages 1–3 priced as scoped. This
  alone discharges the pitch's first promise and is a respectable
  landing for one campaign.
- **PARTIAL-β (Stages 0 + 1a, 1b priced):** correlations and the
  Elitzur discipline stand; positivity is the exposed price; no
  Hilbert space, no transfer matrix may be mentioned as standing.
- **PARTIAL-γ (abelian):** any of the above with $G = U(1)$ only, the
  word "abelian" welded to every claim (§7).

**The single hardest priced step inside the landing** is Stage 1b's
reflection-positivity factorization: elementary in print, unforgiving
in formalization — every plaquette accounted across the reflection
plane, against an API (finite-product integration over half-lattices)
with no corpus precedent. Runner-up: Stage 2's coupling-image
computation. The hardest steps *excluded* from the landing are 3c and
Stage 4, priced in §6.4–6.5 and §9 — deliberately outside, as Pitch 2
excluded its Task 7 and Pitch 3 its Route C.

---

## 9. The priced shelf after Pitch 4 — the summit wall

Assume Pitch 4 stands whole (§8). What remains between the program and
the Clay statement, stated without drama and without minimizing:

1. **Uniformity along the tuning curve (Stage 3c) — the existence
   half.** Exponential clustering and OS control with bounds uniform
   in $a$ as $\beta(a) \to \infty$, at every scale, with large-field
   control: the content of Balaban's program and its open edges. In
   print: incomplete. In Lean: untouched. This is the wall on which
   the continuum theory's *existence* waits, and it is a wall of
   estimates, not of definitions — no scoping converts it into tasks;
   only mathematics does, and the mathematics is fifty years old and
   unfinished.
2. **The interacting continuum gap — the gap half, a further wall
   beyond existence.** Even granted (1) and a constructed theory:
   $\mathrm{spec}(H) \subseteq \{0\} \cup [\Delta, \infty)$ with
   $\Delta > 0$ must be proved *of that theory* — in Euclidean terms,
   exponential clustering of the continuum Schwinger functions with a
   positive physical rate, uniformly, which is (1)'s hardest clause
   promoted to the limit. No known argument in print proves it. The
   distance from "a continuum Yang–Mills theory exists" to "and it has
   a mass gap" is not a formality; historically it is the difference
   between the two halves of the problem's name, and both halves are
   in the statement (§1.1). Pitch 4 does not touch this wall; §8's gap
   clause exists so that nothing built under this pitch can be quoted
   as leaning on it.
3. **Full Wightman verification (the axioms half, made whole).** OS
   reconstruction formalized (Stage 4 item 2 — a theorem that exists
   in print, priced XL-infrastructure) *and* its output verified
   axiom-by-axiom for the constructed theory, including non-triviality
   (the limit is not Gaussian — §4 item 2's obligation, discharged
   last and hardest).

That is the shelf: three walls — uniformity, the gap beyond existence,
verification in full — behind a pitch that, standing whole, gives the
program a gauge sector, an exact passage-step, and a target with
content. The summit is not closer in the sense that matters (parts of
the official statement closed: **0**, before and after, §1.1). The
program is closer in the only sense it has ever honestly claimed: the
wall now has our own instruments leaning against it, every one of them
labeled with what it cannot do.

---

*Scoping ends. No Lean was written, nothing was built, nothing is
claimed. Awaiting Jeff's greenlight on the landing definition (§8),
on the pre-agreed cuts (§7: Stage 3c as task, Stage 4, dynamical
matter, gauge fixing, bundle-route Stage 0), and on the PARTIAL shapes
(α/β/γ) before any build order issues.*
