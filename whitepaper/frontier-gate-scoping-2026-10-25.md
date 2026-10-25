# THE FRONTIER GATE — a scoping charter for Items 3 and 4 (Stage 3c uniform estimates; Stage 4 continuum theory)

**Date:** 2026-10-25 · **Type:** paper charter only. No Lean is commissioned
by this document; every brick below is priced and fenced before any build.
**Commissioned by:** the state of the bench at 2026-10-25 — Stage 2
reconstruction is complete to the limit of the pinned Mathlib, and the
road map's remaining items are the two that have never had a gate paper:
Item 3 (Stage 3c, WALL) and Item 4 (Stage 4, FRONTIER).

**NO CLAIM.** Parts of any official Clay statement closed by anything
scoped here, even if every brick lands: **0**. Dials: **0/4**. Stage 1b-B
positivity at general `(G, ρ)` remains **OPEN** (exhausted-for-now, five
closures around it); U(1) at all `β ≥ 0` remains **T1** (Route C). This
charter touches neither label. Census at writing, per the S2-4(b)
dossier: 5,205 strict / 5,254 attribute-inclusive / 173 counted modules.

**Standing claim rule (restated, governs every section).** A claim on
`Δ` exists only when a proved theorem's statement is part of the official
statement — a 4D continuum Yang–Mills theory constructed, with `Δ > 0`
proved on *it*. Nothing in this paper is, implies, or renames such a
theorem. This paper's job is narrower and, the bench holds, necessary:
to state exactly what Items 3 and 4 demand, to mark precisely where
their statements can and cannot be *written down* in the corpus's
language today, and to price the first bricks that can honestly be
commissioned at that border. A border that is named exactly is not
crossed — but it is the only kind that ever gets crossed on purpose.

---

## 0. How this gate differs from the S2-0 gate

The S2-0 gate (2026-10-24) scoped a ladder whose every statement could
already be written in the corpus's own language; its kills were about
proofs failing. This gate scopes a *border*: on one side, statements the
corpus can formulate (and, in seats, has proved); on the other, Items 3
and 4, whose statements require language the corpus does not yet hold —
a spacing, a tuning curve, a limit, a continuum measure. The kills here
are therefore of two kinds, and the paper keeps them separate:
**formulation kills** (the statement cannot be written without new
language — a frontier fact, not a failure) and **proof kills** (the
statement is written and the proof route dies — a wall fact). Prices are
in the house scale S/M/L, with WALL (research-scale, open) and FRONTIER
(no language yet) used exactly as the gap-theorem queue uses them.

**Tier tags.** Every load-bearing statement below carries one:
**[T1]** landed, machine-checked, parent-verified · **[T2]** a
definition or convention adopted for a statement, not a theorem ·
**[T5]** vision/quarantine register, asserted as nothing · **[WALL]**
research-scale, named in the queue's §2 · **[FRONTIER]** no corpus
language exists for the object named.

**The border, in one table.**

| Item | What it demands | Can the *statement* be written today? | Tier of the demand |
|---|---|---|---|
| 3 — Stage 3c | A floor on the transfer gap, uniform in volume and uniform along the tuning curve as spacing `a → 0` | At the U(1) seat: yes, as a formulation brick (FG-1, §2.1) — modulo dependency D-1. At general `(G, ρ)`: no — the gap it would bound is itself only conditional (§1.1) | [WALL] (queue W1) |
| 4 — Stage 4 | A continuum theory: continuum measure, local algebras, reconstructed space and Hamiltonian, as a limit of the lattice theories | No. The corpus holds zero continuum objects and zero renormalization-group content (§1.2) | [FRONTIER] (queue W2) |
| 5 — `Δ > 0` | The gap, proved on the Item-4 theory | No — it is the claim itself, and Items 3+4 are jointly its prerequisites (§1.3) | the claim |

---

## 1. The border, pinned

The corpus's finite theory lives on one geometry: the torus
`Fin 4 → ZMod N`, `N` even, gauge group `G` with Haar probability
measure `μG`, unitary representation `ρ`, coupling `β` real — and, the
Stage 2 charter's own fence, **no limit of any kind**: no lattice-spacing
limit, no volume limit, no renormalization. Every Item-3/Item-4 word
below is measured against that record. Three absences do most of the
pinning, so they are stated first:

- **There is no spacing.** The lattice is combinatorial (`ZMod N` has no
  metric scale); no `a`, no physical volume, and no `β`-as-function-of-
  resolution appears anywhere in the record. [T1 — absence verified
  across the bounded reading: the Stage 2 charter §1/§3(iii), the
  gap queue, the Q12 dossier.]
- **There is no tuning curve.** Nothing in the record states how `β`
  must move with `N` to hold physics fixed; that is renormalization-group
  content, and the corpus holds none (the module named
  `Renormalization` is Connes–Kreimer combinatorics, not RG flow —
  standing record; flagged TO VERIFY against the module header,
  Appendix B #2). [T1 as absence; the parenthetical is context-supplied]
- **There is no continuum object.** The only continuum-named
  declaration in the corpus is `blockedQ2_continuumLimit`
  (`BlockedQuestions`, [T5], quarantined): an existence statement over a
  `ContinuumLimitData` structure whose content field `recoversLocality`
  is an uninterpreted `Prop`. The queue's own words: a formal discharge
  "would not discharge the question." It is a receipt marking the
  frontier, not an object on this side of it. [T1 — the quarantine is
  landed record, gap queue §4 X2]

### 1.1 Item 3 — Stage 3c: the uniform floor, stated exactly

**The quantity.** At fixed `(G, ρ, β, N)`, the transfer operator `T_β`
on `osSpace` has, where Q12's machinery applies, a spectral gap
`δ(β, N)`: the distance from the vacuum eigenvalue `1` to the rest of
the spectrum. What Q12 landed about it, exactly:

- **Spectral discreteness [T1].** At even `N`, eigenvalues are real
  with `|λ| ≤ 1`, eigenvectors for `λ ≠ 1` are `⊥ Ω`, and for every
  `ε > 0` only finitely many spectral points have `|λ| ≥ ε`
  (`transfer_spectrum_finite_above`). This is per-instance: it controls
  no dependence on `β` or `N`.
- **The gap, conditional [T1 as a conditional].**
  `transfer_gap_of_formPos`: *given* the named package
  **TransferFormPos** — the OS form positive on **all** of `osSpace`,
  plus vacuum simplicity — there is `δ > 0` with `|λ| ≤ 1 − δ` for every
  spectral `λ ≠ 1`. The Q12 dossier's fence, verbatim in substance:
  TransferFormPos on all of `osSpace` *is* the open Stage 1b-B
  positivity content in operator form. At general `(G, ρ)` the gap is
  exactly as strong as Item 1's open statement.
- **The gap at `β = 0`, exact [T1].** `transfer_gap_zero`: the spectrum
  of `T₀` lies in `{0, 1}` and `δ = 1` — at zero coupling `T₀` is
  exactly the vacuum projection. Compactness likewise is unconditional
  at `β = 0` and conditional elsewhere (on **HDen**, the two-slice law
  having an `L²` density w.r.t. the product of its marginals);
  separability of `osSpace` rides as an explicit hypothesis in the
  compactness corollaries. [T1, Q12 dossier fences 3–4]

**The demand.** W1 (gap queue §2) states Item 3 in the sources' terms:
a gap **"uniform in volume and coupling along a continuum trajectory"**;
general-`β` decay/clustering with a uniform-in-volume gap `m(β) > 0` in
Osterwalder–Seiler form; in the floor-to-ceiling blueprint's words, "a
spacing-uniform gap/observable bound that survives `a → 0`… without it
no vertical member reaches Beam A." Pinned into the corpus's language,
the demand is two uniformities, and they must not be conflated:

- **(U-vol) Volume uniformity at fixed coupling [WALL].** For each
  fixed `β` in the trajectory's range, `inf` over even `N` of
  `δ(β, N)` is positive — the fixed-volume gap does not close as the
  torus grows. Nothing landed speaks to the `N`-dependence of `δ` at
  all; Q12's discreteness is one `(β, N)` at a time.
- **(U-traj) Trajectory uniformity as `a → 0` [WALL].** Fix a physical
  volume and read `N` as resolution, `a = 1/N` in unit-volume units
  [T2 — a convention the formulation brick must adopt and name; the
  corpus fixes neither]. The transfer operator advances one lattice
  step, i.e. `a` of physical time, so the physical mass is
  `m = −log|λ₂| / a ≈ δ / a`. The demand is a floor in *physical*
  units along a tuning curve `β(N)`:
  `inf` over the trajectory of `N · δ(β(N), N)` `> 0` — equivalently
  `δ` may close as `a → 0`, but at most linearly in `a`, with the ratio
  bounded below. A `δ` constant in lattice units gives `m → ∞`
  (decoupling — the wrong limit); a `δ` closing faster than `a` gives
  `m = 0` (a gapless continuum). Item 3 is exactly the exclusion of
  the second failure along the curve that Item 4 needs.

**Where the statement is formulable today — by seat.**

- **General `(G, ρ)`: NOT formulable as a standalone statement.** The
  quantity `δ(β, N)` it would bound exists today only inside the
  TransferFormPos hypothesis (and compactness inside HDen). A uniform
  floor over a conditional quantity is a conditional about a
  conditional; writing it as an Item-3 statement would smuggle Item 1.
  The honest general-`(G, ρ)` entry is: *formulable only as a clause
  inside the TransferFormPos hypothesis package* — which is to say,
  not formulable as Item 3 at all until Item 1 moves. [WALL, by
  dependency on OPEN Item 1]
- **The U(1) seat: formulable, as a formulation brick (FG-1, §2.1) —
  with one dependency pinned, not hidden.** Positivity at the circle
  seat is [T1] at every `β ≥ 0` (Route C, `osForm_circle_nonneg`), and
  the Stage 2 engine is hypothesis-free there (S2-3 STANDS IN FULL).
  But Q12's fence 2 records that welding Route C's positivity up to
  TransferFormPos **on all of `osSpace`** "is S2-2-shaped work and was
  not attempted" — as of Q12. Stage 2 has since landed, on the engine's
  slice algebra `𝔸_slice`. Whether the landed state discharges
  `osSpace`-wide TransferFormPos at the U(1) seat is **not settled by
  the record this gate was written from** (Appendix B #1 — dependency
  **D-1**). Both branches are live: if D-1 resolves *landed*, then
  `δ_U(1)(β, N)` is an unconditional quantity at every `β ≥ 0` and
  FG-1 formulates (U-vol) and (U-traj) outright; if D-1 resolves
  *unlanded*, FG-1 formulates them under the named hypothesis
  "TransferFormPos at U(1)" and its first deliverable is the weld
  brick that would discharge it. Either way the *statement* can be
  written at this seat and at no other. No other seat qualifies:
  `β = 0` at general `(G, ρ)` has `δ = 1` exactly [T1], so a "uniform
  floor" there is already a theorem — and a vacuous one for Item 3,
  since `β ≡ 0` is the degenerate theory (`T₀` the vacuum projection,
  `Ĥ₀ = 0`): it is uniform precisely where nothing interacts, and no
  tuning curve to an interacting continuum passes through it as its
  constant trajectory. The gate records this as the **β = 0 shadow of
  uniformity: T1, true, and useless at this border** — any formulation
  that does not fence its trajectories against the degenerate constant
  reading has stated nothing.
- **Formulable ≠ true.** One piece of outside-corpus context, flagged
  as such [T4 — textbook physics, not a corpus result]: 4D lattice
  U(1) gauge theory has a Coulomb phase whose continuum limit is
  expected to be a *free photon* theory — gapless. A uniform floor at
  the U(1) seat along a trajectory entering that phase would then be
  **false**, however cleanly formulated. This does not demote FG-1 —
  a statement whose truth is doubtful is exactly the kind a gate
  should force into the open, with its kill pre-registered — but it
  forbids any drift from "the U(1) statement is written" to "Item 3
  is underway at U(1)". The proof of (U-vol)/(U-traj) at any seat is
  [WALL] (W1 prices Stage 3c research-scale, open; the in-print
  analogue is Balaban-scale and the mass gap is absent from it).

### 1.2 Item 4 — Stage 4: what a continuum object would be here

W2 (gap queue §2) names the gap: "a measure on continuum gauge fields;
local algebras (Type III₁ in the continuum); OS reconstruction outputs
in the continuum (schema only in the re-pin; lattice shadows all
stand); real Poincaré for the interacting continuum theory." Price, in
the source's own word: **FRONTIER** — the Landing Pad's Span (c) is
"quarantined… No span priced; the pad records the quarantine, it does
not lift it." Pinned against the corpus, a continuum object in this
program's language would have to be *all* of the following, and the
corpus today holds *none* of them:

1. **A limit construction.** A specified sense in which the finite
   theories (Gibbs measures on `G`-valued configurations over
   `Fin 4 → ZMod N`) converge as `a → 0` along a tuning curve — a
   projective/weak-limit measure on continuum gauge fields, or an
   algebraic limit of the observable algebras with their OS data.
   Blocked upstream by §1.1's absences: no spacing, no tuning curve,
   no RG statement of any kind. The finite measures are finite
   products of Haar measure; no projective family, no consistency
   condition, no limit measure is constructed or even defined in the
   record. [FRONTIER]
2. **Surviving OS data.** Reflection positivity and the state in the
   limit, feeding a continuum reconstruction (the Stage 2 outputs —
   space, vacuum, `T̂`, `Ĥ` — have continuum analogues only as a
   *schema*, per W2). The finite reconstruction is complete at fixed
   volume [T1, Stage 2 dossiers]; nothing in it is a statement about
   a limit. [FRONTIER]
3. **Local algebras of continuum type — the Type III marker.** The
   finite theory's bookkeeping leans on a trace-shaped state:
   `ω(F) = ∫ F d(gibbsMeasure)`, `ω(1) = 1`, finite Gibbs weights,
   trace-class transfer machinery at fixed volume. W2 names the
   continuum local algebras **Type III₁** [T1 — the naming is landed
   record, gap queue W2]. The frontier content, stated as standard
   theory [T4]: a Type III factor admits **no faithful trace** — the
   continuum theory's local algebras cannot carry the finite theory's
   trace-based bookkeeping at all; the loss of the trace is not a
   technicality to be patched but the marker that the continuum
   object's *kind* differs from every object the corpus holds. Any
   future Item-4 brick whose statement quietly assumes a trace on a
   local algebra has mis-stated its target, and this gate pre-registers
   that as a formulation kill (§3).
4. **Continuum symmetries.** Real Poincaré for the interacting
   continuum theory (W2) — the lattice theory's discrete translations
   (whose one-step operator is `transferOp`/`T̂`) have no continuum
   group action to converge to in the record. [FRONTIER]

**What is *not* missing** — pinned so the frontier is not overstated:
the corpus's fixed-volume theory is complete at its seats (Stage 2);
the finite spectral machinery (Gram criterion, Route C, Q12 compactness
and discreteness, Q13's closed form of `κ_p`) is landed [T1]. Item 4's
frontier is not a gap in the finite theory. It is the absence of the
*passage* — and of the language a passage would be stated in.

### 1.3 The interlock, and Item 5

Items 3 and 4 are jointly necessary and separately insufficient, and
the gate pins why, because the road map's numbering can make them look
independent:

- **Item 4 without Item 3** can deliver a continuum theory that is
  **gapless**: `δ(a) > 0` at every finite `a` is compatible with
  `δ(a)/a → 0`. A constructed limit with no uniform floor is a
  construction of *a* QFT, not of the massive one.
- **Item 3 without Item 4** is a family of lattice estimates with no
  continuum object to inherit them: uniform floors on a sequence of
  finite theories whose limit has not been constructed bound nothing
  in any continuum theory.
- **Item 5** — `Δ > 0` on the Item-4 theory, i.e. `0` isolated in the
  spectrum of the continuum `Ĥ` with the vacuum its unique ground
  state below `Δ` — is the official statement's core. Under the
  standing claim rule it is not approached by accumulation: it exists
  when a proved theorem states it, on a constructed theory, with the
  floor inherited through the limit. Until then: **0 parts closed,
  dials 0/4**, at every seat, without exception for effort spent.


---

## 2. First statable bricks at the border, priced

Each brick: **consumes / delivers / price / kill**, kills pre-registered
in §3 and repeated on the brick. "Statable" is the operative word: a
brick belongs in this section only if its *statement* can be written in
the corpus's language today. Proof content is priced separately and
honestly — most of what follows is formulation, and the gate says so.

**Dependency D-1 (not a brick — a question two bricks stand on).**
Does the landed Stage 2 state discharge TransferFormPos on **all** of
`osSpace` at the U(1) seat? Record: Q12 fence 2 (not attempted, as of
2026-10-24) vs S2-3 STANDS IN FULL (engine hypothesis-free at U(1), on
`𝔸_slice`). The bounded record does not settle whether `𝔸_slice`-seat
discharge is `osSpace`-wide discharge. Resolving D-1 is a *reading*
task inside FG-1's dependency audit, priced inside FG-1; if the reading
finds the discharge absent, the weld that would supply it is a separate
brick (Stage-2-shaped, priced on its own charter, not here).

### 2.1 FG-1 — the U(1)-seat uniform-estimate FORMULATION brick

- **Consumes:** Q12's spectral package at the circle seat
  (`transfer_spectrum_finite_above`, `transfer_gap_of_formPos`,
  `transfer_gap_zero` as the degenerate fence); Route C positivity
  [T1]; the S2-3 U(1) discharge [T1]; W1's demand statement.
- **Delivers (paper; a Lean statement module is the priced option, not
  the default):**
  1. The dependency audit resolving **D-1**, with the branch taken
     named on the paper's face;
  2. The adopted trajectory language [T2]: unit-physical-volume
     reading `a = 1/N`; the class of admissible tuning curves
     `β : {even N} → ℝ≥0` the statement quantifies over, **with the
     degenerate constant trajectory `β ≡ 0` fenced out by name** (the
     β = 0 shadow, §1.1) and with no curve asserted to give a limit —
     the statement is about floors, not about convergence;
  3. The statements **(U-vol)** and **(U-traj)** at the U(1) seat, in
     the corpus's own measure/spectrum language, each labeled with its
     hypothesis status exactly as D-1 resolves (unconditional
     quantity, or under the named hypothesis "TransferFormPos at
     U(1)"), and each carrying on its face: *formulation only — no
     proof is scoped, priced, or implied by this brick*;
  4. A truth-status note per statement: at `β = 0` (U-vol) is [T1] and
     vacuous; at `β > 0` both statements are **open**, with the [T4]
     Coulomb-phase doubt recorded against (U-traj) (§1.1).
- **Price:** **S** (paper formulation + dependency audit). **M** if
  commissioned with the Lean statement module (statements formalized
  and type-checked; still no proof).
- **Kill K-FG-1** (§3): the gap quantity at U(1) cannot be defined
  without first discharging a hypothesis that is itself Item-1-shaped
  *at the circle seat* (i.e. D-1 resolves to "Route C's positivity
  does not reach the quantity Q12's gap is about, even conditionally
  as packaged") → FG-1 lands as formulation-under-named-hypothesis
  only, labeled PARTIAL, with the missing weld named as the next
  brick; if even the trajectory/`N`-family language cannot be written
  without new measure machinery (projective families), the kill is
  total: the formulation moves to the FRONTIER side of the border and
  this gate is re-issued with Item 3 at U(1) reclassified.

### 2.2 FG-2 — the hand-built unbounded-operator theory (a project, not a brick)

**Placement, stated before scope:** FG-2 completes **Stage 2's**
residue — the operator seat of S2-4 half (b). Its objects are
fixed-volume. **It does not advance Item 3 or Item 4 by any amount**,
and it is scoped here only because the S2-4(b) dossier names it as
Stage 2's exact remaining residue and because a builder glancing at
the border could mistake it for frontier work. It is a parallel shelf:
commissionable on its own charter, irrelevant to the claim's road
except through Stage 2's completeness. The dossier's verdict on the
residue is quoted so the project is not oversold: both remaining items
"await Mathlib API that does not exist in the pinned version, or a
hand-built unbounded-operator theory (**a new project, not a
brick**)."

- **The residue, exact [T1 — S2-4(b) dossier].** (i) The Friedrichs
  construction from the landed closed form `sliceHamFormC` on the
  completed space `sliceHilbertSpace` — a self-adjoint `Ĥ ≥ 0` with
  `‖Ĥ^{1/2} x‖² = sliceHamFormC x` on the form domain; (ii) the
  semigroup identity `exp(−Ĥ) = T̂_c` in an unbounded-operator sense.
  The named stops: Mathlib v4.35.0-rc3 has **no Friedrichs
  representation theorem** (no "Friedrichs" in the library) and **no
  unbounded exp/semigroup theory** (no "Hille"); continuous functional
  calculus covers bounded normal elements only; and a bounded
  `exp(−Ĥ)` is always invertible while `−log` is unbounded at spectrum
  point `0` — so rung (3) has, in the dossier's words, "no honest
  sense" in the pinned library. The landed ground it builds on:
  `sliceCompletedForm_package` (19 clauses — defect, term positivity,
  approximants `q_K`, `sliceHamFormC` as an `ℝ≥0∞` supremum, the
  domain submodule with its `≠ ⊤` characterization, energy forms
  `Q_n` with `Q₁ = q₁`) and `sliceOperator_package` (completion,
  `T̂_c` a self-adjoint contraction of bound 1, vacuum fixed) [T1].
- **FG-2a — FIRST BRICK: closedness of the landed form (L).**
  Consumes: `sliceCompletedForm_package`; the S2-5 weld's interface
  clause (`Q₁` is the weld's norm defect:
  `sliceEnergyForm 1 x = ‖x‖² − ‖W x‖²` [T1]).
  Delivers: the form domain `sliceHamFormDomainC` equipped with the
  form inner product (the form's polarization plus the ambient inner
  product), proved a **Hilbert space in the form norm** — i.e.
  `sliceHamFormC` is a *closed* form in the representation theorem's
  sense — with the inclusion into `sliceHilbertSpace` continuous and
  dense-range where the record supports it, every unsupported clause
  named rather than assumed. This is the hypothesis the Friedrichs
  construction consumes; landing it converts FG-2b from "awaiting
  API" to "buildable, at a price."
  Price: **L** (analysis formalization; the approximant/supremum
  construction must be shown to interact correctly with form-norm
  completeness, and no part of that is in the library).
  Kill K-FG-2a (§3): an exhibited form-norm Cauchy sequence in the
  domain whose ambient limit lies outside the domain, or inside it
  with a different form value → the landed form is **not closed**;
  the Friedrichs route *from this form* dies (the form seat of S2-4
  stands untouched — closedness was never among its clauses), and
  FG-2 re-scopes to a closability/closure brick or dies as a project.
- **FG-2b — the Friedrichs operator (named, unpriced beyond L–XL).**
  Consumes FG-2a. Delivers a self-adjoint `Ĥ_F ≥ 0` on
  `sliceHilbertSpace` whose form is `sliceHamFormC`, with
  `Ĥ_F Ω = 0`. Requires, beyond FG-2a, the Riesz/representation step
  for the form's associated operator on its domain — none of it in
  the pinned library. Recorded here so its absence is a named shelf
  item, not a surprise; priced only when FG-2a lands and shows what
  the step actually costs.
- **FG-2c — the semigroup identification (named, XL-flavored).**
  Consumes FG-2b. Delivers `exp(−Ĥ_F) = T̂_c` in a named
  unbounded-operator sense — which itself must first be *built*
  (Hille–Yosida or an equivalent resolvent theory is absent from the
  library), and the identification `Ĥ_F = −log T̂_c` argued through
  the form, not through a bounded functional calculus that cannot
  see spectrum point `0`. This is the project's honest long pole and
  the reason the S2-4(b) dossier prices the whole residue as a
  project, not a brick.

### 2.3 The Q12 → uniformity connector — NONE EXISTS (explicit)

The gate was asked to find, in the bounded reading, a brick connecting
Q12's spectral discreteness toward uniformity, or to say plainly that
none exists. **None exists.** The reading, itemized so the absence is
auditable:

- `transfer_spectrum_finite_above` [T1] is a per-`(β, N)` finiteness:
  the number of spectral points above `ε`, and any bound on them, is
  uncontrolled as `β` and `N` vary. Uniformity *is* control of that
  variation; no landed statement bounds it.
- The gap `transfer_gap_of_formPos` [T1-conditional] produces *a*
  `δ > 0` from a hypothesis package; neither the statement nor its
  proof shape in the record carries a modulus — no function of
  `(β, N)` bounds `δ` below, and extracting one would be a new proof,
  not a corollary.
- Compactness at general `β` rides on **HDen**, an unquantified
  density hypothesis: nothing landed bounds the density, the
  Hilbert–Schmidt norm `‖K‖₂`, or the finite-rank tail rates in terms
  of `(β, N)` — the quantities any uniformity argument would have to
  feed on.
- The β = 0 point is exact (`δ = 1` at every `N` [T1]) and is the
  *only* uniformity-shaped landed fact anywhere near the border —
  the β = 0 shadow of §1.1: true, uniform, and about the degenerate
  theory. It connects to Item 3 the way a streetlight connects to
  the road past the town: it marks where the lit part ends.
- What *would* connect them is therefore not a brick but the WALL
  itself (W1/W3): quantitative compactness — `(β, N)`-explicit
  Hilbert–Schmidt and tail bounds — plus a clustering/decay input,
  neither of which exists in the record in any form. The gate records
  the connector's seat as **empty**, and FG-1 (§2.1) is deliberately
  scoped to consume Q12's gap as a black box precisely because no
  finer interface exists.

---

## 3. Kills and walls, named

### 3.1 Pre-registered kills (this gate's bricks)

| Kill | Fires when | Consequence, exactly |
|---|---|---|
| **K-FG-1** (formulation) | D-1 resolves to: Q12's gap quantity at U(1) is unreachable from Route C positivity even as packaged; or the trajectory language needs projective measure machinery | PARTIAL (formulation under named hypothesis, weld named as next brick); total if the language itself is unwritable — Item 3 at U(1) reclassifies to FRONTIER and this gate is re-issued |
| **K-FG-1-vacuity** | An FG-1 draft states a floor whose only verified instance is the degenerate trajectory (`β ≡ 0`, or trajectories eventually `0`) | The draft is rejected as stating nothing; the trajectory class must be re-fenced before any landing. Pre-registered so the β = 0 shadow can never be landed as progress |
| **K-FG-2a** | Exhibited form-norm Cauchy sequence escaping the domain, or converging to a point with a different form value | Friedrichs-from-this-form dies; S2-4 form seat stands; FG-2 re-scopes to closure theory or terminates as a project |
| **K-FG-2 (project)** | FG-2b's representation step is found to need, inside the proof, a spectral theorem for unbounded operators equivalent in strength to the conclusion | The project is circular as scoped and dies at full rank; the residue returns to "awaiting Mathlib API" |
| **K-Item4-language** (standing) | Any future Item-4-facing statement assumes a faithful trace on a continuum local algebra, a continuum measure as a finite product, or a tuning curve as given | The statement is mis-stated against §1.2's pinning and does not land, whatever its proof state |

Kills fire at the same speed as landings, at full rank, under their own
names — the house rule, restated for this border because formulation
kills are easier to soften than proof kills, and may not be.

### 3.2 WALL vs FRONTIER vs merely unbuilt

| Object | Class | Ground |
|---|---|---|
| FG-1 formulation at U(1) (incl. D-1 audit) | **Unbuilt — queue-able** | §2.1; statement writable today |
| D-1 weld (TransferFormPos on all of `osSpace` at U(1)), if D-1 resolves unlanded | **Unbuilt — queue-able** | Stage-2-shaped; Q12 fence 2 + S2-3 record |
| FG-2a (closedness of `sliceHamFormC`) | **Unbuilt — queue-able** | §2.2; consumes only landed packages |
| FG-2b, FG-2c | **Unbuilt — project shelf** | named, deliberately unpriced beyond L–XL |
| Proof of (U-vol) or (U-traj) at any seat, `β > 0` | **WALL** | W1: Stage 3c, research-scale, open; Balaban-scale analogue |
| Quantitative compactness (β,N-explicit HS/tail bounds); clustering body | **WALL** | W1; W3 (1c-proper, XL, parked) |
| Stage 3c as a whole | **WALL** | gap queue §2 W1 |
| RG content: β-function, tuning-curve existence, running coupling | **FRONTIER** | §1.2(1); zero RG content in the record |
| Continuum measure on gauge fields; projective limit of the finite theories | **FRONTIER** | W2 |
| Continuum local algebras (Type III₁), trace-free bookkeeping | **FRONTIER** | W2; §1.2(3) |
| Continuum OS reconstruction; real Poincaré (interacting) | **FRONTIER** | W2 |
| `Δ > 0` on a continuum theory | **The claim** — not a class | §1.3; standing claim rule |

Two classifications deserve their reasons on the record. **Stage 3c is
a WALL and not a FRONTIER** because its statement *can* be written —
§1.1 writes it, at the U(1) seat outright and at general `(G, ρ)`
inside its hypothesis — and the in-print literature contains
research-scale analogues; what is missing is a proof of research
scale, not a language. **Stage 4 is a FRONTIER and not a WALL**
because no statement in the corpus's language picks out its object:
the one continuum-named declaration is a quarantined [T5] receipt with
an uninterpreted content field, and every component of §1.2's spec —
limit, measure, algebra type, symmetry — lacks corpus language, not
merely corpus proof. Confusing the two classes is how road maps rot;
this gate's tables exist to prevent it.

### 3.3 What this gate does not do

It does not re-open Item 1 (1b-B stays OPEN, exhausted-for-now; the
chessboard/cluster discharge paths named in the Stage 2 charter remain
Item 1's business, not this gate's). It does not commission anything —
commissioning is Jeff's word, as with S2-0. It does not move any dial,
soften any label, or promote any [T5] object — `blockedQ2` remains a
quarantined receipt after this paper exactly as before it.


---

## 4. The recommended first step

**Commission FG-1 — the U(1)-seat uniform-estimate formulation brick,
paper form, price S** (M if the Lean statement module is wanted in the
same commission). One brick, named: *the formulation of (U-vol) and
(U-traj) at the circle seat, with the D-1 dependency audit on its
face.*

Why this one, of everything in §2:

1. **It is the only Item-3 work whose statement exists today.** Every
   other seat fails at formulability (§1.1), and Item 4 fails at
   language (§1.2). FG-1 is the entire intersection of "at the
   border" and "writable now."
2. **Its dependency audit does double duty.** Resolving D-1 either
   retires the last named fence between Q12 and the Stage 2 engine
   (if the `osSpace`-wide discharge is already in the landed state)
   or isolates the exact weld brick that Stage 2's record left
   ambiguous — a fact the bench needs regardless of Item 3.
3. **It converts a WALL paragraph into statements with kills.**
   After FG-1, W1 is no longer only a dossier paragraph: it is two
   named statements, at a named seat, with hypothesis status and a
   vacuity fence, against which any future estimate work — ours or
   the literature's — can be checked. That is what gates are for.
4. **It cannot be oversold, because its fences are pre-registered.**
   K-FG-1 and K-FG-1-vacuity fire on the two ways this brick could
   fake progress (hypothesis smuggling, degenerate-trajectory
   triviality), and §1.1's truth-status note is part of its
   deliverable, not a caveat to be dropped at ship time.

**The honest verdict that accompanies the recommendation:** the
correct next step at this border is a **formulation brick only**. No
proof brick at Item 3 is commissionable on the current record (the
proof content is [WALL], research-scale, and at the one formulable
seat its central statement is under a recorded [T4] doubt); no brick
at Item 4 is commissionable at all (there is no language to state one
in). FG-2a is a legitimate parallel commission for a builder whose
seat is Stage 2's completeness rather than the road — priced L,
killed cleanly by K-FG-2a — but it is not a step toward Items 3/4 and
must never be reported as one. If only one brick is commissioned
tomorrow, it is FG-1.

*Gate ends. The first move is FG-1: one paper formulation, priced S,
with its kills already named. NO CLAIM — 0 parts closed, dials 0/4,
and the border, now, has a gate on it.*

---

## Appendix A — corpus claims and their sources (for parent verification)

Every corpus assertion in this paper traces to the bounded reading:

| Claim used | Source |
|---|---|
| Fixed finite volume; torus `Fin 4 → ZMod N`, `N` even; no limit of any kind in Item 2; uniformity is Item 3's wall; continuum = Item 4, corpus holds zero continuum objects | Stage 2 charter §1, §3(iii) |
| OS positivity at U(1), all `β ≥ 0`, is T1 (Route C, `osForm_circle_nonneg`) | Stage 2 charter §2, §3(i) |
| 1b-B at general `(G, ρ)` OPEN; four routes closed; `hgram` not satisfiable | Stage 2 charter §2; gap queue status note |
| S2-3 discharges H-pos at U(1); engine unconditional at the seat | S2-5 dossier, ladder state; S2-4(b) dossier (circle packages) |
| Weld: engine norm is the transfer-form norm, not the `L²` self-pairing; `Q₁` = norm defect (`sliceEnergyForm 1 x = ‖x‖² − ‖W x‖²`) | S2-5 dossier |
| Completion: `sliceHilbertSpace`, `sliceEmbed`, `sliceHatCompleted` (bound 1, self-adjoint, factored positivity, vacuum fixed); `sliceOperator_package` (7 clauses) | S2-4(b) dossier, rung (1) |
| Form closure on the completion: `sliceHamFormC`, domain `≠ ⊤` characterization, `Q₁ = q₁`; `sliceCompletedForm_package` (19 clauses); β = 0: operator = identity on the whole completion, form ≡ 0 | S2-4(b) dossier, rung (2) |
| Operator residue: Friedrichs construction + semigroup `exp(−Ĥ) = T̂_c`; no "Friedrichs", no "Hille" in Mathlib v4.35.0-rc3; cfc bounded-normal only; "a new project, not a brick" | S2-4(b) dossier, rung (3) + residue |
| Q12: compactness conditional on HDen, unconditional at β = 0; Mathlib has no HS/integral-operator compactness API (built by hand) | Q12 dossier |
| Q12: spectral discreteness — eigenvalues real, `‖λ‖ ≤ 1`, `⊥ Ω` for `λ ≠ 1`, `transfer_spectrum_finite_above` | Q12 dossier |
| Q12: `transfer_gap_of_formPos` conditional on TransferFormPos = 1b-B content in operator form; β = 0 gap exact, δ = 1, `T₀` = vacuum projection | Q12 dossier + fences 1–2 |
| Q12: U(1)-to-TransferFormPos weld "S2-2-shaped, not attempted"; HDen named hypothesis; separability an explicit hypothesis | Q12 dossier, fences 2–4 |
| Q12: "a gap uniform in volume is Stage 3c (WALL)" | Q12 dossier, front matter |
| W1: Stage 3c — gap uniform in volume and coupling along a continuum trajectory; Osterwalder–Seiler `m(β) > 0`; research-scale, open; Balaban-scale analogue, gap absent from it | Gap queue §2, W1 |
| W2: Stage 4 — continuum measure; local algebras Type III₁; continuum OS outputs schema only; real Poincaré; price FRONTIER | Gap queue §2, W2 |
| W3: Stage 1c-proper uniformity/clustering — XL, parked | Gap queue §2, W3 |
| `blockedQ2_continuumLimit` — T5 quarantined; `ContinuumLimitData`, `recoversLocality` an uninterpreted Prop field; formal discharge would not discharge the question | Gap queue §4, X2 |
| Q13 closes STANDS-with-one-named-PARTIAL; κ_p = −1/2 through the general assembly at the circle seat | Q13-closes dossier |
| Census 5,205 / 5,254 / 173 | S2-4(b) dossier |

## Appendix B — TO VERIFY (flagged, not asserted)

1. **D-1 (load-bearing).** Whether the landed Stage 2 state (S2-2
   complete, S2-3 STANDS IN FULL, engine on `𝔸_slice`) discharges
   TransferFormPos on **all** of `osSpace` at the U(1) seat, making
   Q12's `transfer_gap_of_formPos` unconditional there. The bounded
   reading contains Q12's "not attempted" (2026-10-24, pre-Stage-2)
   and Stage 2's seat-level discharge, and does not connect them.
   FG-1's dependency audit exists to resolve exactly this.
2. **Renormalization.lean's contents.** The claim "the corpus holds
   zero RG content; `Renormalization.lean` is Connes–Kreimer
   combinatorics" was supplied as standing context for this gate; the
   module itself was outside the bounded reading. Verify against the
   module header before the sentence is quoted publicly.
3. **The Type III trace gloss.** W2 names the continuum local
   algebras Type III₁ [landed record]. That a Type III factor admits
   no faithful trace is standard theory, tagged [T4] in §1.2(3); no
   corpus dossier in the bounded reading states the no-trace property
   itself. If a corpus citation is required, it must be sourced, not
   assumed.
4. **The Coulomb-phase doubt.** §1.1's note that 4D lattice U(1) is
   expected to have a gapless (free-photon) continuum phase is [T4]
   textbook context, deliberately used only to separate
   *formulability* from *truth*. It is not a corpus result and no
   corpus statement depends on it.
5. **The Q13-closes dossier** contains no road-map section; its only
   forward pointer is to the Stage 2 charter. No road-map headings
   were taken from it; the five-item road map used here is the
   commissioning record for this gate.

---

## Parent resolution of D-1 (added 2026-10-25, on landing)

Resolved from the definitions on disk, not from prose:
`TransferFormPos` (LatticeTransferCompact.lean:2191) quantifies over
**∀ f : osSpace** — positivity of the transfer form on the WHOLE
positive-time space. `SliceHPosOne`, discharged at the U(1) seat by
S2-3, is positivity of Π₁ on the **𝔸_slice quotient** — slice-generated
classes, extended by L² density *within the slice classes* (S2-3's
argument), not over osSpace. **Branch taken: Stage 2 does NOT discharge
TransferFormPos on all of osSpace, at U(1) or anywhere.** Q12's gap at
U(1) therefore remains conditional on the whole-space statement, and
FG-1 proceeds exactly as §2.1's second branch prescribes: formulation
under the named hypothesis "TransferFormPos at U(1)", PARTIAL-labeled
per K-FG-1, with the missing connector — whole-space OS positivity at
U(1) from the landed seats — named as the next brick after FG-1.
Appendix B #2 is also resolved: `Renormalization.lean`'s own header
confirms Connes–Kreimer rooted-tree combinatorics; zero RG content
verified at the source.
