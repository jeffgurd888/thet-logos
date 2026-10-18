# P1 — The Triadic Pin: Heat / Gravity / Light = XYZ, assigned leg by leg

**Date:** 2026-10-17. **Item:** P1 of the heat/gravity/light XYZ
gauntlet (`whitepaper/gauntlet-heat-gravity-light-xyz-2026-10-17.md`,
§6: PRICED — S), ratified into the build line by Jeff 2026-10-17
(all five parked ideas, in price order behind ESA-β). **Mode:** audit
pin — every corpus claim below carries a file:line address verified
by grep or build in this run. One small Lean module was added
(`lean/ThetLogos/TriadicPin.lean`, definitions only); it proves
nothing and asserts nothing.

**What a pin is.** P1 was priced to buy exactly two things: (i) a
definite corpus object assigned to each principle, at its honest
tier; (ii) the sharpened R3 statement — the generating claim with its
classes explicit — written so it can be attacked or killed cleanly.
P1 does not buy existence, evidence, or any change to Open Problem
2's status. The gauntlet's verdicts are the starting point; this
dossier confirms or overturns each with fresh evidence.

**Corpus-growth check (the gauntlet is a day old; the corpus is
not).** Since the gauntlet ran, three modules landed: Yukawa
(`032f20a`), ESA-α (`c5731ec`), ESA-β (`a136da5`; program total now
2,569 strict). Grep this run: `tripotent|triadic` occurs **0 times**
in each of `YukawaInteraction.lean`, `BosonicESA.lean`,
`BosonicESABeta.lean`. Nothing that landed touches the triad; every
gauntlet pin below was nevertheless re-verified at its address, and
one gauntlet premise did not survive re-verification (§3, Gravity).

**Note on the parked-fleet gauntlet.** It contains no XYZ section
(grep-verified this run); P1's price and shape are the XYZ gauntlet's
own §6, and the queue position is Jeff's ratification.

---

## Verdict table

| Item | Gauntlet | This pin |
|---|---|---|
| R1 sector correspondence | FIT as nomenclature (T2) | **CONFIRMED** — the table is §1 |
| R2 operator identity | NOT STATABLE; posed-claim KILLed (K1) | **CONFIRMED** — §2(c) names the missing objects |
| R3 generating claim | PARTIAL (skeleton = Open Problem 2; assignment undefined) | **PARTIAL, sharpened** — R3♯(sectors) now stated in Lean (`TriadicPin.lean`); the principle-seat assignment remains undefined, and §1 says exactly why |
| R4 emblem reading | FIT | **UNTOUCHED** — this dossier files nothing in the emblem register |
| Heat leg | FIT (T1 core) | **PIN STANDS** (T1, hygiene footnote made exact, §3) |
| Gravity leg | PARTIAL (a₄ evaluation open) | **PARTIAL** — but the a₄ premise is **OVERTURNED**: the evaluation is proved (§3); the remaining gaps are the fluctuated a₄, the dictionary, and the continuum |
| Light leg | PARTIAL (K4 caveat) | **PARTIAL** — K4 **CONFIRMED** at its address (§3) |
| K1, K2 | KILL | **CONFIRMED** standing (re-grepped) |
| K3 (triad's gravity = quantum gravity) | KILL | **CONFIRMED** — no quantum-gravity object exists in the corpus (§3) |
| K4 (triad's light = SM hypercharge) | KILL | **CONFIRMED** — by the corpus's own theorem (§3) |

**Composite: PIN STANDS** — at the tier P1 was priced at:
nomenclature (§1) plus one sharpened, machine-stated target (§1,
R3♯). The identity remains NO-FIT; the emblem remains the emblem.

---

## §1. The assignment table

| Leg | Pinned corpus object(s) | Address | Tier | The exact sense |
|---|---|---|---|---|
| **HEAT** | The modular package at a state: K = −ln ρ synthesized (`diagModularK`, K = diag(−log wⱼ) for a positive weight vector); the Gibbs state `gibbsState` and `KMSCondition` with `gibbs_kms`; the flux φ = `modularFlux` = i[K, D]; the flow `modularUnitary` / `flowAction` | `ModularTime.lean:25` (synthesis), `:193` (diagModularK), `:223` (modularFlux), `:229` (modularFlux_selfAdjoint); `KMSBridge.lean:58`, `:73`, `:134`; `FlowKernel.lean:184`, `:193`, `:278` | **T1** | The corpus's heat *is* this package: a state, its own −ln as Hamiltonian, the flow it generates, and the KMS theory of the Gibbs state. Heat is pinned to a **state-dependent operator family**, not to one operator — K does not exist until ρ (here: the weights w) is named. That dependence is part of the pin, not a defect in it. Hygiene: the file's one sorry is `ModularTime.lean:206`, inside `kms_identity_diagonal` (:200) — the diagonal-eigenbasis KMS specialization. The general Gibbs KMS theorem is proved separately (`KMSBridge.lean:134`); the pin's objects above do not route through the sorry. |
| **GRAVITY** | The finite Dirac operator D_F (the concrete `smDirac` family on I32) and its spectral-action moments: a₀, a₂ (plain and fluctuated), the closed expansion, **and the a₄ Yukawa evaluation** | `SpectralActionBridge.lean:74` (a₀), `:80` (a₂), `:89` (a₂ fluctuated), `:158` (expansion); `SpectralActionFinite.lean:866` (a₄, **proved** — §3); `InnerFluctuations.lean:120` (fluctuatedDirac) | **T1** for the moments; the Einstein–Hilbert *identification* of the a₂ moment is the standard NCG **dictionary (T2-grade, cited, not a theorem about curvature)** | "Gravity" is pinned to **finite spectral geometry**: one operator and the proved moments of its action. The seat holds numbers along a chosen D_F (a₀ = 32, the a₂/a₄ Yukawa polynomials), not an operator named gravity, not a metric, not curvature — `SpectralActionFinite.lean`'s own header: *"No manifolds, curvature, or heat kernels appear."* |
| **LIGHT** | (i) The U(1) factor of the finite gauge algebra, via the unimodular reduction `SMUnimodular_mem_iff`; (ii) the lattice Circle with its fundamental representation `circleRep` | `SMGaugeAlgebra.lean:197`; `LatticeGauge.lean:1465` (also `:1492`, `:1500`) | **T1** for the seat's existence at both addresses | "Light" is pinned to the **gauge-group seat**: a group factor and its representation data. At neither address is there a quantized electromagnetic field — no photon operator, no field φ(f) for the U(1) sector. The occupant caveat is §3/K4. |
| **XYZ** (the RHS structure) | The predicate `Tripotent` ({{e,e,e}} = e for the TRO ternary product), the generated-TRO predicate `MemGenTRO`, and the target data `smGen` (the twelve SM generators) | `XYZTripotents.lean:39`, `:126`; `MartinettiRep.lean:103` | Predicate **T2** (file's own label); its proved theory T1-grade machine-checked (file dialect "T3") | XYZ is pinned to an **open existential over triples** (Open Problem 2, `XYZTripotents.lean:488`), not to any triple. The named proved tripotents are representation-sector matrices: `cfMat` and `1 − cfMat`, γ_F (`:239`; γ_F itself at `Scaffold32.lean:109`), UJ (`:245`), genC (`:321`), genH k (`:1032`), genM 0 (`:1125`); one proved non-tripotent, genM 7 (`:1161`). |

### The sharpened R3 — what the pin adds

The gauntlet left R3 as: *the (state, geometry, gauge) triple
generates the tripotent field content*, skeleton = Open Problem 2,
triadic assignment undefined. The pin sharpens the **sector** content
and states it in Lean (`lean/ThetLogos/TriadicPin.lean`, built green
this run, 3,128 jobs; strict count **0 theorems / 4 definitions**,
zero sorry — a stated target in the ESA-α `BosonicESA`-def pattern,
asserting nothing):

- `sectorC := {genC}`, `sectorH := Set.range genH`,
  `sectorM := Set.range genM` — the three sector families of the
  Martinetti representation (`MartinettiRep.lean:61`, `:70`, `:97`).
- **`TriadicSectorExistence` (R3♯(sectors), T5):** there exist
  X ∈ sectorC, Y ∈ sectorH, Z ∈ sectorM, each `Tripotent`, whose
  generated TRO contains `smGen g` for all twelve g.

R3♯(sectors) is Open Problem 2 restricted to one-per-sector-family
triples. It is **statable-and-open**: no proved no-go rule closes
this class (R1–R5 close other classes — §4), and no screen in the
corpus has attempted it (grep-verified: the file's triple screens
are `{genC, UJ, γ_F}`, `{genH 0, UJ, genM 0}`, `{genH 0, genH 1,
genH 2}` — §4). The named-matrix grid it ranges over is finite:
1 × 3 × 8 = 24 named triples, of which the 8 containing genM 7 are
dead on arrival (`not_tripotent_genM7`); the tripotence of genM
1–6 is not established anywhere in the corpus — that is P2's
first sub-task (§4).

**The principle-seat assignment is the pin's negative result.**
R3♯ as priced by the gauntlet wanted seats labeled X_heat,
Y_gravity, Z_light. No such labeling is written, because none can
be: a seat label is content only if the seat's class is *defined
from the leg's data*, and the corpus constructs no tripotent from
any leg's data —

- no tripotent is constructed from a state ρ or from K
  (`XYZTripotents.lean` contains no occurrence of the modular /
  Gibbs / state vocabulary — grep this run);
- no tripotent is constructed from D_F (`XYZTripotents.lean`
  contains zero occurrences of `smDirac`, `D_F`, or `Dirac` — grep
  this run; γ_F and the sector matrices are defined from the
  triple's *representation* data in `Scaffold32.lean` /
  `MartinettiRep.lean`, and share with D_F only the carrier
  `Matrix I32 I32 ℂ`);
- no tripotent is constructed from the gauge representation (the
  U(1)/unimodular material never enters the file).

Any bijection {C, H, M} → {heat, gravity, light} is therefore a
**naming choice (R1-tier nomenclature), Jeff's to make, not the
corpus's to derive**. The pin records the three seats unlabeled
rather than counterfeit a derivation. If Jeff names a bijection,
it enters the ledger as nomenclature beside this table and
R3♯(sectors) acquires principle labels at T2 — its mathematical
status (open) is unchanged by any labeling.

---

## §2. The relations audit

Relations among the pinned objects of §1, classified: **(a)**
proved, **(b)** statable-and-open, **(c)** not statable today.

### (a) Proved

| Relation | Content | Address |
|---|---|---|
| ρ ↔ K | K is synthesized as −ln ρ; for diagonal weights, `diagModularK` | `ModularTime.lean:25`, `:193` |
| K → flow | `modularUnitary` is unitary; `flowAction` conjugates observables by it | `FlowKernel.lean:184`, `:193`, `:278` |
| Gibbs ↔ KMS | The Gibbs state satisfies `KMSCondition` at its own β | `KMSBridge.lean:73`, `:134` (unnormalized form `:110`) |
| **Heat ↔ Gravity** | φ = `modularFlux` K D = i[K, D] is self-adjoint for Hermitian K, D — the one proved cross-leg relation: the state's K acts on the geometry's D | `ModularTime.lean:223`, `:229` |
| Heat ↔ Gravity (vanishing direction) | For Gibbs-type K = β·D² the flux is identically 0; the KMS state is flux-stationary | `ModularFlux.lean:42`; `KMSBridge.lean:214` |
| **Gravity ↔ Light** (finite level) | Inner fluctuation: `fluctuatedDirac` D_F A couples the gauge potential A into D; order-one condition and self-adjointness proved; the fluctuated a₂ moment is a theorem | `InnerFluctuations.lean:120`, `:329`, `:422`; `SpectralActionBridge.lean:89` |
| Within XYZ | Reachability and no-go theory around Open Problem 2 | §4 (addresses there) |

### (b) Statable-and-open

| Relation / statement | Status | Address |
|---|---|---|
| Open Problem 2 (generation, unlabeled) | Stated in Lean; open; sole sorry quarantined at `:492`; depended on by no theorem outside its file (grep this run — the only external mention is this pin's own module header, a comment) | `XYZTripotents.lean:488` |
| R3♯(sectors) (generation, one per sector family) | Stated in Lean by this pin; open; unscreened | `TriadicPin.lean` (`TriadicSectorExistence`) |
| `tr_fluctuated_fourth` (the fluctuated a₄ moment) | Stated as open in its file's header and §-comment; the unfluctuated analog is proved (:866) | `SpectralActionFinite.lean:17`, `:632` |

### (c) Not statable today — the missing object named for each

1. **Any equation or relation with "XYZ" as a term** (R2's core).
   Missing object: **a denotation for XYZ** — a constructed triple
   of tripotents, or the existence theorem (Open Problem 2) that
   would let one be named. Today "XYZ" denotes an existential, and
   an existential cannot stand in an equation.
2. **The principle-seat assignment** (which tripotent seat answers
   to heat, which to gravity, which to light). Missing object:
   **a sector-assignment construction** — a map from a leg's data
   (a state ρ; the operator D_F; the gauge representation) to a
   tripotent or a tripotent class. Evidence of absence, this run:
   `Tripotent` occurs outside `XYZTripotents.lean` only at
   `Axioms.lean:32` (a tripotent relation for N₀ — a different
   object) and `Chromatic.lean:30` (a string label); the
   tripotent file contains no Dirac, state, or modular vocabulary
   at all.
3. **Any modular/thermal relation of the gauge sector** (heat ↔
   light), including the sharp form "the lattice β is a KMS β".
   Missing objects: **a named state on H_F** (no density matrix on
   the I32 carrier exists in the corpus's modular formalism — the
   modular sector lives over a generic `Fin N`, the triple sector
   over `I32`, and no construction identifies them); and **a
   density-matrix/modular formulation of the lattice Gibbs
   measure** (`gibbsMeasure`, `LatticeCorrelations.lean:188`, is a
   classical probability measure; grep this run finds no KMS or
   modular treatment in `LatticeGauge.lean` /
   `LatticeCorrelations.lean`, and no file of the modular package
   imports a gauge file or vice versa).
4. **Gravity as curvature** — any statement of the form "the a₂
   moment *is* the Einstein–Hilbert term" as a theorem, and every
   continuum form of the gravity leg. Missing objects: **curvature
   and manifold objects** — none exist in the corpus
   (`SpectralActionFinite.lean` header, quoted in §1). The
   identification that exists is dictionary-level (T2).
5. **Light as a field** — any statement about light as a quantized
   electromagnetic field at either pinned address. Missing object:
   **a quantized EM field** (a photon/field operator for the U(1)
   sector). Both addresses hold group-and-representation data only.
6. **Quantum gravity, in any form** (K3's object). Missing object:
   **any quantum-gravity object whatsoever** — no quantized metric,
   no graviton, no quantum geometry dynamics exists in the corpus
   to state a relation with. (The word "gravity" in corpus prose —
   e.g. the dictionary line at `SpectralAction.lean:107` — is
   header prose about the *continuum* dictionary, not an object.)

---

## §3. Verdicts per leg, and the kills re-examined

**HEAT — PIN STANDS.** The gauntlet's FIT is confirmed at every
address, with the hygiene footnote made exact (the sorry is
`kms_identity_diagonal`'s, `ModularTime.lean:206`; the pin's
objects are proved, and the general KMS theorem is
`KMSBridge.lean:134`). The thermal-vanishing discipline travels
with the pin (`ModularFlux.lean:42`): the leg's flux exists only
for the state's own K, not for an arbitrary hot operator.

**GRAVITY — PARTIAL, with the gauntlet's a₄ premise OVERTURNED.**
The gauntlet (following the file's own header) recorded the a₄
Yukawa evaluation as an open stretch. It is not open:
`tr_DF_fourth_yukawa` stands proved at
`SpectralActionFinite.lean:866` on the block lemma
`trace_buildDirac_fourth` (`:720`); this run rebuilt the module
(3,125 jobs, green) and `#print axioms tr_DF_fourth_yukawa`
returned exactly `[propext, Classical.choice, Quot.sound]` — no
sorry. The theorem predates the gauntlet (the file's last commits
are the 2026-10-15 repair line); **the file's header (`:16`) and
its §-comment (`:631–632`) still call it open — a stale-header
defect in the corpus, flagged here and priced in §5, not edited by
this pin.** Consequences, stated at exactly their width:

- The gravity leg's proved moment content is now a₀, a₂, a₄
  (unfluctuated) + a₂ fluctuated. What remains open in-leg is the
  **fluctuated** a₄ (`tr_fluctuated_fourth`) — a different, still
  open statement.
- The gauntlet's §6 upgrade condition for this leg ("a₄ landed
  *and* a stated finite-level EH identification theorem") is now
  half met. The leg stays **PARTIAL** on the remaining items: the
  EH identification is dictionary-only (§2(c)4), the continuum is
  NO-FIT (theories intake, standing), and —
- **K3 is CONFIRMED, not softened:** none of this is quantum
  gravity. No quantum-gravity object exists in the corpus (§2(c)6);
  the morning audit the gauntlet restated stands at full strength.
  The reading "the triad's gravity is quantum gravity" is **KILLed
  as posed**, confirmed at the audited addresses.

**LIGHT — PARTIAL; K4 CONFIRMED at its address.** The seat stands
(T1, two addresses — §1). The occupant claim dies by the corpus's
own theorem: `pi_u1_eL_trivial` (`SMGaugeAlgebra.lean:340`, its
docstring consequence at `:334–338`) — the represented U(1) acts
trivially where hypercharge does not, so the represented U(1)
**cannot be SM hypercharge**; the hypercharge assignments
themselves are T2 inputs (`SMGaugeAlgebra.lean:219–229`;
`SMFermions.lean:45–47`, docstring: "INPUT (Tier T2)"). The
reading "the triad's light is SM hypercharge" is **KILLed as
posed**, confirmed. No quantized EM field exists at the seat
(§2(c)5).

**XYZ / R3 — PARTIAL, sharpened.** The generation skeleton is
Open Problem 2 (stated, open, quarantined sorry at
`XYZTripotents.lean:492` inside the statement at `:488`). The pin
adds R3♯(sectors) as a stated, unscreened sharpening (§1) and
records the seat assignment as undefined-for-cause (§1, §2(c)2).
**K1 CONFIRMED** (the identity is neither posed nor provable:
type audit + the §2(c) greps, rerun this run). **K2 CONFIRMED**
("XYZ is a constructed triple of field operators" — at its only
corpus address it is an open existential over a proved graveyard
of candidate classes, §4).

**R1 — CONFIRMED FIT (T2).** §1 is the correspondence table the
reading asserts; every cell has a verified address.

**R4 — UNTOUCHED.** The emblem register is not this dossier's
business; nothing here promotes or demotes it.

**Composite — PIN STANDS.** As priced: the assignment is written
at its tiers (§1), the sharpened R3 is stated in Lean (§1), the
relations are classified with every gap named (§2), and the
inflated readings of two legs are confirmed dead (K3, K4). The
identity (R2) remains NO-FIT and unposed; that was the gauntlet's
verdict and the pin's evidence sustains it in full.

---

## §4. What P2 inherits

The screening wave (gauntlet §6: PRICED — M; next-but-one in the
ratified line) screens against exactly these pinned statements —
all addresses verified in this run:

1. **The target, unlabeled:** `xyz_tripotents_exist`
   (`XYZTripotents.lean:488`): ∃ X Y Z : Matrix I32 I32 ℂ,
   Tripotent X ∧ Tripotent Y ∧ Tripotent Z ∧ ∀ g : Fin 12,
   MemGenTRO {X, Y, Z} (smGen g). Sole sorry `:492`.
2. **The target, sector-sharpened (new with this pin):**
   `TriadicSectorExistence` (`TriadicPin.lean`): one tripotent
   from each of `sectorC` / `sectorH` / `sectorM`. Its named
   grid is 24 triples; 8 die with genM 7 (`:1161`); **P2's first
   sub-task is the tripotence of genM 1–6**, established nowhere
   in the corpus today.
3. **The reachability scoreboard** (which generators any named
   triple reaches — of the twelve `smGen`, exactly {0, 1, 2, 3, 4}
   are reached by some named triple; no single triple reaches
   more):
   - `{genC, UJ, γ_F}` reaches smGen 0 (`:931`) and provably not
     smGen 1 (`:939`);
   - `{genH 0, genH 1, genH 2}` reaches smGen 1, 2, 3 (`:1267`);
   - `{genH 0, UJ, genM 0}` reaches smGen 1 and 4 (`:1249`) and
     provably misses smGen 11 (`:1259`).
4. **The five no-go rules** (the surviving candidate class is what
   they leave: non-diagonal, multi-sector, non-ℤ[i]-valued):
   R1 no all-diagonal triple (`:175`; the sector-projection
   candidate refuted by name, `sector_triple_fails` `:203`);
   R2 conjugation preserves diagonality (`:390`); R3 support
   invariance traps single-sector triples (`:447`); R4
   pair-support invariance kills {UJ + two diagonals} for smGen 1
   (`:741`); R5 ℤ[i]-entry invariance kills every ℤ[i]-valued
   triple for smGen 11 (`:901`).
5. **The proved tripotent inventory P2 may draw on:** γ_F
   (`:239`), UJ (`:245`), genC (`:321`), genH k (`:1032`), genM 0
   (`:1125`), plus the projection family (`cfMat`, `1 − cfMat`)
   — and the one proved non-tripotent, genM 7 (`:1161`).
6. **The failure branch is a deliverable:** a sixth invariant
   closing the surviving class proves the negation of (1) — Open
   Problem 2's own header counts that as a legitimate outcome of
   the test (`XYZTripotents.lean`, header and §12 rubric).

P2 inherits **no principle labels on seats** (§1): it screens
sector statements. If Jeff supplies the seat bijection as
nomenclature, P2's report may use the labels at T2 without any
statement changing.

---

## §5. What would have to be built for R2 to become statable

Priced per item. "Statable" means: both sides denote objects of
one type and the connective tissue exists as definitions — it
does not mean proved, or plausible.

| # | Build | Price | What it buys |
|---|---|---|---|
| 1 | A denotation for XYZ: prove Open Problem 2, or construct one named triple reaching all twelve generators | **UNPRICED** — research; both branches (construction / sixth-invariant kill) are live, per the file's own assessment | Removes §2(c)1. Without it nothing else on this list makes R2 statable. |
| 2 | A *named partial triple* + identities stated about it (the R2 shape, weakened to a denoting RHS) | **S** — but it enters as a **new candidate** under the relabeling rule, not as R2 discharged | An equatable RHS with partial reach (today's best: 2 of 12 from one triple, `:1249`) |
| 3 | Principle-seat constructions: tripotents *defined from* leg data — from D (sign/grading constructions on H_F; γ_F at `Scaffold32.lean:109` is the existing template), from the gauge rep (sector projections; the `cfMat` family exists), from a state (blocked on item 4) | **S** per leg for the definitions; any *proved generation content* for the constructed classes is Open-Problem-2-scale, unpriced | Removes §2(c)2 at the definitional level: seats acquire classes with provenance, and R3♯ gains principle labels as content rather than nomenclature |
| 4 | A named state on H_F (a density matrix on the I32 carrier in the corpus's modular formalism) + its modular package (K, flow, KMS-at-that-state statements; the `FlowKernel` machinery is generic over `Fin N`, so instantiation is the cheap part) | **S–M** | The heat leg gets an address *on the triple's own carrier*; heat ↔ gravity and heat ↔ light relations become statable (open) instead of (c) |
| 5 | A density-matrix / modular formulation of the lattice Gibbs measure (finite config space: a state on the config algebra + its K) | **M–L** | The sharp heat ↔ light form ("lattice β vs KMS β") becomes statable |
| 6 | A stated finite-level EH identification theorem (the spectral-action moments assembled into an Einstein–Hilbert-type functional statement about the finite triple) | **M** | The gravity leg's dictionary becomes a theorem at finite level (the continuum stays NO-FIT — a different wall, untouched by this item) |
| 7 | `tr_fluctuated_fourth` (the fluctuated a₄ moment; the block-expansion lemma it needs is the proved `trace_buildDirac_fourth` pattern, `SpectralActionFinite.lean:720`) | **S–M** | Completes the gravity leg's moment table; does not by itself move R2 |
| 8 | A quantized EM field at the light seat | **XL** — Pitch-4-scale infrastructure, outside this pin's frame | Light as a field becomes statable |
| 9 | A quantum-gravity object | **NO PRICE** — no object class exists in the corpus to price a construction against | K3 stands until a field of objects exists |
| 10 | Editorial: correct the stale `SpectralActionFinite.lean` header (`:16`) and §-comment (`:631–632`) that call the proved a₄ evaluation open | **S** — flagged by this pin, **not executed** (outside this commission's commit scope) | The corpus stops misdescribing its own gravity leg |

---

## Appendix — evidence index (all verified in this run)

- **Pin module:** `lean/ThetLogos/TriadicPin.lean` — targeted
  build green (3,128 jobs); strict count (line-initial
  `^(theorem|lemma) `, comment-stripped): **0 theorems, 4
  definitions** (`sectorC`, `sectorH`, `sectorM`,
  `TriadicSectorExistence`); zero sorry/admit. Program total
  unchanged: the module adds no theorem declarations.
- **a₄ verification:** `lake build ThetLogos.SpectralActionFinite`
  green (3,125 jobs); `#print axioms
  ThetLogos.tr_DF_fourth_yukawa` → `[propext, Classical.choice,
  Quot.sound]` (scratch probe, deleted).
- **Heat:** `ModularTime.lean:25/:193/:206/:223/:229`;
  `FlowKernel.lean:184/:193/:278`;
  `KMSBridge.lean:58/:73/:110/:134/:214`;
  `ModularFlux.lean:42`.
- **Gravity:** `SpectralActionBridge.lean:6/:74/:80/:89/:158`;
  `SpectralActionFinite.lean:16/:17/:631–632/:720/:866`;
  `InnerFluctuations.lean:120/:329/:422`;
  `SpectralAction.lean:107` (dictionary prose).
- **Light:** `SMGaugeAlgebra.lean:197/:219–229/:334–338/:340`;
  `SMFermions.lean:45–47`; `LatticeGauge.lean:1465/:1492/:1500`.
- **XYZ:** `XYZTripotents.lean` (1,278 lines): `:39/:126/:175/
  :203/:239/:245/:321/:390/:447/:488/:492/:741/:901/:931/:939/
  :1032/:1125/:1161/:1249/:1259/:1267`;
  `MartinettiRep.lean:61/:70/:97/:103`;
  `Scaffold32.lean:109`; corpus-wide `Tripotent` also only at
  `Axioms.lean:32`, `Chromatic.lean:30`.
- **Growth check:** `YukawaInteraction.lean`, `BosonicESA.lean`,
  `BosonicESABeta.lean` — 0 occurrences of `tripotent|triadic`
  each; no modular↔gauge cross-imports in either direction;
  no KMS/modular hits in the lattice files.

*End of dossier. The pin stands: three legs assigned at their
tiers, one sharpened target stated in Lean, every unstatable
relation carrying the name of its missing object — and the seats
left honestly unlabeled, because the corpus cannot label them and
this program does not counterfeit labels.*
