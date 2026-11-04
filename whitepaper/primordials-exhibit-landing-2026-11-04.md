# PRIMORDIALS EXHIBIT — SCOPING + LANDING DOSSIER — 2026-11-04

**Item:** "The Primordials Exhibit" (WORKING LABEL ONLY — naming is
Jeff's hand). Commissioned by Jeff's word "build it" (2026-11-04
11:19 EST) on his seeing of 2026-11-04 ~11:16, filed verbatim in
`~/memory/2026-11-04.md`:

> "our primordials are mathematics physics and correlations of
> letters and meanings. in language words are and do while in
> mathematics numbers are objects or actions and the correlations
> to each in a unified language/letters/numbers/correlations/
> meaning/logic/reason"

**Bounded reading (stated to Jeff before the build):** build the
formable core — the are/do duality inside the corpus's own grammar —
and fence the rest as not-yet-statements with pins for Jeff's hand.
No semantics/meaning machinery is invented; no "unified language"
is claimed.

**Lane:** isolated worktree `~/workspace/thet-logos-primordials`,
branch `primordials-lane`, cut from main-tree HEAD `3f35ede`
(T4-integrated successor: census 13,307 strict / 491 modules,
fence 345/345 at cut). Lane commit only — NO integration, NO push.
Mathlib v4.35.0-rc3.

---

## PHASE 1 — SCOPING: WHAT OF THE SEEING IS STATABLE TODAY

The audit question: which components of the seeing are statements
in the corpus's type theory (Lean 4 dependent type theory over the
pinned Mathlib) *today*, with theorem content, and which are
not-yet-statements. The duality at the heart of the seeing — words
*are* and *do*; numbers are objects *or* actions — is, in dependent
type theory, structural: every term both IS (it is an object of the
grammar, nameable, storable, passable) and, if its type is a
function type, DOES (it acts by application). That structural fact
by itself is definitional and proves nothing; the scoping grades
below separate the definitional shadow from the components that
carry actual proof content at the corpus's own seats.

Seats audited (all landed, consumed unedited):
- `ThetLogos.laplacianOp (w : V → V → ℝ) (F : V → ℝ) (i : V) : ℝ`
  (BridgeLaplacian) — the corpus's operator in curried action form.
- `ThetLogos.lapLinFun (w) : (V → ℝ) →ₗ[ℝ] (V → ℝ)`
  (BridgeCompletion) — the same operator packaged as ONE object, a
  citizen of the endomorphism ring; landed bridge
  `lapLinFun_apply : lapLinFun w F = laplacianOp w F` (T2's dossier).
- `ThetLogos.ModularVariance.gibbsProb / gibbsExpect / meanEnergy`
  (ModularVariance) — the finite Gibbs state's weight-object and
  its action on observables.

### Component grades

**(a) ACTIONS ARE OBJECTS — GO (with a definitional core, graded).**
The bare claim "a function is a term" is DTT-definitional: no
theorem content, and none is manufactured. The content-bearing
form at the seat: the packaged action-object `lapLinFun w` is a
citizen of the endomorphism ring — action-objects can be ADDED and
MULTIPLIED (composed) as objects, and the ring operations act as
the corresponding doings (sum acts pointwise-sum; product acts by
iteration). Those application facts are real statements about the
corpus's own operator. GO.

**(b) OBJECTS ACT — GO.**
Three exhibits at corpus seats: (i) a vertex name `i : V` — a pure
object, a "letter" of the seat — acts on the space of potentials
as the evaluation functional `evalAt i`; (ii) a number `a : ℝ`
acts on potentials by scaling (component (d)); (iii) a Gibbs
weight-object `gibbsProb E β` acts on observables as the
expectation functional, returning `gibbsExpect` / at the energy
observable, the number `meanEnergy E β`. GO.

**(c) THE CORRELATION IS APPLICATION / COMPOSITION — GO.**
The correlations between the are-role and the do-role are the
evaluation facts: applying the named object reproduces the action
(landed `lapLinFun_apply`, consumed); composition of actions is
an object whose application is iteration; the number-action and
the operator-action commute, and the commutation IS the corpus's
proved linearity of its own Laplacian (`map_smul` of `lapLinFun`,
whose `map_smul'` field is the landed `laplacianOp_smul`); a name's
evaluation of a number's action is multiplication. Each is a small
theorem stated about the seat, not a metaphor. GO.

**(d) NUMBERS SPECIFICALLY — GO.**
For `a : ℝ`, the scaling action-object `numAction a` on
`(V → ℝ)`: the correlations between the number's object-arithmetic
and its action-arithmetic are theorems — `numAction (a + b)` is
the sum of the actions, `numAction (a * b)` is the composition
(product in the endomorphism ring) of the actions, `numAction 0`
is the zero action, `numAction 1` is the identity action; and the
assignment is FAITHFUL at any inhabited seat
(`numAction_injective`, `[Nonempty V]`): distinct numbers are
distinct actions — the number's are-role and do-role determine
each other at the seat. The injectivity carries a genuine
hypothesis (an empty seat has no potentials to act on, and there
the correlation collapses — stated, not hidden). GO.

### NO-GO components — not-yet-statements, pins for Jeff's hand

- **N1 — Letters as syntax with denotation.** A type of letters/
  words (an alphabet, strings, a grammar) together with a
  denotation map into corpus objects and a compositionality law
  (denotation of a compound = combination of denotations). The
  *shape* is formable, but no alphabet/syntax type exists in the
  corpus, and choosing one — what counts as a letter, what
  compounds are legal — is a design act in Jeff's hand, not a
  lane's. PIN (shape only): `⟦·⟧ : Syn → SeatObject` with
  `⟦compound s t⟧ = combine ⟦s⟧ ⟦t⟧` for a named `combine`.
- **N2 — Meaning / reference.** What a letter *means* beyond its
  denotation inside the grammar: no semantics, reference, or
  intension machinery exists in the corpus or the pinned Mathlib
  adequate to state it. PIN (shape only): a meaning assignment
  with at least one theorem distinguishing two expressions of
  equal denotation and different meaning — until such a
  distinguishing theorem is statable, "meaning" has no seat.
- **N3 — Natural-language words are/do.** Nouns and verbs of
  natural language are outside type theory entirely; no formal
  seat exists or is proposed. Not a pin — a boundary.
- **N4 — The mathematics↔physics correlation as a theorem.**
  That is the program's horizon (the dial structure), not an
  exhibit brick; it is not purchasable at exhibit scale and is
  not stated here.
- **N5 — A unified-language object.** A single type in which
  letters, numbers, and meanings are citizens with proved
  correlations among all three: depends on N1 and N2 landing
  first. Not-yet-statement.

### What Phase 1 clears for build

One module exhibiting (a)–(d) at the seats above, with every
item's grade (definitional / generic-structure / seat-content)
printed on the module's face. Nothing else builds.

---

## HONESTY LEDGER (standing, on the dossier and the module face)

This exhibit shows the are/do duality INSIDE the formal grammar
the corpus already owns. It is not new mathematics: most items
are the pinned Mathlib's generic structure instantiated at corpus
seats, plus two seat-specific facts with real hypotheses
(faithfulness of the number-action at an inhabited seat; the
commutation correlation, which consumes the corpus's own proved
linearity of its Laplacian). It is NOT a unified language of
letters and meanings; the letters↔meaning correlation is fenced
as T5, unbuilt, pins N1–N5 above. Jeff's seeing stands at T5 as
filed; this module is its formable core and nothing more.
**NO CLAIM; dials 0/4.**

---

## PHASE 2 — LANDING

**OUTCOME GRADE: FULL** — every component Phase 1 cleared GO
landed, in one new module, at its scoped shape. No component was
dropped, weakened, or restated in transit.

**Artifact:** `lean/ThetLogos/PrimordialsExhibit.lean` —
**strict 16 + 3 defs** (`numAction`, `evalAt`, `weightFunctional`).
NO PRICE WAS PRE-SET for this commission; the count is reported
plainly. Size note: 16 strict is small by the corpus's brick
standards — correctly so. This is an exhibit, not a theory: the
duality is structural in the grammar, and the module's job is to
pin it at the corpus's seats with grades on the face, not to
manufacture theorem bulk. Padding it would have been the failure
mode Phase 1 was written to prevent.

**Verification:** targeted build green (3,593 jobs — the lane
built `ModularVariance` fresh: it has no cached olean in the main
tree, not being in the root build graph; the SR-5 lane hit the
same fact), ZERO sorrys, module WARNING-CLEAN (every warning in
the log belongs to pre-existing corpus modules), no
`native_decide`. `#print axioms` on all 16 headlines: exactly
`{propext, Classical.choice, Quot.sound}` each — no `sorryAx`,
no other axioms.

**Grade-per-item (as printed on the module's face):**
- DEFINITIONAL (the grammar's shadow; pins the duality, proves
  nothing): `numAction_apply`, `evalAt_apply`,
  `weightFunctional_apply`, `weightFunctional_gibbsProb`,
  `gibbsWeight_act_energy` — plus the landed `lapLinFun_apply`,
  consumed, not restated.
- GENERIC (the pin's Mathlib structure at the seat):
  `lapAction_mul_apply` (composition-object acts by iteration),
  `lapAction_add_apply` (sum-object acts pointwise-sum),
  `numAction_apply_apply`, `numAction_zero`, `numAction_one`,
  `numAction_add` (object + ↔ action +), `numAction_mul`
  (object × ↔ action composition), `eq_of_evalAt_eq`
  (determination: `funext` at the seat), `evalAt_numAction`
  (letter ∘ number = multiplication).
- SEAT-CONTENT (real hypotheses / corpus-proved facts consumed):
  `numAction_injective` — faithfulness of number ↦ action,
  carrying `[Nonempty V]` on its face (on an empty seat the
  correlation collapses, and the statement says so);
  `numAction_comm_lap` — the number-action and the Laplacian
  action commute, consuming the corpus's own proved linearity
  of its operator (`lapLinFun`'s `map_smul'`, i.e. the landed
  `laplacianOp_smul`).

**Pin quirks found in the lane (recorded for the next builder):**
(i) in this pin the composition-apply lemma for endomorphisms is
`Module.End.mul_apply`, not `LinearMap.mul_apply`; (ii) bare
statements of the form `numAction c = …` do not elaborate — the
seat `V` occurs only as `numAction`'s implicit and must be pinned
(`(V := V)` or a full type ascription); (iii) the `ext` tactic on
equalities over `V → ℝ` chains into the Pi-module extensionality
via `LinearMap.single` compositions (in this pin) and produces
unworkable goals — the correlations are proved through
`LinearMap.ext` applied directly; (iv) `omit` must precede the
doc comment (house rule, reconfirmed).

**Not built, standing as pins for Jeff's hand:** N1
syntax-with-denotation, N2 meaning/reference, N3 natural
language, N4 the mathematics↔physics correlation, N5 a
unified-language object (Phase 1, above). The letters↔meaning
correlation remains T5, unbuilt. **NO CLAIM; dials 0/4.**

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from primordials-lane commit `2300257` (lane base
`3f35ede`) onto main-tree HEAD `5024f52` (SR-5 integration
successor). Module + this dossier copied **byte-identical**
(md5 `18d1809d…` PrimordialsExhibit, `7af106a4…` dossier;
diff-verified). Declaration-level collision scan of all 19
declaration names plus the module name against the main tree at
HEAD found **zero collisions** (index-based `git grep` at HEAD).

- Main-tree targeted build green (**3593 jobs**, matching the
  lane), zero sorrys (zero-sorry source gate PASS, 508 files),
  **module warning-clean** (every warning in the build log is
  pre-existing dependency replay).
- Recount exact: PrimordialsExhibit **strict 16 + 3 defs**
  (whole-tree 14,009/508 minus frozen remainder 669/15).
- Fence admissions: all **16 headlines** with
  `import ThetLogos.PrimordialsExhibit` in the **same commit**
  as the module — **FENCE PASS 378/378** (362 → 378), every
  headline on exactly {propext, Classical.choice, Quot.sound},
  no `sorryAx` (verified independently in the main tree by
  `#print axioms` on all 16).
- Ledger record `primordials-exhibit` (standing, T3, kill_id
  null — no kill was registered for this exhibit; the grades
  are on the module's face); validator PASS, 39 records.
- Census (FILES-TRUE, method of record): **13,324/492 →
  13,340 strict / 493 modules**; README prose census and badge
  both 13,340 / 493, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`) and in the
  commit message's own record chain. The letters↔meaning
  correlation remains T5, unbuilt; pins N1–N5 stand for Jeff's
  hand. NO CLAIM; dials 0/4.
