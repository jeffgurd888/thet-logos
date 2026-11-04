# MEANING BRIDGE — LANDING DOSSIER — 2026-11-04

**Item:** "Meaning Bridge" (WORKING LABEL ONLY — naming is
Jeff's hand). Brick 1 of 2 of Jeff's commission "build the
bridge of the alignment" → "do all and see" (2026-11-04).
Brick 2 (the three-primordial alignment exhibit) consumes this
module's interface; its definition names are FROZEN below.

**Jeff's seeing served (verbatim, filed in
`~/memory/2026-11-04.md`):** the primordials are mathematics,
physics, and the correlations of letters and meanings; in
language words are and do; symbols and glyphs also carry
meaning; words sometimes have conflated meanings; translated
words are even worse at precision of grammar; the unified
language needs to contain every language.

**Bounded reading (stated before the build):** pin N1 of the
primordials dossier (`primordials-exhibit-landing-2026-11-04.md`)
at its first formable core — a language as a syntax set, a
meaning set, and an alignment relation between them, with the
exact conditions under which a checkable denotation exists.
Nothing more. No semantics is invented; N2 stays open.

**Lane:** isolated worktree `~/workspace/thet-logos-meaningbridge`,
branch `meaning-bridge-lane`, cut from main-tree HEAD `7f400d8`
(census 13,357 strict / 494 modules, fence 395/395 at cut).
Interface freeze commit `08cfd6c`. Lane commits only — NO
integration, NO push. Mathlib v4.35.0-rc3.

---

## OUTCOME GRADE: FULL

Every component of the scoped brick landed at its pinned
shape: §1 interface, §2 characterizations (a)–(d) ALL FOUR
(including the quotient fact, which was conditional on landing
cheaply — it did), §3 are/do echo (definitional, as fenced),
§4 containment seed WITH its kill. Nothing was dropped,
weakened, or restated in transit. No component went PARTIAL.

**Artifact:** `lean/ThetLogos/MeaningBridge.lean` —
**strict 15 + 12 defs**, inside the priced S–M band (~10–20
strict) and under the 22-strict stop-line. The module is
self-contained: it imports only `Mathlib.Tactic` and consumes
no corpus seat — by design. Its content is the SHAPE of a
meaning kernel, true of every relation of this form, and the
honesty ledger below grades it exactly that way.

**Verification:** targeted build green (3,117 jobs), ZERO
sorrys (source scan: no `sorry`, no `native_decide` anywhere
in the module), module WARNING-CLEAN on a forced rebuild
(every warning in the wider log belongs to pre-existing corpus
modules). `#print axioms` on all 15 headlines plus the
quotient equivalence: every one on a SUBSET of
{propext, Classical.choice, Quot.sound} — no `sorryAx`, no
other axioms. Itemized: the seven §1–§2 headlines rest on
Classical.choice alone (via the denotation's choice), except
`exists_unique_denotation` (Classical.choice, Quot.sound) and
`conflation_iff_not_functional` (all three);
`quotientSameMeaningEquivRange` rests on (Classical.choice,
Quot.sound); `SameMeaning.equivalence`, both §4 rfl facts,
`graphAlign_functional_total`, and all three §5 union items
depend on NO axioms at all.

---

## WHAT LANDED, GRADED ON ITS FACE

**§1. The interface (DEFINITIONAL).** `MeaningAlign S M`, a
transparent alias for a relation `S → M → Prop` — a language
as glyphs, meanings, and the carrying relation. Predicates:
`MeaningAlign.Functional` (each glyph at most one meaning —
its failure is Jeff's conflation), `MeaningAlign.Total` (every
glyph means something), `MeaningAlign.InjectiveAlign` (each
meaning at most one glyph — its failure is synonymy),
`MeaningAlign.SurjectiveAlign` (every meaning is named).

**§2. The characterization (GENERIC).** The checkable
content of the brick:

- (a) `MeaningAlign.functional_total_iff`: functional ∧
  total ⟺ the alignment is the graph of a denotation
  function. With `MeaningAlign.denotationOf` (the picked
  meaning, choice in the construction on its face),
  `denotationOf_spec` (the pick is aligned), and
  `align_iff_denotation` (under functionality, aligned =
  denoted), and `exists_unique_denotation`: the denotation
  exists AND is unique. Jeff's "mathematical equivalent" made
  literal — a checkable denotation exists iff no conflation
  and no gaps, and when it exists it is pinned.
- (b) `MeaningAlign.denotation_injective_iff`: under (a)'s
  hypotheses, the denotation is injective ⟺ the alignment is
  injective — synonymy in the relation and non-injectivity of
  the function are one fact in two roles.
  `MeaningAlign.denotation_surjective_iff`: the same for
  surjectivity / unnamed meanings.
- (c) `MeaningAlign.conflation_iff_not_functional`: a glyph
  with two distinct aligned meanings exists ⟺ the alignment
  is not functional. Jeff's observation as a theorem shape,
  with the witness.
- (d) `SameMeaning` / `SameMeaning.equivalence` /
  `sameMeaningSetoid` / `quotientSameMeaningEquivRange`: for
  a denotation function, same-meaning is an equivalence on
  glyphs (the synonym classes), and its quotient is
  equivalent to the denotation's range — the occurring
  meanings, each counted once.

**§3. The are/do echo (DEFINITIONAL, as fenced).**
`graphAlign` (a function IS an alignment: its graph),
`graphAlign_apply` (by `rfl`), `graphAlign_functional_total`
(functions never conflate and never gap — §2 read backwards,
the one fact of the section, proved in one line), `actAlign`
(a glyph denotes, then an action on meanings acts — the
composite is again an alignment), `actAlign_apply` (by
`rfl`). Nothing here cost real proof work; had it wanted any,
it would have been left out, per the fence.

**§4. The containment seed (GENERIC).** `unionAlign` /
`unionAlign_apply`: two alignments into a COMMON meaning set
unite — the smallest alignment containing both.
`unionAlign_total_of_left`: totality survives union (no
glyph's meaning is lost by containment). And the price of
containment, as theorems:

- `unionAlign_functional_iff`: the union is functional ⟺
  both are functional AND they agree across the seam
  (∀ s m₁ m₂, A s m₁ → B s m₂ → m₁ = m₂). The cross-condition
  is necessary and sufficient — internally conflation-free
  languages can still conflate a glyph between them.
- `exists_functional_unionAlign_not_functional`: **K-MB-1
  FIRED as a proved counterexample.** The naive claim "a
  union of functional alignments is functional" is FALSE:
  on `Bool`, the constant-`true` and constant-`false`
  alignments are each functional, and their union hands every
  glyph both meanings. The kill is a theorem in the module,
  not a remark in this dossier.

---

## KILL DISPOSITIONS

- **K-MB-1 — FIRED (and landed as its corrected form).** The
  naive union-preserves-functionality claim is false, by the
  explicit `Bool` counterexample above. The corrected form
  (exact cross-condition, iff) landed in the same module.
  Nothing was smoothed: the dossier and the module header
  both carry the kill at full rank.
- **K-MB-2 — DID NOT FIRE.** The denotation-existence
  characterization needs only Classical.choice (inside the
  fence) — no choice principle beyond {propext,
  Classical.choice, Quot.sound} anywhere in the brick.

---

## FROZEN INTERFACE FOR BRICK 2 (verbatim)

Defs (12): `MeaningAlign` (abbrev), `MeaningAlign.Functional`,
`MeaningAlign.Total`, `MeaningAlign.InjectiveAlign`,
`MeaningAlign.SurjectiveAlign`, `MeaningAlign.denotationOf`,
`SameMeaning`, `sameMeaningSetoid`,
`quotientSameMeaningEquivRange`, `graphAlign`, `actAlign`,
`unionAlign`.

Theorems (15): `MeaningAlign.denotationOf_spec`,
`MeaningAlign.align_iff_denotation`,
`MeaningAlign.functional_total_iff`,
`MeaningAlign.exists_unique_denotation`,
`MeaningAlign.denotation_injective_iff`,
`MeaningAlign.denotation_surjective_iff`,
`MeaningAlign.conflation_iff_not_functional`,
`SameMeaning.equivalence`, `graphAlign_apply`,
`graphAlign_functional_total`, `actAlign_apply`,
`unionAlign_apply`, `unionAlign_total_of_left`,
`unionAlign_functional_iff`,
`exists_functional_unionAlign_not_functional`.

---

## HONESTY LEDGER (standing, on the dossier and the module face)

This module is the SHAPE of a meaning kernel: syntax,
meanings, an alignment, and the exact conditions under which
a checkable denotation exists. It is NOT a semantics for any
natural language — no glyph in the file is a word, no element
of `M` is a meaning of anything in the world; `S`, `M` are
bare types and the alignment a bare relation. It is NOT a
unified language: the containment seed is pairwise union into
a common meaning set under an exact agreement condition, not
a container of every language. Pin N2 (meaning vs reference —
two expressions of equal denotation and different meaning)
remains OPEN and is untouched by this brick: nothing here can
distinguish two expressions beyond their aligned meanings.
Pin N1's further parts (a chosen alphabet/syntax, a
compositionality law) remain design acts in Jeff's hand, as
the primordials dossier left them. Jeff's seeing stands at T5
as filed; this module is its first formable core and nothing
more. **NO CLAIM; dials 0/4.**
