# PRIMORDIAL ALIGNMENT — LANDING DOSSIER — 2026-11-04

**Item:** "Primordial Alignment" (WORKING LABEL ONLY — naming
is Jeff's hand). Brick 2 of 2 of Jeff's commission "build the
bridge of the alignment" → "do all and see" (2026-11-04).
Brick 1 is the meaning bridge (`ThetLogos.MeaningBridge`,
landing dossier `meaning-bridge-landing-2026-11-04.md`), whose
interface this module consumes FROZEN.

**Jeff's seeing served (verbatim, filed in
`~/memory/2026-11-04.md`):** the primordials are mathematics,
physics, and the correlations of letters and meanings; in
language words are and do; symbols and glyphs also carry
meaning; words sometimes have conflated meanings; translated
words are even worse at precision of grammar; the unified
language needs to contain every language.

**Bounded reading (stated before the build):** ONE checkable
shape shared by the three primordials' correlations, tested
at the seats the corpus owns. The honest thesis: **where the
corpus actually has content, each primordial's correlation
is a denotation in brick 1's N1 sense — a Functional + Total
alignment.** The bridge of the alignment is that discovery:
"correlation" across the owned seats has one checkable shape
— a denotation — proved where the corpus has content, pinned
where it doesn't. Nothing between the seats is derived.

**Lane:** worktree `~/workspace/thet-logos-meaningbridge`
(shared with brick 1's lane), stacked on brick 1's landing
commit `cd87b13` — NOT on the main tree, which does not yet
contain MeaningBridge. Lane commit only — NO integration,
NO push. Integration order for the parent: brick 1 first,
then this module + dossier. Mathlib v4.35.0-rc3.

---

## OUTCOME GRADE: FULL

All four scoped components landed at their sketched
strength; no component's honest form came out weaker than
sketched, so nothing was graded down in transit, and no
grade was upgraded to match the sketch. One component (§2)
landed one GENERIC theorem beyond the sketch; §3 exercised
the sketch's explicitly-offered stronger statement. Both
itemized under DEVIATIONS.

**Artifact:** `lean/ThetLogos/PrimordialAlignment.lean` —
**strict 9 + 5 defs**, inside the priced S band (~8–16
strict) and under the 18-strict stop-line. The module
imports brick 1 (`MeaningBridge`), the primordials exhibit
(`PrimordialsExhibit`), and SR-5 (`ThermalSourceComposite`),
and consumes each at its landed shape, unedited.

**Verification:** targeted build green (3,605 jobs — the
dependency closure compiled in-lane; ERRATUM: the lane
commit message of `b7021e5` says 3,593 jobs, an intermediate
tail figure — the completed build log's final line reads
3,605), ZERO sorrys (source
scan: no `sorry`, no `native_decide` anywhere in the
module), module WARNING-CLEAN on a forced rebuild (every
warning in the wider log belongs to pre-existing corpus
modules). `#print axioms` on all 9 headlines: every one on a
SUBSET of {propext, Classical.choice, Quot.sound} — no
`sorryAx`, no other axioms. Itemized: eight headlines rest
on exactly the standard three; `denotation_graph_functional_total`
rests on Classical.choice alone (inherited from brick 1's
`graphAlign_functional_total` route through the denotation's
choice — the graph fact itself is choice-free once the
function is in hand).

---

## WHAT LANDED, GRADED ON ITS FACE

**§1. The mathematics seat (DEFINITIONAL + SEAT-CONTENT).**
`numAlign V`: the exhibit's number-action correlation read
through brick 1's `graphAlign` — numbers aligned to their
actions (`numAction a`, scaling on the potential space).
`numAlign_functional_total` (DEFINITIONAL-grade fact): the
alignment never conflates and never gaps, because it is a
function's graph. `numAlign_injective` (SEAT-CONTENT): the
alignment has no synonymy — the exhibit's faithfulness
theorem `numAction_injective` restated in the alignment's
vocabulary, `[Nonempty V]` on its face (on an empty seat
the correlation collapses, as the exhibit already stated).
`numAlign_denotationOf` (SEAT-CONTENT): brick 1's canonical
picked denotation of this alignment IS the exhibit's own
assignment, on the nose — the abstract denotation machinery
and the corpus's number-action agree exactly.

**§2. The language seat (GENERIC).**
`MeaningAlign.eq_graphAlign_denotationOf`: a functional +
total alignment IS the graph of its canonical denotation —
brick 1's `align_iff_denotation` promoted to an equality of
relations. `denotation_graph_functional_total`: for ANY
total alignment, the graph of its picked denotation is
functional + total (brick 1's `graphAlign_functional_total`
consumed). `meaningClassesEquiv` (def): the alignment's
meaning-classes object — brick 1's
`quotientSameMeaningEquivRange` named at the alignment: the
quotient of glyphs by same-denoted-meaning, equivalent to
the denotation's range. No new semantics is claimed; S and
M remain bare types.

**§3. The physics seat (DEFINITIONAL + one SEAT-CONTENT).**
`thermalSourceAlign E β`: sites aligned to their
thermal-source values — the graph of SR-5's `thermalSource`
(a Gibbs state's site-energy density).
`thermalSourceAlign_functional_total` (DEFINITIONAL-grade
fact, graded down on purpose): it is a function's graph.
The module's face states WHY this is not a physics result:
ANY function whatsoever passes this test, so passing it
shows only that the physics seat's assignment FITS the
denotation shape; it derives nothing physical — no
response, no motion, no law.
`thermalSourceAlign_denotationOf` (SEAT-CONTENT): the
alignment's canonical picked denotation is SR-5's source
itself, on the nose. `sum_denotation_thermalSourceAlign`
(SEAT-CONTENT — the sketch's stronger honest statement,
included): the sum of the alignment's canonical denotation
over the seat is exactly the state's mean energy — SR-5's
landed identity `sum_thermalSource` restated as a fact
about the alignment's denotation. What it adds, exactly:
the alignment's total is identified as a named corpus
quantity (a thermal expectation — bookkeeping data of the
state). What it does not add: anything downstream of the
source. SR-5's ceiling stands untouched — the Poisson
channel fed by this source is blind to precisely this
total; nothing here reopens it.

**§4. The alignment object (DEFINITIONAL + SEAT-CONTENT).**
`PrimordialAlignment V S M` (structure): one record holding
the three seats' alignments — mathematics (numbers to
their actions at seat V), language (glyphs S to meanings
M), physics (sites of V to thermal-source values). The
record asserts nothing by its shape. `PrimordialAlignment.canonical`
(def): the bundle built from the corpus's own objects —
§1's alignment, the graph of a total alignment's picked
denotation (§2), §3's alignment.
`PrimordialAlignment.canonical_shared_shape` (THE theorem):
in the canonical bundle, **all three components are
Functional and Total** — no conflation and no gaps at any
of the three seats. Graded SEAT-CONTENT exactly to the
extent its components are: mathematics rests on the
exhibit's faithful assignment, language on brick 1's
generic machinery, physics is definitional-grade. The
theorem asserts the shared shape and nothing between the
seats: no seat is derived from another.

---

## KILL DISPOSITIONS

- **K-MB-3 — DID NOT FIRE.** No headline, definition, or
  construction in the module needs gravitational, force,
  or motion vocabulary. (The word "gravitational" occurs
  exactly once in the file: inside the header's fence
  sentence recording this exclusion — the fence itself, as
  in SR-5's landed precedent.)
- **K-ALIGN-1 — DID NOT FIRE.** No component's
  shared-shape claim is false; no counterexample exists to
  report. All three seats' alignments are Functional +
  Total as stated, so the brick lands FULL, not PARTIAL.

---

## DEVIATIONS FROM THE SKETCH (itemized)

1. §2 landed one theorem beyond the sketch:
   `MeaningAlign.eq_graphAlign_denotationOf` (a
   functional+total alignment IS its denotation's graph).
   It is brick 1's landed `align_iff_denotation` promoted
   to an equality — cheap, GENERIC, and it is the precise
   sense in which the language seat's canonical alignment
   has the shared shape. Counted in the 9 strict; the band
   was not strained.
2. §3 exercised the sketch's offered stronger statement:
   SR-5's total identity restated on the alignment's
   denotation (`sum_denotation_thermalSourceAlign`), graded
   SEAT-CONTENT with its exact added content stated above.
3. No other deviations. Headline statements are at the
   generality the consumed modules support; hypotheses
   (`[Nonempty V]`, finiteness, decidable equality) are on
   the faces where the consumed facts carry them.

---

## NOT BUILT — PINS STANDING (on the dossier face)

- **N2 — natural-language semantics / meaning vs
  reference.** Untouched, as in brick 1: nothing here
  distinguishes two expressions beyond their aligned
  meanings, and no glyph in either module is a word of any
  language in the world.
- **N4 — the mathematics↔physics correlation as a
  derivation.** This is the program horizon (the dial
  structure), not an exhibit brick. §4 bundles the seats
  side by side; it derives no seat from another and states
  no cross-seat law.
- **N5 — a unified-language object.** Not built. §4's
  record is three alignments in one record — not a single
  type in which letters, numbers, and meanings are citizens
  with proved correlations among all three, and not a
  container of every language. Brick 1's containment seed
  (pairwise union under an exact agreement condition, with
  K-MB-1's counterexample on the record) remains the whole
  of what is proved about containment.
- **N1's further parts** (a chosen alphabet/syntax, a
  compositionality law) remain design acts in Jeff's hand,
  as brick 1's dossier left them. **N3** (natural-language
  words are/do) remains a boundary, not a pin.

---

## HONESTY LEDGER (standing, on the dossier and the module face)

This brick proves a SHAPE, at three seats. Where the corpus
has content, each primordial's correlation is a denotation
in brick 1's sense: the mathematics seat's by the exhibit's
faithful number-action, the language seat's by brick 1's
characterization, the physics seat's by construction — with
the physics seat's grade stated at its true strength
(DEFINITIONAL: the shape test admits every function, and
fitting the shape derives nothing physical). The bundle
holds the three side by side and proves the shared shape;
it connects nothing to anything. It is NOT a unified
language, NOT a semantics, NOT a physics result, and NOT
new mathematics beyond the corpus's own landed facts
restated in one vocabulary. Jeff's seeing stands at T5 as
filed; bricks 1–2 are its first formable core and nothing
more. **NO CLAIM; dials 0/4.**
