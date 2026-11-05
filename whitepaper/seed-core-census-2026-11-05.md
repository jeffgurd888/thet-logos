# SEED CORE — SC-3: The Census (2026-11-05)

**Status: SC-3 DELIVERABLE — the seed-core chain's final brick.**
The module is `ThetLogos/SeedCoreCensus.lean`, landed in-lane on
branch `sc2-seed-core-encoding`, commit `5f6a641` (parent: SC-2b,
`864c396`). Targeted build GREEN and warning-clean; zero sorrys;
no `native_decide`. Axiom audit: 30 headline and bridge theorems
checked, each on exactly `{propext, Classical.choice, Quot.sound}`,
no `sorryAx`. Integration into the main tree is the parent's
step, scheduled after the surface-tension seat; nothing here is
in the main-tree census yet.

**Method, in one paragraph.** Nothing in this census is a typed
list. SC-2 encoded SC-1's link column as finite data and built
Bool checks with proved bridges to the Meaning Bridge's own
predicates; SC-3 added the pointwise reflections (per prime:
is anything carrying it? per glyph: is it carrying anything?)
with bridges of the same shape, and then evaluated everything
by kernel decision over the data. Each list below is
*characterized* by a theorem — a prime is uncovered iff it is
in the gap list — so the lists are proved content, not
transcription.

**Claim ceiling (unchanged from the scoping, §5):** T5 exhibit.
The Lean content is T1 only about the finite encoded table.
Universality is NOT claimed; "contains every language" remains
a horizon statement. The seed is a candidate first finite seat
for pin N2 — **not a discharge of N2**. No dial moves; dials 0/4.

---

## 1. Headline numbers

| Reading | Covered | Gap | Functional (no conflation) | Total (no glyph gaps) | SurjectiveAlign (no unnamed meanings) | InjectiveAlign (no synonymy) |
|---|---|---|---|---|---|---|
| **Primary** (6 instrumental links) | **5 / 65** | **60** | FALSE | FALSE | FALSE | FALSE |
| **Denotative baseline** (∅ links) | **0 / 65** | **65** | TRUE *(vacuous)* | FALSE | FALSE | TRUE *(vacuous)* |
| **WATCHLIST** (primary + D6's 4 loose pairs) | **7 / 65** | **58** | FALSE | FALSE | FALSE | FALSE |

Every cell of that table is a theorem in the module (check-value
theorems by kernel decision, predicate theorems through SC-2's
bridges). The baseline's two TRUEs are vacuity, and the module
says so in words: an empty relation cannot conflate or crowd,
because it carries nothing at all.

**Covered primes, primary reading (5):** SEE, SAY, DO, MOVE,
TOUCH — via ʿayin (eye) → SEE, pē (mouth) → SAY, yōd (hand) →
DO and → TOUCH, kāp (palm) → TOUCH, ṭēt (wheel) → MOVE. All
instrumental; the denotative covered set is empty, proved
(`denotativeAlign_covered_iff`: the covered set is the empty
list).

**Witnesses, by name (primary reading):**

- **Conflation:** yōd carries two distinct primes, TOUCH and
  DO (`seedAlign_conflation_witness`). This is Jeff's
  "conflated meanings" as a finite fact: the hand is both the
  organ of touch and the canonical instrument of doing, and
  the seed has no way to make it choose.
- **Synonymy:** TOUCH is carried by two distinct glyphs, yōd
  (hand) and kāp (palm) (`seedAlign_synonymy_witness`) — the
  BODY-neighbourhood crowding the scoping predicted.
- **Glyph-side gaps:** 17 of the 22 glyphs carry nothing
  (§3 below).

## 2. The headline, read against the criterion

The Meaning Bridge's characterization
(`MeaningAlign.functional_total_iff`) says a checkable
denotation exists iff an alignment is functional and total —
no conflation, no gaps. The census's headline theorem
(`seedAlign_not_denotation`) is that criterion read against
the primary reading:

> **The seed alignment is not the graph of any denotation
> function.** There is no `f : Glyph → Prime` with
> `seedAlign s m ↔ m = f s` throughout.

The seed is a **partial, conflated, synonymous** alignment.
That is the measured content of the exhibit: a 22-glyph fossil
seed, aligned by the strictest honest link rule SC-1 could
state, reaches 5 of the 65 published meaning-primes, conflates
one of its five working glyphs, crowds one of its five primes,
and leaves 60 primes and 17 glyphs untouched. The near-zero
result is reported at full rank as a result — per the scoping,
SC-3 has no kill criterion on the numbers. What it measures is
the distance between a pictographic seed and a denotation:
that distance is now a finite, proved quantity instead of an
impression. The WATCHLIST reading (§4) shows the distance is
not an artifact of SC-1's strictness: loosening the four
hardest judgment calls buys two primes and no cleanliness.

## 3. The full gap list (primary reading — 60 of 65)

Characterized by `seedAlign_gap_iff`: a prime is carried by
no glyph iff it is on this list. Canonical NSM order;
constructor names in parentheses where the exponent needs
flattening.

I · YOU · SOMEONE · SOMETHING/THING (`SOMETHING`) · PEOPLE ·
BODY · KIND · PART · THIS · THE SAME (`THE_SAME`) ·
OTHER/ELSE (`OTHER`) · ONE · TWO · SOME · ALL · MUCH/MANY
(`MUCH_MANY`) · LITTLE/FEW (`LITTLE_FEW`) · GOOD · BAD · BIG ·
SMALL · THINK · KNOW · WANT · DON'T WANT (`DONT_WANT`) ·
FEEL · HEAR · WORDS · TRUE · HAPPEN · BE (SOMEWHERE)
(`BE_SOMEWHERE`) · THERE IS (`THERE_IS`) · BE
(SOMEONE/SOMETHING) (`BE_SOMEONE_SOMETHING`) · (IS) MINE
(`IS_MINE`) · LIVE · DIE · WHEN/TIME (`WHEN_TIME`) · NOW ·
BEFORE · AFTER · A LONG TIME (`A_LONG_TIME`) · A SHORT TIME
(`A_SHORT_TIME`) · FOR SOME TIME (`FOR_SOME_TIME`) · MOMENT ·
WHERE/PLACE (`WHERE_PLACE`) · HERE · ABOVE · BELOW · FAR ·
NEAR · SIDE · INSIDE · NOT · MAYBE · CAN · BECAUSE · IF ·
VERY · MORE · LIKE/WAY (`LIKE_WAY`).

Worth pausing on, without inflating: the gap is not random.
Everything relational, grammatical, quantificational, temporal,
and abstract gaps — the primes that make a metalanguage a
*language* rather than a picture-book. The five that land are
exactly the ones with a bodily organ or a canonical instrument:
eye, mouth, hand, palm, wheel. The seed speaks where the body
is; it is silent everywhere else. (That sentence is the
exhibit's T5 reading of its own T1 content, labeled as such.)

**Glyph-side gap list (primary reading — 17 of 22),**
characterized by `seedAlign_glyph_gap_iff`, codepoint order:
ʾālep (ox) · bēt (house) · gīmel (throwstick) · dālet (door) ·
hē (window) · wāw (hook) · zayin (weapon) · ḥēt (fence) ·
lāmd (goad) · mēm (water) · nūn (fish) · sāmek (support) ·
ṣādē (papyrus plant) · qōp (monkey) · rēš (head) · šīn
(tooth) · tāw (mark). The five glyphs NOT on this list are
the only carriers: ṭēt, yōd, kāp, ʿayin, pē.

## 4. The WATCHLIST reading (labeled, throughout)

SC-1's dossier (departure D6) recorded four links judged too
loose under the link rule and **not drawn**: weapon → DIE
(zayin), window → SEE (hē), goad → MOVE (lāmd), water →
SOMETHING/THING (mēm). SC-3 evaluates the alignment those
four pairs would make, as a sensitivity bound on SC-1's
judgment — the pairs are transcribed from the dossier text,
and nothing else is added.

- **Coverage: 7 of 65** — the primary five plus DIE and
  SOMETHING, exactly (`watchlistAlign_covered_iff`). The four
  loose calls were worth precisely two primes.
- **Gap: 58 of 65** (`watchlistAlign_gap_iff` — the full list
  is the primary gap list minus DIE and SOMETHING).
- **Glyph-side gaps: 13 of 22** (`watchlistAlign_glyph_gap_iff`).
- **All four predicates still fail.** Conflation unchanged:
  yōd → TOUCH, DO (`watchlistAlign_conflation_witness`).
  Totality and surjectivity still fail on the lists above.
  And synonymy gets **worse**: besides TOUCH (yōd, kāp), the
  watchlist crowds SEE — ʿayin (eye) and hē (window)
  (`watchlistAlign_synonymy_see`) — and MOVE — ṭēt (wheel)
  and lāmd (goad) (`watchlistAlign_synonymy_move`).
- **Headline survives:** `watchlistAlign_not_denotation` —
  even the loosened seed is not the graph of a denotation.

## 5. The prime-set correction (SC-2b) — the denominator

Every "of 65" in this dossier is the **canonical** 65 of
Goddard & Wierzbicka (2014), including the possession prime
**(IS) MINE**. As first scoped, the enumeration named only
62: its single entry EXIST had collapsed the canonical
four-prime cluster — BE (SOMEWHERE), THERE IS, BE
(SOMEONE/SOMETHING), (IS) MINE — into one slot. SC-2b caught
the collapse against the canonical table (Goddard &
Wierzbicka 2014, as reproduced in *Conversatoria Linguistica*
XVI (2024), Table 1; stabilisation at 65 confirmed in
Wierzbicka, *Russian Journal of Linguistics* 25(2), 2021) and
corrected the scoping, the SC-1 dossier, and the encoding in
one brick. No SC-1 link touched the cluster, so no count in
this census moved when the denominator was repaired — but
three of the repaired primes (BE (SOMEWHERE), BE
(SOMEONE/SOMETHING), (IS) MINE) and THERE IS itself stand in
the gap list above, where a 62-denominator census would have
silently never asked about them.

## 6. What stands, and what does not

**Stands (T1, about the finite encoded table):** the three
readings' predicate values, with witnesses; the covered and
gap lists on both sides, characterized; the not-a-denotation
headline for the primary and watchlist readings; the
exact price of SC-1's four loosest judgment calls (+2
coverage, +2 synonymy crowdings, no predicate repaired).

**Does not stand, and is not claimed:** any discharge of pin
N2 (the seed is a candidate first finite seat for meaning,
measured — the pin asks for a distinguishing theorem about
meaning, and a census of one seed is not it); any advance on
N4 (SC-1's correlate column was never encoded, by design);
anything about N5 or about all languages (the prime set's own
universality is the NSM program's claim, cited as theirs);
any dial movement. The chain SC-1 → SC-2 → SC-3 is complete:
the table, the encoding, and the census are all landed in the
lane. What the exhibit finally says is small and exact — a
fossil alphabet, honestly aligned, says five things, says one
of them twice, says one of them ambiguously, and is silent
about the other sixty — and that sentence is now backed by
machine-checked finite mathematics rather than by intuition
about old letters.

*SC-3 delivered 2026-11-05. Grounding: scoping note §§3–5;
SC-1 dossier (links, flags, departure D6); SC-2 encoding
(checks, bridges, decidability instances); MeaningBridge
(`functional_total_iff`). Module: `SeedCoreCensus.lean`,
45 theorems + 10 definitions, lane commit `5f6a641`. NO
CLAIM; dials 0/4.*
